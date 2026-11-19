/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.Encoding
public import Mathlib.Data.Nat.Log
public import MathlibExt.Computability.TuringMachine.Program
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.DenseSAT

/-!
# From the dense SAT encoding to the binary-index encoding

`Cslib.CookLevin.satDec` (the language of the `theorem_wanted` Cook-Levin statement) encodes a
literal as the self-delimited binary code of its variable index followed by its polarity, with
unary clause and literal counts. The dense encoding of `Cslib.Complexity.DenseSAT` writes two bits
per variable slot. This file translates the second into the first.

The translation names slot `j` of a clause of length `L` by the variable `2 ^ (L - 1 - j) - 1`,
whose binary code is `L - 1 - j` ones (`encodeNat_two_pow_sub_one`), so a machine can emit it with
a unary counter. For formulas whose clauses all have the same length (as the Cook-Levin formula
does), this is a consistent renaming of variables, so satisfiability is preserved
(`cnfSat_binCNF_iff`).

* `binClause`, `binCNF`: the translated formula; `mem_binClause`.
* `conv`: the translation as a function on the *reversed* dense bit string, in the form a stack
  machine computes it; `conv_encodeCNF`: on a dense encoding it produces
  `Cslib.CookLevin.encodeCNF (binCNF φ)`.
* `satDec_encodeCNF`: `satDec` on an encoding is satisfiability.
-/

@[expose] public section

namespace Cslib.Complexity.DenseSAT.ToBinary

open Computability MetaMathlibExt

/-! ### Binary codes of `2 ^ k - 1` -/

/-- **The binary code of $2^k - 1$.** For every natural number $k$, the binary code of
$2^k - 1$ (Mathlib's encoding of natural numbers as bit lists, least significant bit first) is
the list of $k$ ones. -/
theorem encodeNat_two_pow_sub_one (k : ℕ) : encodeNat (2 ^ k - 1) = List.replicate k true := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
        have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega
      rw [h, List.replicate_succ, ← ih]
      unfold encodeNat
      rcases Nat.eq_zero_or_pos (2 ^ k - 1) with h0 | hp
      · rw [h0]; rfl
      · obtain ⟨m, hm⟩ : ∃ p : PosNum, ((2 ^ k - 1 : ℕ) : Num) = Num.pos p := by
          cases e : ((2 ^ k - 1 : ℕ) : Num) with
          | zero => exfalso; have := congrArg (fun n : Num => (n : ℕ)) e; simp at this; omega
          | pos p => exact ⟨p, rfl⟩
        have hm' : ((m : ℕ)) = 2 ^ k - 1 := by
          have := congrArg (fun n : Num => (n : ℕ)) hm
          simp only [Num.to_of_nat, Num.cast_pos] at this
          exact this.symm
        have : ((2 * (2 ^ k - 1) + 1 : ℕ) : Num) = Num.pos (PosNum.bit1 m) := by
          apply Num.to_nat_inj.1
          rw [Num.to_of_nat, Num.cast_pos, PosNum.cast_bit1, hm']
          omega
        rw [this, hm]; rfl

/-- **Self-delimiting code of a block of ones.** For every $k \in \mathbb{N}$, the self-delimiting
form of the bit string of $k$ ones is $k$ copies of $11$ followed by a single $0$. -/
theorem delimit_replicate (k : ℕ) :
    BitstringEncoding.delimit (List.replicate k true) =
      TM2Program.rep [true, true] k ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, BitstringEncoding.delimit, ih, TM2Program.rep_succ]
      rfl

/-- **Binary codes of literals on variables one less than a power of two.** For every
$k \in \mathbb{N}$ and every truth value $b$, the binary code of the literal of polarity $b$ on
variable $2^k - 1$ is $k$ copies of $11$, followed by $0$, followed by the bit $b$. -/
theorem encodeLit_two_pow (k : ℕ) (b : Bool) :
    Cslib.CookLevin.encodeLit (2 ^ k - 1, b) = TM2Program.rep [true, true] k ++ [false, b] := by
  simp [Cslib.CookLevin.encodeLit, Cslib.CookLevin.encodeNatPrefix, encodeNat_two_pow_sub_one,
    delimit_replicate]

/-! ### The translated formula -/

/-- **Binary-index translation of a dense clause.** Let $k_0 \in \mathbb{N}$ and let $c$ be a dense
clause with slots $s_0, \dots, s_{L-1}$. Its binary-index translation with offset $k_0$ is the
clause that has, for each slot $j$ holding a literal of polarity $b$, the literal of polarity $b$
on variable $2^{k_0 + L - 1 - j} - 1$, listed in increasing order of $j$; absent slots contribute
no literal. -/
def binClause (k₀ : ℕ) : Clause → Cslib.CookLevin.CNFClause
  | [] => []
  | none :: c => binClause k₀ c
  | some b :: c => (2 ^ (k₀ + c.length) - 1, b) :: binClause k₀ c

/-- **Binary-index translation of a dense formula.** The translation of a dense CNF formula
$\varphi$ replaces each clause $c$ of $\varphi$, keeping their order, by its binary-index
translation with offset $0$: if $c$ has length $L$, each slot $j$ of $c$ holding a literal of
polarity $b$ becomes the literal of polarity $b$ on variable $2^{L - 1 - j} - 1$, and absent slots
are dropped. -/
def binCNF (φ : CNF) : Cslib.CookLevin.CNF := φ.map (binClause 0)

theorem mem_binClause (c : Clause) (x : ℕ) (b : Bool) :
    (x, b) ∈ binClause 0 c ↔ ∃ j, c[j]? = some (some b) ∧ x = 2 ^ (c.length - 1 - j) - 1 := by
  induction c with
  | nil => simp [binClause]
  | cons s c ih =>
      have shift : ∀ j, 2 ^ (c.length - 1 - j) - 1 = 2 ^ ((s :: c).length - 1 - (j + 1)) - 1 := by
        intro j; simp only [List.length_cons]; congr 2; omega
      constructor
      · intro h
        cases s with
        | none =>
            obtain ⟨j, hj, hx⟩ := ih.1 h
            exact ⟨j + 1, by simpa using hj, by rw [hx, shift]⟩
        | some b' =>
            simp only [binClause, List.mem_cons, Prod.mk.injEq] at h
            rcases h with ⟨hx, hb⟩ | h
            · exact ⟨0, by simp [hb], by simp [hx]⟩
            · obtain ⟨j, hj, hx⟩ := ih.1 h
              exact ⟨j + 1, by simpa using hj, by rw [hx, shift]⟩
      · rintro ⟨j, hj, hx⟩
        cases j with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
            subst hj
            simp only [binClause, List.mem_cons, Prod.mk.injEq, and_true]
            left; simp [hx]
        | succ j =>
            simp only [List.getElem?_cons_succ] at hj
            have h := ih.2 ⟨j, hj, by rw [hx, shift]⟩
            cases s with
            | none => exact h
            | some b' => exact List.mem_cons_of_mem _ h

/-- **The binary-index translation preserves satisfiability when all clauses have equal length.**
Let $\varphi$ be a dense CNF formula all of whose clauses have the same length $V$. Then the
binary-index translation of $\varphi$ is satisfiable (some assignment of truth values to the
variables satisfies every clause) if and only if some finite list of truth values satisfies
$\varphi$. -/
theorem cnfSat_binCNF_iff {φ : CNF} {V : ℕ} (hV : ∀ c ∈ φ, c.length = V) :
    Cslib.CookLevin.CNFSat (binCNF φ) ↔ ∃ a, cnfSat φ a := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(List.range V).map fun j => σ (2 ^ (V - 1 - j) - 1), fun c hc => ?_⟩
    obtain ⟨x, b, hxb, hσx⟩ := hσ _ (List.mem_map.2 ⟨c, hc, rfl⟩)
    obtain ⟨j, hj, hx⟩ := (mem_binClause c x b).1 hxb
    have hjl : j < c.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
    refine ⟨j, b, hj, ?_⟩
    rw [hV c hc] at hx hjl
    simp [List.getElem?_range hjl, ← hx, hσx]
  · rintro ⟨a, ha⟩
    refine ⟨fun x => a.getD (V - 1 - Nat.log 2 (x + 1)) false, fun C hC => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hC
    obtain ⟨j, b, hj, haj⟩ := ha c hc
    have hjl : j < c.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
    refine ⟨2 ^ (c.length - 1 - j) - 1, b, (mem_binClause c _ b).2 ⟨j, hj, rfl⟩, ?_⟩
    rw [hV c hc] at hjl ⊢
    have h1 : 2 ^ (V - 1 - j) - 1 + 1 = 2 ^ (V - 1 - j) := Nat.sub_add_cancel Nat.one_le_two_pow
    simp only [h1, Nat.log_pow Nat.one_lt_two]
    rw [show V - 1 - (V - 1 - j) = j by omega, List.getD_eq_getElem?_getD, haj]
    rfl


/-! ### The translation on the reversed bit string -/

/-- **Closing a clause in the translated output.** For a natural number $n$ and a bit string
$o$, closing a clause with $n$ literals in front of $o$ gives the bit string consisting of $n$
ones, then a zero, then $o$; that is, the unary count of $n$ is prepended to $o$.

In the translation, $o$ starts with the codes of the clause's $n$ literals, already emitted. -/
def endClause (n : ℕ) (o : List Bool) : List Bool := List.replicate n true ++ false :: o

/-- **The dense-to-binary translation on the reversed bit string.** The function
$\mathrm{conv}(w, \iota, n, k, m, o)$ consumes the bit string $w$ two bits at a time and prepends
to the output bit string $o$. The truth value $\iota$ records whether a clause is open, $n$ counts
the literals of the open clause, $k$ counts slots and $m$ counts clauses. Juxtaposition of bit
strings is concatenation, $1^n$ is $n$ ones, $(11)^k$ is $k$ copies of $11$, $\bar s$ is the
negation of a bit $s$, and $C$ is $1^n 0\, o$ if $\iota$ is true and $o$ otherwise. For every bit
$s$ and bit string $r$:

* $\mathrm{conv}(00\, r, \iota, n, k, m, o) = \mathrm{conv}(r, \mathrm{true}, 0, 0, m + 1, C)$;
* $\mathrm{conv}(10\, r, \iota, n, k, m, o) = \mathrm{conv}(r, \iota, n, k + 1, m, o)$;
* $\mathrm{conv}(s1\, r, \iota, n, k, m, o)$ is
  $\mathrm{conv}(r, \mathrm{true}, n + 1, k + 1, m, (11)^k 0 \bar s\, o)$ if $\iota$ is true and
  $\mathrm{conv}(r, \mathrm{false}, n, k, m, o)$ otherwise;
* if $w$ has fewer than two bits, $\mathrm{conv}(w, \iota, n, k, m, o) = 1^m 0\, C$.

On the reversed dense encoding a slot $s_1 s_2$ is read as $s_2 s_1$: $00$ is a terminator, which
closes the open clause and opens the next, $10$ is an absent slot, and $s1$ is a present slot,
whose literal $(2^k - 1, \bar s)$ is emitted (its binary code is $(11)^k 0 \bar s$) inside a
clause and skipped outside one. At the end the open clause is closed and the unary clause count
is emitted. -/
def conv : List Bool → Bool → ℕ → ℕ → ℕ → List Bool → List Bool
  | false :: false :: r, ins, n, _, m, o =>
      conv r true 0 0 (m + 1) (if ins then endClause n o else o)
  | true :: false :: r, ins, n, k, m, o => conv r ins n (k + 1) m o
  | s :: true :: r, ins, n, k, m, o =>
      if ins then conv r true (n + 1) (k + 1) m (TM2Program.rep [true,
          true] k ++ false :: (!s) :: o)
      else conv r false n k m o
  | _, ins, n, _, m, o => List.replicate m true ++ false :: (if ins then endClause n o else o)

/-- **The translation on the slots of a clause.** Write $\mathrm{conv}(w, \iota, n, k, m, o)$ for
the reversed-string translation run on the bit string $w$ with open-clause flag $\iota$, literal
count $n$, slot count $k$, clause count $m$ and output $o$; juxtaposition of bit strings is
concatenation, $w^R$ is the reversal of $w$ and $|x|$ is the length of a list $x$. Let $c$ be a
dense clause, $r$ and $o$ bit strings and $n, k, m \in \mathbb{N}$. Let $s(c)$ be the
concatenation of the two-bit codes of the slots of $c$, let $c'$ be the binary-index translation
of $c$ with offset $k$, and let $e$ be the concatenation of the binary codes of the literals of
$c'$. Then
$\mathrm{conv}(s(c)^R r, \mathrm{true}, n, k, m, o) =
\mathrm{conv}(r, \mathrm{true}, n + |c'|, k + |c|, m, e\, o)$. -/
theorem conv_slots (c : Clause) (r : List Bool) (n k m : ℕ) (o : List Bool) :
    conv ((c.flatMap encodeSlot).reverse ++ r) true n k m o =
      conv r true (n + (binClause k c).length) (k + c.length) m
        ((binClause k c).flatMap Cslib.CookLevin.encodeLit ++ o) := by
  induction c generalizing r with
  | nil => simp [binClause]
  | cons x c ih =>
      rw [List.flatMap_cons, List.reverse_append, List.append_assoc, ih]
      cases x with
      | none =>
          simp only [encodeSlot, List.reverse_cons, List.reverse_nil, List.nil_append,
            List.cons_append, conv, binClause, List.length_cons]
          rw [Nat.add_assoc]
      | some b =>
          simp only [encodeSlot, List.reverse_cons, List.reverse_nil, List.nil_append,
            List.cons_append, conv, binClause, ite_true, List.length_cons,
            List.flatMap_cons, encodeLit_two_pow, List.append_assoc, Bool.not_not, Nat.add_assoc]

/-- **The translation on a whole clause.** Write $\mathrm{conv}(w, \iota, n, k, m, o)$ for the
reversed-string translation run on the bit string $w$ with open-clause flag $\iota$, literal count
$n$, slot count $k$, clause count $m$ and output $o$; juxtaposition of bit strings is
concatenation, $w^R$ is the reversal of $w$, $1^n$ is $n$ ones and $|x|$ is the length of a list
$x$. Let $c$ be a dense clause, $r$ and $o$ bit strings, $\iota$ a truth value and
$n, k, m \in \mathbb{N}$. Let $E(c)$ be the dense encoding of $c$ (its slot codes followed by the
terminator $00$), $c'$ the binary-index translation of $c$ with offset $0$, and $e$ the
concatenation of the binary codes of the literals of $c'$. Put $o' = 1^n 0\, o$ if $\iota$ is true
and $o' = o$ otherwise. Then
$\mathrm{conv}(E(c)^R r, \iota, n, k, m, o) =
\mathrm{conv}(r, \mathrm{true}, |c'|, |c|, m + 1, e\, o')$. -/
theorem conv_clause (c : Clause) (r : List Bool) (ins : Bool) (n k m : ℕ) (o : List Bool) :
    conv ((encodeClause c).reverse ++ r) ins n k m o =
      conv r true (binClause 0 c).length c.length (m + 1)
        ((binClause 0 c).flatMap Cslib.CookLevin.encodeLit ++
          (if ins then endClause n o else o)) := by
  rw [encodeClause, List.reverse_append, List.append_assoc]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, conv]
  rw [conv_slots]
  simp

/-- **The translation on the remaining clauses.** Write $\mathrm{conv}(w, \iota, n, k, m, o)$ for
the reversed-string translation run on the bit string $w$ with open-clause flag $\iota$, literal
count $n$, slot count $k$, clause count $m$ and output $o$; juxtaposition of bit strings is
concatenation, $w^R$ is the reversal of $w$, $1^n$ is $n$ ones and $|x|$ is the length of a list
$x$. For a dense clause $c$, let $E(c)$ be its dense encoding, $c'$ its binary-index translation
with offset $0$, $e(c)$ the concatenation of the binary codes of the literals of $c'$, and $B(c)$
the binary code of the clause $c'$. Let $p, k, m \in \mathbb{N}$, let $c_0, c_1, \dots, c_p$ be
dense clauses and let $D$ be a bit string. Then
$\mathrm{conv}(E(c_1)^R \cdots E(c_p)^R, \mathrm{true}, |c_0'|, k, m, e(c_0)\, D) =
1^{m + p} 0\, B(c_p) \cdots B(c_1) B(c_0) D$. -/
theorem conv_clauses (ψ : List Clause) (c₀ : Clause) (k m : ℕ) (D : List Bool) :
    conv (ψ.flatMap fun c => (encodeClause c).reverse) true (binClause 0 c₀).length k m
        ((binClause 0 c₀).flatMap Cslib.CookLevin.encodeLit ++ D) =
      List.replicate (m + ψ.length) true ++ false ::
        ((ψ.reverse.flatMap fun c => Cslib.CookLevin.encodeClause (binClause 0 c)) ++
          Cslib.CookLevin.encodeClause (binClause 0 c₀) ++ D) := by
  induction ψ generalizing c₀ k m D with
  | nil =>
      simp [conv, endClause, Cslib.CookLevin.encodeClause]
  | cons c ψ ih =>
      rw [List.flatMap_cons, conv_clause]
      simp only [↓reduceIte]
      have e : endClause (binClause 0 c₀).length
          ((binClause 0 c₀).flatMap Cslib.CookLevin.encodeLit ++ D) =
          Cslib.CookLevin.encodeClause (binClause 0 c₀) ++ D := by
        simp [endClause, Cslib.CookLevin.encodeClause]
      rw [e, ih]
      simp only [List.length_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc]
      congr 2
      omega

/-- **The translation computes the binary encoding.** Let $\varphi$ be a dense CNF formula. Run the
reversed-string translation on the reversal of the dense encoding of $\varphi$, starting with no
clause open, literal count $0$, slot count $0$, clause count $0$ and empty output. The result is
the binary encoding of the binary-index translation of $\varphi$. -/
theorem conv_encodeCNF (φ : CNF) :
    conv (encodeCNF φ).reverse false 0 0 0 [] = Cslib.CookLevin.encodeCNF (binCNF φ) := by
  rw [encodeCNF, List.reverse_flatMap]
  simp only [Function.comp_def]
  rcases h : φ.reverse with _ | ⟨c, ψ⟩
  · rw [List.reverse_eq_nil_iff] at h
    subst h
    simp [conv, Cslib.CookLevin.encodeCNF, binCNF]
  · have hφ : φ = ψ.reverse ++ [c] := by
      rw [← List.reverse_reverse φ, h, List.reverse_cons]
    rw [List.flatMap_cons, conv_clause]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have := conv_clauses ψ c c.length 1 []
    simp only [List.append_nil] at this ⊢
    rw [this, hφ]
    simp only [Cslib.CookLevin.encodeCNF, binCNF, List.map_append, List.map_cons, List.map_nil,
      List.length_append, List.length_map, List.length_reverse, List.length_cons,
      List.length_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.flatMap_map]
    congr 2
    omega

/-! ### `satDec` on an encoding -/

/-- **SAT accepts the code of a formula exactly when it is satisfiable.** For every CNF formula
$\psi$, the SAT decision problem returns true on the length-prefixed binary code of $\psi$ if and
only if $\psi$ is satisfiable. -/
theorem satDec_encodeCNF (ψ : Cslib.CookLevin.CNF) :
    Cslib.CookLevin.satDec (Cslib.CookLevin.encodeCNF ψ) = true ↔
      Cslib.CookLevin.CNFSat ψ := by
  classical
  unfold Cslib.CookLevin.satDec
  constructor
  · intro h
    by_cases hm : Cslib.CookLevin.encodeCNF ψ ∈ Cslib.CookLevin.SATLang
    · obtain ⟨φ, he, hs⟩ := hm
      rwa [Cslib.CookLevin.encodeCNF_injective he] at hs
    · simp [hm] at h
  · intro h
    have hm : Cslib.CookLevin.encodeCNF ψ ∈ Cslib.CookLevin.SATLang := ⟨ψ, rfl, h⟩
    simp [hm]

/-- **Unparsable input is not in SAT.** If the decoder for binary-encoded CNF formulas fails on
a bit string $x$, then the SAT decision problem rejects $x$. -/
theorem satDec_of_decodeCNF_eq_none {x : List Bool} (h : Cslib.CookLevin.decodeCNF x = none) :
    Cslib.CookLevin.satDec x = false := by
  unfold Cslib.CookLevin.satDec
  rw [ite_eq_right]
  rintro ⟨φ, rfl, -⟩
  simp at h

end Cslib.Complexity.DenseSAT.ToBinary
