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

/-- The binary code of `2 ^ k - 1` is `k` ones. -/
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

/-- `rep [true, true] k ++ [false]` self-delimits `k` ones. -/
theorem delimit_replicate (k : ℕ) :
    BitstringEncoding.delimit (List.replicate k true) =
      TM2Program.rep [true, true] k ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, BitstringEncoding.delimit, ih, TM2Program.rep_succ]
      rfl

/-- The binary literal code of `(2 ^ k - 1, b)`. -/
theorem encodeLit_two_pow (k : ℕ) (b : Bool) :
    Cslib.CookLevin.encodeLit (2 ^ k - 1, b) = TM2Program.rep [true, true] k ++ [false, b] := by
  simp [Cslib.CookLevin.encodeLit, Cslib.CookLevin.encodeNatPrefix, encodeNat_two_pow_sub_one,
    delimit_replicate]

/-! ### The translated formula -/

/-- Slot `j` of `c` becomes the literal on variable `2 ^ (k₀ + #slots after j) - 1`. -/
def binClause (k₀ : ℕ) : Clause → Cslib.CookLevin.CNFClause
  | [] => []
  | none :: c => binClause k₀ c
  | some b :: c => (2 ^ (k₀ + c.length) - 1, b) :: binClause k₀ c

/-- The translated formula. -/
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

/-- **Satisfiability is preserved** for formulas whose clauses all have length `V`. -/
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

/-- Close a clause with `n` literals: its unary count, emitted in front of the literals. -/
def endClause (n : ℕ) (o : List Bool) : List Bool := List.replicate n true ++ false :: o

/-- The translation, reading the dense bit string **backwards** two bits at a time (`s₂` before
`s₁` for a slot `s₁ s₂`) and prepending to the output `o`. `ins` says whether a clause is open
(the reversed string starts with a terminator), `n` counts its literals, `k` its slots so far, and
`m` the clauses. A terminator `00` closes the open clause and opens the next; an absent slot `01`
bumps `k`; a present slot `1s` emits the literal `(2 ^ k - 1, !s)` inside a clause and is skipped
outside one; at the end the clause count is emitted. -/
def conv : List Bool → Bool → ℕ → ℕ → ℕ → List Bool → List Bool
  | false :: false :: r, ins, n, _, m, o =>
      conv r true 0 0 (m + 1) (if ins then endClause n o else o)
  | true :: false :: r, ins, n, k, m, o => conv r ins n (k + 1) m o
  | s :: true :: r, ins, n, k, m, o =>
      if ins then conv r true (n + 1) (k + 1) m (TM2Program.rep [true,
          true] k ++ false :: (!s) :: o)
      else conv r false n k m o
  | _, ins, n, _, m, o => List.replicate m true ++ false :: (if ins then endClause n o else o)

/-- The slots of a clause, read backwards from slot count `k`. -/
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

/-- One whole clause (terminator first), from any state. -/
theorem conv_clause (c : Clause) (r : List Bool) (ins : Bool) (n k m : ℕ) (o : List Bool) :
    conv ((encodeClause c).reverse ++ r) ins n k m o =
      conv r true (binClause 0 c).length c.length (m + 1)
        ((binClause 0 c).flatMap Cslib.CookLevin.encodeLit ++
          (if ins then endClause n o else o)) := by
  rw [encodeClause, List.reverse_append, List.append_assoc]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, conv]
  rw [conv_slots]
  simp

/-- The remaining clauses (in reverse order), with clause `c₀` open. -/
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

/-- **The translation computes the binary encoding** of `binCNF φ` from the dense encoding. -/
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

/-- Input that does not parse as a CNF formula is not in SAT. -/
theorem satDec_of_decodeCNF_eq_none {x : List Bool} (h : Cslib.CookLevin.decodeCNF x = none) :
    Cslib.CookLevin.satDec x = false := by
  unfold Cslib.CookLevin.satDec
  rw [ite_eq_right]
  rintro ⟨φ, rfl, -⟩
  simp at h

end Cslib.Complexity.DenseSAT.ToBinary
