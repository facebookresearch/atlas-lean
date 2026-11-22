/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rice's theorem in Sipser's form, A_TM ≤ HALT_TM, and regular halting sets
-/
module

public import CSLibExt.Computability.Decidability.Undecidable
public import Mathlib.Computability.DFA
public import Mathlib.Tactic.Linarith

/-!
# Rice's theorem in Sipser's form, A_TM ≤ HALT_TM, and regular halting sets

Programs are partial recursive codes (`Nat.Partrec.Code`), equivalent to `FinTM2` machines, and
decision is by `FinTM2` (`TM2Decidable`).

**Conventions.** The *language* of a code is its domain, the set of inputs it halts on, as for
recognizers (`TM2Recognizable`) and for `EmptyCode`/`EqCode` in `RiceApplications.lean`;
`RegularDomainCode` uses it. `Accepts` instead models Sipser's accept/reject distinction, where a
machine may halt without accepting: a code accepts `n` when it halts on `n` with output `0`.

* **Rice's theorem** (Sipser, Problem 5.28): a property of the computed partial function that
  holds for some partial recursive function and fails for another is undecidable
  (`not_tm2Decidable_of_nontrivial`). The language form (`not_tm2Decidable_language`) is about
  the domain of a code, the set of inputs it halts on.
* **Acceptance and halting** (Sipser, Theorems 4.11 and 5.1): a code *accepts* `n` when it halts
  on `n` with output `0` (`Accepts`). Acceptance and halting (`Halts`) reduce to each other
  (`manyOneReducible_accepts_halts`, `manyOneReducible_halts_accepts`), and both are undecidable.
* **Regular halting sets**: `RegularDomainCode c` says the halting set of `c`, read as a unary
  language, is regular. This is a domain analogue of Sipser's `REGULAR_TM`, not `REGULAR_TM`
  itself, whose language is the set of accepted words. The proof follows Sipser's for
  Theorem 5.3. Halting reduces to it (`manyOneReducible_halts_regularDomain`): on `(c, n)`,
  build a code halting on every square, and on every input if `c` halts on `n`. Its domain is
  then all of `ℕ` (regular) or the squares, which are not regular by the pumping lemma
  (`not_isRegular_unaryLang_squares`). So regularity of halting sets is undecidable.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §4.2 and §5.1.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability Encodable
open Nat.Partrec (Code)

/-! ### Rice's theorem -/

/-- **Rice's theorem for partial recursive codes.** Let $C$ be a set of partial functions
$\mathbb{N} \rightharpoonup \mathbb{N}$, and suppose there are partial recursive functions
$f \in C$ and $g \notin C$. Then the property of a partial recursive code $c$ that the partial
function computed by $c$ belongs to $C$ is not decidable by a multi-stack Turing machine. -/
theorem not_tm2Decidable_of_nontrivial (C : Set (ℕ →. ℕ)) {f g : ℕ →. ℕ} (hf : Nat.Partrec f)
    (hg : Nat.Partrec g) (hfC : f ∈ C) (hgC : g ∉ C) :
    ¬TM2Decidable fun c : Code ↦ c.eval ∈ C :=
  fun h ↦ hgC (rice_tm2 C h hf hg hfC)

/-- **Rice's theorem for languages.** Let $P$ be a set of subsets of $\mathbb{N}$, and suppose
there are partial recursive codes $c_1$ and $c_2$ such that the domain of $c_1$ (the set of
inputs on which it halts) belongs to $P$ and the domain of $c_2$ does not. Then the property of a
partial recursive code $c$ that the domain of $c$ belongs to $P$ is not decidable by a
multi-stack Turing machine. -/
theorem not_tm2Decidable_language (P : Set (Set ℕ)) {c₁ c₂ : Code} (h₁ : c₁.eval.Dom ∈ P)
    (h₂ : c₂.eval.Dom ∉ P) : ¬TM2Decidable fun c : Code ↦ c.eval.Dom ∈ P :=
  not_tm2Decidable_of_nontrivial {f | f.Dom ∈ P} (Code.exists_code.2 ⟨c₁, rfl⟩)
    (Code.exists_code.2 ⟨c₂, rfl⟩) h₁ h₂

/-! ### Acceptance and halting -/

/-- **Acceptance by a code.** A partial recursive code $c$ accepts a natural number $n$ when $c$
halts on input $n$ with output $0$. Acceptance is a predicate on pairs $(c, n)$; it is the analogue
of Sipser's $A_{\mathrm{TM}}$, where a machine may halt without accepting. -/
def Accepts (p : Code × ℕ) : Prop := 0 ∈ p.1.eval p.2

/-- **Halting of a code on an input.** A partial recursive code $c$ halts on a natural number $n$
when its evaluation at $n$ is defined. Halting is a predicate on pairs $(c, n)$; it is the analogue
of Sipser's $\mathrm{HALT}_{\mathrm{TM}}$. -/
def Halts (p : Code × ℕ) : Prop := (p.1.eval p.2).Dom

theorem eval_comp (c₁ c₂ : Code) (n : ℕ) :
    (Code.comp c₁ c₂).eval n = (c₂.eval n).bind c₁.eval := rfl

/-- **A code that halts only on zero.** There is a partial recursive code $z$ that on input $0$
halts with output $0$ and on every input $x \ne 0$ does not halt. -/
theorem exists_code_zero_or_loop :
    ∃ z : Code, z.eval = fun x ↦ if x = 0 then Part.some 0 else Part.none := by
  refine Code.exists_code.1 (Partrec.nat_iff.1 ?_)
  have : Partrec fun x : ℕ ↦ cond (decide (x = 0)) (Part.some 0) Part.none :=
    Partrec.cond (Primrec.eq.comp Primrec.id (Primrec.const 0)).decide.to_comp
      (Partrec.const' _) Partrec.none
  exact this.of_eq fun x ↦ by by_cases hx : x = 0 <;> simp [hx]

/-- **Acceptance reduces to halting.** Say a partial recursive code $c$ accepts a natural number
$n$ when $c$ halts on input $n$ with output $0$. Acceptance many-one reduces to halting: there is
a computable map $f$ from pairs $(c, n)$ of a partial recursive code and a natural number to such
pairs, such that for every pair $(c, n)$, the code $c$ accepts $n$ if and only if, writing
$f(c, n) = (c', n')$, the code $c'$ halts on $n'$.

The reduction runs the code, then loops unless the output is $0$. -/
theorem manyOneReducible_accepts_halts : ManyOneReducible Accepts Halts := by
  obtain ⟨z, hz⟩ := exists_code_zero_or_loop
  refine ⟨fun p ↦ (Code.comp z p.1, p.2), ?_, fun p ↦ ?_⟩
  · exact (Primrec.pair (Code.primrec₂_comp.comp (Primrec.const z) Primrec.fst)
      Primrec.snd).to_comp
  · simp only [Accepts, Halts, eval_comp, hz, Part.bind_dom]
    constructor
    · intro h
      exact ⟨Part.dom_iff_mem.mpr ⟨0, h⟩, by rw [Part.get_eq_of_mem h]; simp⟩
    · rintro ⟨hd, hz0⟩
      have h0 : (p.1.eval p.2).get hd = 0 := by
        by_contra hne
        simp [hne] at hz0
      exact h0 ▸ Part.get_mem hd

/-- **Halting reduces to acceptance.** Say a partial recursive code $c$ accepts a natural number
$n$ when $c$ halts on input $n$ with output $0$. Halting many-one reduces to acceptance: there is
a computable map $f$ from pairs $(c, n)$ of a partial recursive code and a natural number to such
pairs, such that for every pair $(c, n)$, the code $c$ halts on $n$ if and only if, writing
$f(c, n) = (c', n')$, the code $c'$ accepts $n'$.

The reduction runs the code, then outputs $0$. -/
theorem manyOneReducible_halts_accepts : ManyOneReducible Halts Accepts := by
  refine ⟨fun p ↦ (Code.comp (Code.const 0) p.1, p.2), ?_, fun p ↦ ?_⟩
  · exact (Primrec.pair (Code.primrec₂_comp.comp (Primrec.const _) Primrec.fst)
      Primrec.snd).to_comp
  · simp only [Accepts, Halts, eval_comp]
    constructor
    · intro h
      exact Part.mem_bind_iff.mpr ⟨_, Part.get_mem h, Part.mem_some 0⟩
    · intro h
      obtain ⟨x, hx, -⟩ := Part.mem_bind_iff.mp h
      exact Part.dom_iff_mem.mpr ⟨x, hx⟩

/-- **Halting is undecidable.** No multi-stack Turing machine decides, for pairs $(c, n)$ of a
partial recursive code and a natural number, whether $c$ halts on $n$. -/
theorem not_tm2Decidable_halts : ¬TM2Decidable Halts := fun h ↦
  not_tm2Decidable_halting 0 (tm2Decidable_of_manyOneReducible
    ⟨fun c ↦ (c, 0), Computable.pair Computable.id (Computable.const 0), fun _ ↦ Iff.rfl⟩ h)

/-- **Acceptance is undecidable.** No multi-stack Turing machine decides, for pairs $(c, n)$ of a
partial recursive code and a natural number, whether $c$ accepts $n$, that is, halts on $n$ with
output $0$.

This is Sipser's Theorem 4.11, with partial recursive codes in place of Turing machines. -/
theorem not_tm2Decidable_accepts : ¬TM2Decidable Accepts := fun h ↦
  not_tm2Decidable_halts (tm2Decidable_of_manyOneReducible manyOneReducible_halts_accepts h)

/-! ### Regularity -/

/-- **Unary language of a set of naturals.** For a set $S \subseteq \mathbb{N}$, the unary
language of $S$ is the language over the one-letter alphabet $\{\ast\}$ consisting of the words
whose length lies in $S$. -/
def unaryLang (S : Set ℕ) : Language Unit := {w | w.length ∈ S}

/-- **Codes with a regular halting set.** A partial recursive code $c$ has a regular halting set
when the unary language of its domain (the set of inputs on which $c$ halts), that is, the
language of the words over a one-letter alphabet whose length lies in the domain of $c$, is
regular.

This is a domain analogue of Sipser's $\mathrm{REGULAR}_{\mathrm{TM}}$, which asks about the
accepted words instead. -/
def RegularDomainCode (c : Code) : Prop := (unaryLang c.eval.Dom).IsRegular

theorem isRegular_unaryLang_univ : (unaryLang Set.univ).IsRegular := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ ↦ (), (), Set.univ⟩, ?_⟩
  ext w
  exact ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩

/-- **The unary squares are not regular.** The unary language of the perfect squares, the set of
words over a one-letter alphabet whose length is $m^2$ for some $m \in \mathbb{N}$, is not regular.

The proof uses the pumping lemma: if a DFA with $N$ states accepted this language, pumping the word
of length $N^2$ by a block of length between $1$ and $N$ would give a length strictly between $N^2$
and $(N + 1)^2$. -/
theorem not_isRegular_unaryLang_squares :
    ¬(unaryLang {n | ∃ m, n = m * m}).IsRegular := by
  rintro ⟨σ, _, M, hM⟩
  set N := Fintype.card σ
  have hx : List.replicate (N * N) () ∈ M.accepts := by
    rw [hM]
    exact ⟨N, by simp⟩
  obtain ⟨a, b, c, hxabc, hab, hb, hpump⟩ :=
    M.pumping_lemma hx (by simp only [List.length_replicate]; exact Nat.le_mul_self N)
  have hlen : a.length + b.length + c.length = N * N := by
    have := congrArg List.length hxabc
    simp only [List.length_replicate, List.length_append] at this
    omega
  have hmem : a ++ (b ++ b) ++ c ∈ M.accepts := by
    apply hpump
    refine Language.mem_mul.mpr ⟨a ++ (b ++ b), Language.mem_mul.mpr ⟨a, rfl, b ++ b, ?_, rfl⟩,
      c, rfl, rfl⟩
    refine Language.mem_kstar.mpr ⟨[b, b], by simp, fun y hy ↦ ?_⟩
    rcases List.mem_pair.mp hy with rfl | rfl <;> exact Set.mem_singleton _
  rw [hM] at hmem
  obtain ⟨m, hm⟩ := hmem
  simp only [List.length_append] at hm
  have hb1 : 1 ≤ b.length := List.length_pos_iff.mpr hb
  -- `N² < N² + |b| ≤ N² + N < (N + 1)²`
  have hlo : N * N < m * m := by omega
  have hhi : m * m < (N + 1) * (N + 1) := by nlinarith
  have h1 : N < m := by nlinarith
  have h2 : m < N + 1 := by nlinarith
  omega

/-- **Partial function of the halting-to-regularity reduction.** For a partial recursive code
$c$ and natural numbers $n$ and $x$, the value at $((c, n), x)$ is $0$ if $x$ is a perfect
square; otherwise it is defined exactly when $c$ halts on input $n$, and then it is $0$. -/
def regularRedFun (q : Code × ℕ) (x : ℕ) : Part ℕ :=
  if Nat.sqrt x * Nat.sqrt x = x then Part.some 0 else (q.1.eval q.2).map fun _ ↦ 0

theorem partrec₂_regularRedFun : Partrec₂ regularRedFun := by
  have hsq : Computable₂ fun (_ : Code × ℕ) (x : ℕ) ↦ decide (Nat.sqrt x * Nat.sqrt x = x) :=
    (Primrec.eq.comp (Primrec.nat_mul.comp (Primrec.nat_sqrt.comp Primrec.snd)
      (Primrec.nat_sqrt.comp Primrec.snd)) Primrec.snd).decide.to_comp
  have hrun : Partrec₂ fun (q : Code × ℕ) (_ : ℕ) ↦ (q.1.eval q.2).map fun _ ↦ (0 : ℕ) :=
    ((Code.eval_part.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst)).map (Computable.const 0).to₂)
  refine (Partrec.cond hsq (Partrec.const' (Part.some 0)) hrun).of_eq fun p ↦ ?_
  by_cases h : Nat.sqrt p.2 * Nat.sqrt p.2 = p.2 <;> simp [regularRedFun, h]

/-- **A single code for the regularity reduction function.** For a pair $q = (c, n)$ of a partial
recursive code and a natural number, let $g_q$ be the partial function on $\mathbb{N}$ that on
input $x$ halts with output $0$ if $x$ is a perfect square, and otherwise runs $c$ on $n$ and,
if that halts, outputs $0$ (and is undefined if it does not). Write $\ulcorner q \urcorner$ for
the standard encoding of $q$ as a natural number, and $\langle a, b \rangle$ for the standard
pairing of natural numbers $a$ and $b$. There is a partial recursive code $U$ such that for every
such pair $q$ and every $x \in \mathbb{N}$, the value of $U$ at
$\langle \ulcorner q \urcorner, x \rangle$ equals $g_q(x)$ as a partial value: one is defined
exactly when the other is, and then they agree. -/
theorem exists_code_regularRedFun :
    ∃ U : Code, ∀ q x, U.eval (Nat.pair (encode q) x) = regularRedFun q x := by
  have hG : Partrec fun m : ℕ ↦ (Part.ofOption (decode (α := Code × ℕ) m.unpair.1)).bind
      fun q ↦ regularRedFun q m.unpair.2 :=
    Partrec.bind (Computable.ofOption (Computable.decode.comp
      (Computable.fst.comp Computable.unpair)))
      (partrec₂_regularRedFun.comp Computable.snd
        (Computable.snd.comp (Computable.unpair.comp Computable.fst)))
  obtain ⟨U, hU⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hG)
  refine ⟨U, fun q x ↦ ?_⟩
  rw [hU]
  simp only [Nat.unpair_pair, Encodable.encodek, Part.coe_some, Part.bind_some]

theorem dom_regularRedFun (q : Code × ℕ) :
    {x | (regularRedFun q x).Dom} = {x | (∃ m, x = m * m) ∨ Halts q} := by
  ext x
  simp only [Set.mem_ofPred_eq, regularRedFun, Halts]
  have hsq : Nat.sqrt x * Nat.sqrt x = x ↔ ∃ m, x = m * m := by
    rw [← Nat.exists_mul_self]
    exact ⟨fun ⟨m, h⟩ ↦ ⟨m, h.symm⟩, fun ⟨m, h⟩ ↦ ⟨m, h.symm⟩⟩
  by_cases h : Nat.sqrt x * Nat.sqrt x = x
  · simp only [h, ↓reduceIte, Part.some_dom, true_iff]
    exact Or.inl (hsq.mp h)
  · simp only [h, ↓reduceIte, Part.map_Dom]
    exact ⟨Or.inr, fun h' ↦ h'.resolve_left fun hm ↦ h (hsq.mpr hm)⟩

/-- **Halting reduces to regularity of halting sets.** There is a computable map $f$ from pairs
$(c, n)$ of a partial recursive code and a natural number to partial recursive codes such that for
every pair $(c, n)$, the code $c$ halts on $n$ if and only if the halting set of $f(c, n)$ (the set
of inputs on which it halts), read as a unary language, is regular. That is, halting many-one
reduces to regularity of halting sets.

The construction follows Sipser's proof of Theorem 5.3: $f(c, n)$ halts on every perfect square,
and on every input if $c$ halts on $n$. -/
theorem manyOneReducible_halts_regularDomain : ManyOneReducible Halts RegularDomainCode := by
  obtain ⟨U, hU⟩ := exists_code_regularRedFun
  refine ⟨fun q ↦ Code.curry U (encode q), ?_, fun q ↦ ?_⟩
  · exact (Code.primrec₂_curry.comp (Primrec.const U) Primrec.encode).to_comp
  · have hdom : (Code.curry U (encode q)).eval.Dom = {x | (∃ m, x = m * m) ∨ Halts q} := by
      rw [← dom_regularRedFun]
      ext x
      simp only [PFun.dom_eq, Set.mem_ofPred_eq, Code.eval_curry, hU]
      exact Part.dom_iff_mem.symm
    simp only [RegularDomainCode, hdom]
    by_cases hq : Halts q
    · simp only [hq, or_true, Set.ofPred_true, true_iff]
      exact isRegular_unaryLang_univ
    · simp only [hq, or_false, false_iff]
      exact not_isRegular_unaryLang_squares

/-- **Regularity of halting sets is undecidable.** For a partial recursive code $c$, let
$\operatorname{dom}(c) \subseteq \mathbb{N}$ be the set of inputs on which $c$ halts. The
property of $c$ that the unary language $\{w \in \{\ast\}^* : |w| \in \operatorname{dom}(c)\}$
is regular is not decidable by a multi-stack Turing machine. -/
theorem not_tm2Decidable_regularDomain : ¬TM2Decidable RegularDomainCode := fun h ↦
  not_tm2Decidable_halts
    (tm2Decidable_of_manyOneReducible manyOneReducible_halts_regularDomain h)

@[deprecated (since := "2026-10-15")] alias RegularCode := RegularDomainCode
@[deprecated (since := "2026-10-15")] alias manyOneReducible_halts_regular :=
  manyOneReducible_halts_regularDomain
@[deprecated (since := "2026-10-15")] alias not_tm2Decidable_regular :=
  not_tm2Decidable_regularDomain

end Cslib.Decidability
