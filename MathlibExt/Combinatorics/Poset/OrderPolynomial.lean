/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Poset.LinearExtension
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Finset.Sort
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Order polynomials of finite posets

For a finite poset `P` with `p` elements, Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed.
(author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf), Sections 3.12 and
3.15.3, counts

* `orderPolynomialValue P m = Ω_P(m)`: order-preserving maps `P → [m]`;
* `strictOrderPolynomialValue P m = Ω̄_P(m)`: strictly order-preserving maps `P → [m]`;
* `surjMonotoneCount P s = e_P(s)`: surjective order-preserving maps `P → [s]`.

Here `[m]` is represented by `Fin m`. By `m + 1 - σ` these also count order-reversing maps, that is
the `P`-partitions (and strict `P`-partitions) of a naturally labelled poset with parts in `[m]`,
which is how Section 3.15.3 phrases them. Main results:

* `surjMonotoneCount_card_eq`: `e_P(p) = e(P)`, the number of linear extensions;
* `orderPolynomialValue_eq_sum`: `Ω_P(m) = ∑_{s=0}^{p} e_P(s) C(m, s)`;
* `exists_orderPolynomial`: `Ω_P` is a polynomial of degree `p` with leading coefficient
  `e(P)/p!`.

The reciprocity theorem is proved in `MathlibExt.Combinatorics.Poset.OrderPolynomialReciprocity`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Poset.OrderPolynomial

variable (P : Type*) [PartialOrder P] [Fintype P]

/-- **Order polynomial (values).** For a finite poset `P` and `m : ℕ`, `Ω_P(m)` is the number of
order-preserving maps `σ : P → [m]` (`s ≤ t ⇒ σ(s) ≤ σ(t)`), with `[m]` represented by `Fin m`
(Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011,
Section 3.12, after Proposition 3.12.1). -/
noncomputable def orderPolynomialValue (m : ℕ) : ℕ :=
  Nat.card {σ : P → Fin m // Monotone σ}

/-- **Strict order polynomial (values).** `Ω̄_P(m)` is the number of strictly order-preserving
maps `σ : P → [m]` (`s < t ⇒ σ(s) < σ(t)`); equivalently, by `σ ↦ m + 1 - σ`, of strict
`P`-partitions with parts in `[m]` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's
draft of 15 July 2011, Section 3.15.3, `Ω_{P, ω̄}` for `ω` natural). -/
noncomputable def strictOrderPolynomialValue (m : ℕ) : ℕ :=
  Nat.card {σ : P → Fin m // StrictMono σ}

/-- **Surjective order-preserving maps.** `e_P(s)` is the number of surjective order-preserving
maps `P → [s]` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of
15 July 2011, Section 3.15.3, `e_{P, ω}(s)` for `ω` natural, after reversing the order of
`[s]`). -/
noncomputable def surjMonotoneCount (s : ℕ) : ℕ :=
  Nat.card {σ : P → Fin s // Monotone σ ∧ Function.Surjective σ}

/-- **Surjective order-preserving maps onto `[p]` are linear extensions.** For a poset with
`p` elements, `e_P(p) = e(P)`: a surjective map `P → [p]` is bijective, so the surjective
order-preserving maps onto `[p]` are exactly the linear extensions (Stanley, *Enumerative
Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Section 3.15.3: "for any `ω`
we have `e_{P, ω}(p) = e(P)`"). -/
theorem surjMonotoneCount_card_eq :
    surjMonotoneCount P (Fintype.card P) = (FinPoset.linearExtensions P).card := by
  classical
  unfold surjMonotoneCount
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
  rw [FinPoset.mem_linearExtensions]
  constructor
  · rintro ⟨hmono, hsurj⟩
    exact ⟨(Fintype.bijective_iff_surjective_and_card σ).mpr ⟨hsurj, by simp⟩, hmono⟩
  · rintro ⟨hbij, hmono⟩
    exact ⟨hmono, hbij.2⟩

omit [Fintype P] in
/-- **One colour.** `Ω_P(1) = 1`: the constant map is the only map `P → [1]`. -/
theorem orderPolynomialValue_one : orderPolynomialValue P 1 = 1 := by
  unfold orderPolynomialValue
  have : Unique {σ : P → Fin 1 // Monotone σ} :=
    ⟨⟨⟨fun _ => 0, fun _ _ _ => le_rfl⟩⟩,
      fun σ => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩
  exact Nat.card_unique

open Finset

/-- **Order-preserving maps with a given image.** For `S ⊆ [m]`, the order-preserving maps `P → [m]`
with image `S` correspond to the surjective order-preserving maps `P → [|S|]`, by composing with the
increasing enumeration of `S` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft
of 15 July 2011, Section 3.15.3, "by first choosing the image"). -/
noncomputable def imageEquiv {m : ℕ} (S : Finset (Fin m)) :
    {σ : P → Fin m // Monotone σ ∧ univ.image σ = S} ≃
      {τ : P → Fin S.card // Monotone τ ∧ Function.Surjective τ} where
  toFun σ := ⟨fun x => (S.orderIsoOfFin rfl).symm
      ⟨σ.1 x, (Finset.ext_iff.mp σ.2.2 _).mp (mem_image_of_mem _ (mem_univ x))⟩,
    fun x y hxy => (S.orderIsoOfFin rfl).symm.monotone (Subtype.mk_le_mk.mpr (σ.2.1 hxy)),
    fun i => by
      have hi : S.orderEmbOfFin rfl i ∈ univ.image σ.1 :=
        (Finset.ext_iff.mp σ.2.2 _).mpr (S.orderEmbOfFin_mem rfl i)
      obtain ⟨x, -, hx⟩ := mem_image.mp hi
      refine ⟨x, ?_⟩
      rw [OrderIso.symm_apply_eq]
      exact Subtype.ext (by rw [coe_orderIsoOfFin_apply]; exact hx)⟩
  invFun τ := ⟨fun x => S.orderEmbOfFin rfl (τ.1 x),
    fun x y hxy => (S.orderEmbOfFin rfl).monotone (τ.2.1 hxy), by
      ext a
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨x, rfl⟩; exact S.orderEmbOfFin_mem rfl _
      · intro ha
        obtain ⟨i, hi⟩ : a ∈ Set.range (S.orderEmbOfFin rfl) := by
          rw [range_orderEmbOfFin]; exact ha
        obtain ⟨x, hx⟩ := τ.2.2 i
        exact ⟨x, by rw [hx, hi]⟩⟩
  left_inv σ := by
    refine Subtype.ext (funext fun x => ?_)
    change S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨σ.1 x, _⟩) = σ.1 x
    rw [← coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  right_inv τ := by
    refine Subtype.ext (funext fun x => ?_)
    change (S.orderIsoOfFin rfl).symm ⟨S.orderEmbOfFin rfl (τ.1 x), _⟩ = τ.1 x
    rw [OrderIso.symm_apply_eq]
    exact Subtype.ext (coe_orderIsoOfFin_apply _ _ _).symm

set_option linter.unusedFintypeInType false in
/-- **Grouping order-preserving maps by their image.** `Ω_P(m) = ∑_{S ⊆ [m]} e_P(|S|)`. -/
theorem orderPolynomialValue_eq_sum_finset (m : ℕ) :
    orderPolynomialValue P m = ∑ S : Finset (Fin m), surjMonotoneCount P S.card := by
  classical
  unfold orderPolynomialValue surjMonotoneCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_eq_sum_card_fiberwise (f := fun σ => univ.image σ) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun S _ => ?_
  rw [← Nat.card_congr (imageEquiv P S), Nat.card_eq_fintype_card, Fintype.card_subtype,
    filter_filter]

/-- **No surjection onto a larger chain.** `e_P(s) = 0` when `s > #P`. -/
theorem surjMonotoneCount_eq_zero {s : ℕ} (hs : Fintype.card P < s) :
    surjMonotoneCount P s = 0 := by
  unfold surjMonotoneCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨σ, -, hσ⟩
  have := Fintype.card_le_of_surjective σ hσ
  simp at this
  omega

/-- **Expansion of the order polynomial in binomial coefficients.** For every `m`, `Ω_P(m) =
∑_{s=0}^{p} e_P(s) C(m, s)`, by first choosing the image of an order-preserving map `P → [m]`
(Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Section
3.15.3, display before Theorem 3.15.8, there summed from `s = 1`; the term `s = 0` vanishes unless
`P` is empty, where it is the only term). -/
theorem orderPolynomialValue_eq_sum (m : ℕ) :
    orderPolynomialValue P m =
      ∑ s ∈ range (Fintype.card P + 1), surjMonotoneCount P s * m.choose s := by
  classical
  rw [orderPolynomialValue_eq_sum_finset, ← powerset_univ,
    sum_powerset_apply_card (fun s => surjMonotoneCount P s), card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_id]
  set N := max m (Fintype.card P) + 1
  have h1 : ∑ s ∈ range (m + 1), m.choose s * surjMonotoneCount P s =
      ∑ s ∈ range N, m.choose s * surjMonotoneCount P s :=
    sum_subset (range_subset_range.mpr (by omega)) fun s hs hs' => by
      simp only [mem_range, not_lt] at hs hs'
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  have h2 : ∑ s ∈ range (Fintype.card P + 1), surjMonotoneCount P s * m.choose s =
      ∑ s ∈ range N, surjMonotoneCount P s * m.choose s :=
    sum_subset (range_subset_range.mpr (by omega)) fun s hs hs' => by
      simp only [mem_range, not_lt] at hs hs'
      rw [surjMonotoneCount_eq_zero P (by omega), zero_mul]
  rw [h1, h2]
  exact sum_congr rfl fun s _ => Nat.mul_comm _ _

open Polynomial in
/-- **The order polynomial.** `Ω_P(m)` is a polynomial function of `m` of degree `p = #P` with
leading coefficient `e(P)/p!`, where `e(P)` is the number of linear extensions of `P` (Stanley,
*Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Section 3.12, after
Proposition 3.12.1, and Section 3.15.3). The polynomial is `∑_{s ≤ p} e_P(s) x(x - 1)⋯(x - s + 1) /
s!`. -/
theorem exists_orderPolynomial :
    ∃ Q : ℚ[X], Q.natDegree = Fintype.card P ∧
      Q.leadingCoeff = ((FinPoset.linearExtensions P).card : ℚ) / (Fintype.card P).factorial ∧
      ∀ m : ℕ, Q.eval (m : ℚ) = orderPolynomialValue P m := by
  set p := Fintype.card P
  let c : ℕ → ℚ := fun s => (surjMonotoneCount P s : ℚ) / s.factorial
  let low : ℚ[X] := ∑ s ∈ range p, C (c s) * descPochhammer ℚ s
  let top : ℚ[X] := C (c p) * descPochhammer ℚ p
  have he : surjMonotoneCount P p = (FinPoset.linearExtensions P).card :=
    surjMonotoneCount_card_eq P
  have hcp : c p ≠ 0 := by
    have hpos := FinPoset.card_linearExtensions_pos P
    simp only [c, he]
    exact div_ne_zero (by exact_mod_cast hpos.ne') (by exact_mod_cast (Nat.factorial_pos _).ne')
  have hdtop : top.degree = p := by
    simp only [top]
    rw [degree_C_mul hcp, degree_eq_natDegree (monic_descPochhammer ℚ p).ne_zero,
      descPochhammer_natDegree]
  have hlow : low.degree < top.degree := by
    rw [hdtop]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro s hs
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    refine lt_of_le_of_lt (WithBot.coe_le_coe.mpr ((natDegree_C_mul_le _ _).trans
      (descPochhammer_natDegree ℚ s).le)) ?_
    exact WithBot.coe_lt_coe.mpr (mem_range.mp hs)
  refine ⟨low + top, ?_, ?_, fun m => ?_⟩
  · rw [natDegree_add_eq_right_of_degree_lt hlow, natDegree_eq_of_degree_eq_some hdtop]
  · rw [leadingCoeff_add_of_degree_lt hlow]
    simp only [top, leadingCoeff_mul, leadingCoeff_C, (monic_descPochhammer ℚ p).leadingCoeff,
      mul_one, c, he]
    rfl
  · rw [orderPolynomialValue_eq_sum, Nat.cast_sum]
    simp only [low, top, eval_add, eval_finsetSum, eval_mul, eval_C,
      descPochhammer_eval_eq_descFactorial]
    rw [← sum_range_succ (fun s => c s * (m.descFactorial s : ℚ))]
    refine sum_congr rfl fun s _ => ?_
    simp only [c]
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    have : (s.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
    push_cast
    rw [← mul_assoc, div_mul_cancel₀ _ this]

end MathlibExt.Combinatorics.Poset.OrderPolynomial
