/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.Inequalities.Reimer

open MeasureTheory Finset
open scoped NNReal BigOperators

namespace StatMech

open ConfigSpace

variable {E : Type*}











def DeterminedBy (A : Set (ConfigSpace E)) (K : Set E) : Prop :=
  ∀ ω ω' : ConfigSpace E, agreeOn K ω ω' → (ω ∈ A ↔ ω' ∈ A)



lemma DeterminedBy.mono {A : Set (ConfigSpace E)} {K K' : Set E} (hKK' : K ⊆ K')
    (h : DeterminedBy A K) : DeterminedBy A K' :=
  fun ω ω' hω' => h ω ω' (agreeOn_mono hKK' hω')



lemma determinedBy_occursOn {A : Set (ConfigSpace E)} {K : Set E}
    (h : DeterminedBy A K) {ω : ConfigSpace E} (hω : ω ∈ A) : OccursOn A K ω :=
  fun ω' hω' => (h ω ω' hω').mp hω










theorem disjointOccurrence_eq_inter_of_determined {A B : Set (ConfigSpace E)} {K L : Set E}
    (hKL : Disjoint K L) (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    disjointOccurrence A B = A ∩ B := by
  refine Set.Subset.antisymm (disjointOccurrence_subset_inter A B) ?_
  rintro ω ⟨hωA, hωB⟩
  exact ⟨K, L, hKL, determinedBy_occursOn hA hωA, determinedBy_occursOn hB hωB⟩











section Fintype

variable [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in

private lemma restP_symm (p : E → Prop) [DecidablePred p]
    (a : {x // p x} → Bool) (b : {x // ¬ p x} → Bool) :
    (fun x : {x // p x} =>
      (Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (a, b) x.1) = a := by
  funext x; simp only [Equiv.piEquivPiSubtypeProd]; exact dif_pos x.2

omit [Fintype E] [DecidableEq E] in


private lemma restNP_symm (p : E → Prop) [DecidablePred p]
    (a : {x // p x} → Bool) (b : {x // ¬ p x} → Bool) :
    (fun x : {x // ¬ p x} =>
      (Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (a, b) x.1) = b := by
  funext x; simp only [Equiv.piEquivPiSubtypeProd]; exact dif_neg x.2



private noncomputable def detIndicatorP (A : Set (ConfigSpace E)) (p : E → Prop)
    [DecidablePred p] (a : {x // p x} → Bool) : ℝ :=
  A.indicator (fun _ => (1 : ℝ))
    ((Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (a, fun _ => false))



private noncomputable def detIndicatorNP (B : Set (ConfigSpace E)) (p : E → Prop)
    [DecidablePred p] (b : {x // ¬ p x} → Bool) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    ((Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (fun _ => false, b))

omit [Fintype E] [DecidableEq E] in


private lemma detIndicatorP_eq (A : Set (ConfigSpace E)) (p : E → Prop) [DecidablePred p]
    (h : DeterminedBy A {x | p x}) (ω : ConfigSpace E) :
    A.indicator (fun _ => (1 : ℝ)) ω = detIndicatorP A p (fun x => ω x.1) := by
  unfold detIndicatorP
  set a := (fun x : {x // p x} => ω x.1) with ha
  set ω0 := (Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (a, fun _ => false) with hω0
  have hagree : agreeOn {x | p x} ω ω0 := by
    intro e he
    have : (fun x : {x // p x} => ω0 x.1) ⟨e, he⟩ = a ⟨e, he⟩ := by rw [hω0, restP_symm]
    simpa [ha] using this
  have hiff : ω ∈ A ↔ ω0 ∈ A := h ω ω0 hagree
  by_cases hmem : ω ∈ A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hiff.mpr hc))]

omit [Fintype E] [DecidableEq E] in


private lemma detIndicatorNP_eq (B : Set (ConfigSpace E)) (p : E → Prop) [DecidablePred p]
    (h : DeterminedBy B {x | ¬ p x}) (ω : ConfigSpace E) :
    B.indicator (fun _ => (1 : ℝ)) ω = detIndicatorNP B p (fun x => ω x.1) := by
  unfold detIndicatorNP
  set b := (fun x : {x // ¬ p x} => ω x.1) with hb
  set ω0 := (Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (fun _ => false, b) with hω0
  have hagree : agreeOn {x | ¬ p x} ω ω0 := by
    intro e he
    have : (fun x : {x // ¬ p x} => ω0 x.1) ⟨e, he⟩ = b ⟨e, he⟩ := by rw [hω0, restNP_symm]
    simpa [hb] using this
  have hiff : ω ∈ B ↔ ω0 ∈ B := h ω ω0 hagree
  by_cases hmem : ω ∈ B
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hiff.mpr hc))]





private lemma wprob_factor_aux (p : E → Prop) [DecidablePred p]
    (gA : ({x // p x} → Bool) → ℝ) (gB : ({x // ¬ p x} → Bool) → ℝ) (φ : E → Bool → ℝ) :
    (∑ ω : E → Bool, (gA (fun x => ω x.1) * gB (fun x => ω x.1)) * (∏ x, φ x (ω x)))
      = (∑ a : {x // p x} → Bool, gA a * ∏ x : {x // p x}, φ x.1 (a x))
        * (∑ b : {x // ¬ p x} → Bool, gB b * ∏ x : {x // ¬ p x}, φ x.1 (b x)) := by
  rw [Finset.sum_mul_sum]
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm
      (fun ω => (gA (fun x => ω x.1) * gB (fun x => ω x.1)) * (∏ x, φ x (ω x)))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  set ω := (Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (a, b) with hω
  have hrA : (fun x : {x // p x} => ω x.1) = a := by rw [hω, restP_symm]
  have hrB : (fun x : {x // ¬ p x} => ω x.1) = b := by rw [hω, restNP_symm]
  have hprod : (∏ x, φ x (ω x))
      = (∏ x : {x // p x}, φ x.1 (a x)) * (∏ x : {x // ¬ p x}, φ x.1 (b x)) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype p (fun x => φ x (ω x))]
    congr 1
    · apply Finset.prod_congr rfl; intro x _; congr 1; rw [hω]; exact congrFun (restP_symm p a b) x
    · apply Finset.prod_congr rfl; intro x _; congr 1; rw [hω]; exact congrFun (restNP_symm p a b) x
  rw [hrA, hrB, hprod]; ring



private lemma marginal_eq_one {I : Type*} [Fintype I] [DecidableEq I] (ψ : I → Bool → ℝ)
    (h1 : ∀ i, ψ i false + ψ i true = 1) :
    (∑ b : I → Bool, ∏ i, ψ i (b i)) = 1 := by
  have key := Finset.prod_univ_sum (ι := I) (fun (_ : I) => (Finset.univ : Finset Bool))
    (fun i b => ψ i b)
  rw [Fintype.piFinset_univ] at key
  rw [← key]
  apply Finset.prod_eq_one
  intro i _
  simp only [Fintype.sum_bool, add_comm]
  exact h1 i


private lemma wprob_eq_marginalP (A : Set (ConfigSpace E)) (p : E → Prop) [DecidablePred p]
    (φ : E → Bool → ℝ) (h1 : ∀ x, φ x false + φ x true = 1) (hA : DeterminedBy A {x | p x}) :
    wprob φ A = ∑ a : {x // p x} → Bool, detIndicatorP A p a * ∏ x : {x // p x}, φ x.1 (a x) := by
  unfold wprob pweight
  have hrw : (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * ∏ x, φ x (ω x))
      = ∑ ω : E → Bool,
          (detIndicatorP A p (fun x => ω x.1)
            * (fun (_ : {x // ¬ p x} → Bool) => (1 : ℝ)) (fun x => ω x.1)) * (∏ x, φ x (ω x)) := by
    apply Finset.sum_congr rfl; intro ω _; rw [detIndicatorP_eq A p hA ω]; ring
  rw [hrw, wprob_factor_aux p (detIndicatorP A p) (fun _ => 1) φ]
  simp only [one_mul]
  rw [marginal_eq_one (fun (x : {x // ¬ p x}) c => φ x.1 c) (fun x => h1 x.1), mul_one]



private lemma wprob_eq_marginalNP (B : Set (ConfigSpace E)) (p : E → Prop) [DecidablePred p]
    (φ : E → Bool → ℝ) (h1 : ∀ x, φ x false + φ x true = 1) (hB : DeterminedBy B {x | ¬ p x}) :
    wprob φ B
      = ∑ b : {x // ¬ p x} → Bool, detIndicatorNP B p b * ∏ x : {x // ¬ p x}, φ x.1 (b x) := by
  unfold wprob pweight
  have hrw : (∑ ω, B.indicator (fun _ => (1 : ℝ)) ω * ∏ x, φ x (ω x))
      = ∑ ω : E → Bool,
          ((fun (_ : {x // p x} → Bool) => (1 : ℝ)) (fun x => ω x.1)
            * detIndicatorNP B p (fun x => ω x.1)) * (∏ x, φ x (ω x)) := by
    apply Finset.sum_congr rfl; intro ω _; rw [detIndicatorNP_eq B p hB ω]; ring
  rw [hrw, wprob_factor_aux p (fun _ => 1) (detIndicatorNP B p) φ]
  simp only [one_mul]
  rw [marginal_eq_one (fun (x : {x // p x}) c => φ x.1 c) (fun x => h1 x.1), one_mul]

set_option linter.unusedDecidableInType false in




theorem wprob_inter_eq_mul_predicate (A B : Set (ConfigSpace E)) (p : E → Prop)
    [DecidablePred p] (φ : E → Bool → ℝ) (h1 : ∀ x, φ x false + φ x true = 1)
    (hA : DeterminedBy A {x | p x}) (hB : DeterminedBy B {x | ¬ p x}) :
    wprob φ (A ∩ B) = wprob φ A * wprob φ B := by
  rw [wprob_eq_marginalP A p φ h1 hA, wprob_eq_marginalNP B p φ h1 hB,
    ← wprob_factor_aux p (detIndicatorP A p) (detIndicatorNP B p) φ]
  unfold wprob pweight
  apply Finset.sum_congr rfl; intro ω _
  rw [← detIndicatorP_eq A p hA ω, ← detIndicatorNP_eq B p hB ω]
  by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
    simp [Set.indicator, ha, hb, Set.mem_inter_iff]




theorem wprob_inter_eq_mul_of_determined (A B : Set (ConfigSpace E)) {K L : Set E}
    (hKL : Disjoint K L) (φ : E → Bool → ℝ) (h1 : ∀ x, φ x false + φ x true = 1)
    (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    wprob φ (A ∩ B) = wprob φ A * wprob φ B := by
  classical
  have hL : L ⊆ {x | ¬ (x ∈ K)} := by
    rw [Set.disjoint_left] at hKL
    intro x hx; exact fun hxK => hKL hxK hx
  exact wprob_inter_eq_mul_predicate A B (fun x => x ∈ K) φ h1 hA (hB.mono hL)















theorem reimer_wprob_eq_of_determinedDisjoint (φ : E → Bool → ℝ)
    (h1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace E)} {K L : Set E}
    (hKL : Disjoint K L) (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    wprob φ (disjointOccurrence A B) = wprob φ A * wprob φ B := by
  rw [disjointOccurrence_eq_inter_of_determined hKL hA hB]
  exact wprob_inter_eq_mul_of_determined A B hKL φ h1 hA hB



theorem reimer_wprob_le_of_determinedDisjoint (φ : E → Bool → ℝ)
    (h1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace E)} {K L : Set E}
    (hKL : Disjoint K L) (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  le_of_eq (reimer_wprob_eq_of_determinedDisjoint φ h1 hKL hA hB)

end Fintype











theorem reimerCore_holds_on_determinedDisjoint
    (n : ℕ) (φ : Fin n → Bool → ℝ)
    (_hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1)
    (A B : Set (ConfigSpace (Fin n))) {K L : Set (Fin n)} (hKL : Disjoint K L)
    (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  reimer_wprob_le_of_determinedDisjoint φ hφ1 hKL hA hB



set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in




theorem reimer_bernoulli_eq_of_determinedDisjoint [Fintype E] [DecidableEq E] {p : ℝ≥0}
    (hp : p ≤ 1) {A B : Set (ConfigSpace E)} {K L : Set E} (hKL : Disjoint K L)
    (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      = (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  set φ : E → Bool → ℝ := fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b} with hφ
  have hφ1 : ∀ x, φ x false + φ x true = 1 := by
    intro _
    have h1 : (bernoulliMeasure p hp).real {false} = ((1 - p : ℝ≥0) : ℝ) := by
      rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal]
    have h2 : (bernoulliMeasure p hp).real {true} = (p : ℝ) := by
      rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]
    simp only [hφ]
    rw [h1, h2, NNReal.coe_sub hp, NNReal.coe_one]
    ring
  rw [bernoulli_real_eq_wprob hp (disjointOccurrence A B), bernoulli_real_eq_wprob hp A,
    bernoulli_real_eq_wprob hp B]
  exact reimer_wprob_eq_of_determinedDisjoint φ hφ1 hKL hA hB

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in



theorem reimer_inequality_determinedDisjoint [Fintype E] [DecidableEq E] {p : ℝ≥0}
    (hp : p ≤ 1) {A B : Set (ConfigSpace E)} {K L : Set E} (hKL : Disjoint K L)
    (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  le_of_eq (reimer_bernoulli_eq_of_determinedDisjoint hp hKL hA hB)

end StatMech
