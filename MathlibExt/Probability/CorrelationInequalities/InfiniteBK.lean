/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.InfiniteHarris
public import MathlibExt.Probability.CorrelationInequalities.BK

import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# BK inequality on countable configuration spaces

For a countable set `E`, the van den Berg–Kesten inequality for the product Bernoulli measure on
`ConfigSpace E = E → Bool` holds for increasing events that depend on finitely many coordinates.
The proof restricts both events and their disjoint occurrence to a finite window `F` and applies
`StatMech.bk_inequality` there.

## Main results

* `disjointOccurrence_isIncreasing`: `A □ B` is increasing when `A` and `B` are.
* `StatMech.ibk_disjointOccurrence_dependsOn`: `A □ B` depends only on `F` when `A` and `B` do.
* `StatMech.ibk_inequality_of_finite_dependsOn`: the **BK inequality**
  `P_p(A □ B) ≤ P_p(A) * P_p(B)` for increasing events depending on finitely many coordinates.
* `StatMech.ibk_triple_of_finite_dependsOn`, `StatMech.ibk_criterion_of_finite_dependsOn`:
  the three-event form `P_p(P □ (Q □ R)) ≤ P_p(P) P_p(Q) P_p(R)` and the resulting union bound.
* `StatMech.ibk_measure_mono_parameter`: `p ↦ P_p(A)` is monotone for an increasing event `A`
  depending on finitely many coordinates.

## References

* J. van den Berg, H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
-/

open MeasureTheory Set
open scoped NNReal

namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]

omit [Countable E] [DecidableEq E] in
/-- If `A` depends only on `F` and occurs on `K` at `ω`, then it occurs on `K ∩ F` at every
configuration agreeing with `ω` on `F`. -/
theorem ibk_occursOn_inter_finite {A : Set (ConfigSpace E)} {F : Finset E}
    {K : Set E} {omega omega' : ConfigSpace E}
    (hA : DependsOn A (F : Set E)) (hocc : OccursOn A K omega)
    (hagree : agreeOn (F : Set E) omega omega') :
    OccursOn A (K ∩ (F : Set E)) omega' := by
  classical
  intro z hz
  let z' : ConfigSpace E := fun e => if he : e ∈ F then z e else omega e
  have hz'mem : z' ∈ A := hocc z' (by
    intro e heK
    by_cases heF : e ∈ F
    · simp only [z', dite_eq_left heF]
      exact (hz e ⟨heK, heF⟩).trans (hagree e heF)
    · simp only [z', dite_eq_right heF])
  exact (hA z' z (by
    intro e heF
    have heF' : e ∈ F := heF
    simp [z', heF'])).mp hz'mem

omit [Countable E] [DecidableEq E] in
/-- If `A` and `B` depend only on the coordinates in `F`, so does `A □ B`. -/
theorem ibk_disjointOccurrence_dependsOn {A B : Set (ConfigSpace E)} {F : Finset E}
    (hA : DependsOn A (F : Set E)) (hB : DependsOn B (F : Set E)) :
    DependsOn (disjointOccurrence A B) (F : Set E) := by
  classical
  intro omega omega' hagree
  constructor
  · rintro ⟨K, L, hKL, hAK, hBL⟩
    exact ⟨K ∩ (F : Set E), L ∩ (F : Set E),
      hKL.mono Set.inter_subset_left Set.inter_subset_left,
      ibk_occursOn_inter_finite hA hAK hagree,
      ibk_occursOn_inter_finite hB hBL hagree⟩
  · rintro ⟨K, L, hKL, hAK, hBL⟩
    have hagree' : agreeOn (F : Set E) omega' omega := agreeOn_symm hagree
    exact ⟨K ∩ (F : Set E), L ∩ (F : Set E),
      hKL.mono Set.inter_subset_left Set.inter_subset_left,
      ibk_occursOn_inter_finite hA hAK hagree',
      ibk_occursOn_inter_finite hB hBL hagree'⟩

omit [Countable E] in
/-- The section on `F` of `A □ B` is contained in the disjoint occurrence of the sections. -/
theorem ibk_section_disjointOccurrence_subset (A B : Set (ConfigSpace E))
    (F : Finset E) :
    ih_section (disjointOccurrence A B) F ⊆
      disjointOccurrence (ih_section A F) (ih_section B F) := by
  rintro eta ⟨K, L, hKL, hAK, hBL⟩
  let KF : Set F := {i | (i : E) ∈ K}
  let LF : Set F := {i | (i : E) ∈ L}
  refine ⟨KF, LF, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro i hiK hiL
    exact (Set.disjoint_left.1 hKL) hiK hiL
  · intro eta' heta
    change ih_fill F eta' ∈ A
    apply hAK
    intro e heK
    by_cases heF : e ∈ F
    · have heq := heta ⟨e, heF⟩ (show (⟨e, heF⟩ : F) ∈ KF from heK)
      simpa [ih_fill, heF] using heq
    · simp [ih_fill, heF]
  · intro eta' heta
    change ih_fill F eta' ∈ B
    apply hBL
    intro e heL
    by_cases heF : e ∈ F
    · have heq := heta ⟨e, heF⟩ (show (⟨e, heF⟩ : F) ∈ LF from heL)
      simpa [ih_fill, heF] using heq
    · simp [ih_fill, heF]

omit [DecidableEq E] in
/-- The **BK inequality** on a countable configuration space: for increasing events `A, B`
depending only on the coordinates in a finite set `F`, `P_p(A □ B) ≤ P_p(A) * P_p(B)`. -/
theorem ibk_inequality_of_finite_dependsOn {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (F : Finset E)
    (hAdep : DependsOn A (F : Set E)) (hBdep : DependsOn B (F : Set E))
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤
      (bernoulliProductMeasure (E := E) p hp).real A *
        (bernoulliProductMeasure (E := E) p hp).real B := by
  classical
  have hDOdep := ibk_disjointOccurrence_dependsOn hAdep hBdep
  have hDOrw := ih_eq_cylinder_of_dependsOn F hDOdep
  have hArw := ih_eq_cylinder_of_dependsOn F hAdep
  have hBrw := ih_eq_cylinder_of_dependsOn F hBdep
  have hDOprob :
      (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) =
        (bernoulliProductMeasure (E := F) p hp).real
          (ih_section (disjointOccurrence A B) F) := by
    calc
      (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) =
          (bernoulliProductMeasure (E := E) p hp).real
            (MeasureTheory.cylinder F (ih_section (disjointOccurrence A B) F)) :=
        congrArg (bernoulliProductMeasure (E := E) p hp).real hDOrw
      _ = _ := realProb_cylinder p hp F _
  have hAprob :
      (bernoulliProductMeasure (E := E) p hp).real A =
        (bernoulliProductMeasure (E := F) p hp).real (ih_section A F) := by
    calc
      (bernoulliProductMeasure (E := E) p hp).real A =
          (bernoulliProductMeasure (E := E) p hp).real
            (MeasureTheory.cylinder F (ih_section A F)) :=
        congrArg (bernoulliProductMeasure (E := E) p hp).real hArw
      _ = _ := realProb_cylinder p hp F _
  have hBprob :
      (bernoulliProductMeasure (E := E) p hp).real B =
        (bernoulliProductMeasure (E := F) p hp).real (ih_section B F) := by
    calc
      (bernoulliProductMeasure (E := E) p hp).real B =
          (bernoulliProductMeasure (E := E) p hp).real
            (MeasureTheory.cylinder F (ih_section B F)) :=
        congrArg (bernoulliProductMeasure (E := E) p hp).real hBrw
      _ = _ := realProb_cylinder p hp F _
  calc
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) =
        (bernoulliProductMeasure (E := F) p hp).real
          (ih_section (disjointOccurrence A B) F) := hDOprob
    _ ≤ (bernoulliProductMeasure (E := F) p hp).real
          (disjointOccurrence (ih_section A F) (ih_section B F)) :=
      measureReal_mono (ibk_section_disjointOccurrence_subset A B F)
    _ ≤ (bernoulliProductMeasure (E := F) p hp).real (ih_section A F) *
          (bernoulliProductMeasure (E := F) p hp).real (ih_section B F) :=
      bk_inequality hp (ih_section_isIncreasing hAinc F)
        (ih_section_isIncreasing hBinc F)
    _ = (bernoulliProductMeasure (E := E) p hp).real A *
          (bernoulliProductMeasure (E := E) p hp).real B :=
      (congrArg₂ (· * ·) hAprob hBprob).symm

omit [DecidableEq E] in
/-- The BK inequality for three increasing events depending on finitely many coordinates:
`P_p(P □ (Q □ R)) ≤ P_p(P) * P_p(Q) * P_p(R)`. -/
theorem ibk_triple_of_finite_dependsOn {p : ℝ≥0} (hp : p ≤ 1)
    {P Q R : Set (ConfigSpace E)} (F : Finset E)
    (hPdep : DependsOn P (F : Set E)) (hQdep : DependsOn Q (F : Set E))
    (hRdep : DependsOn R (F : Set E))
    (hP : IsIncreasing P) (hQ : IsIncreasing Q) (hR : IsIncreasing R) :
    (bernoulliProductMeasure (E := E) p hp).real
        (disjointOccurrence P (disjointOccurrence Q R)) ≤
      (bernoulliProductMeasure (E := E) p hp).real P *
        (bernoulliProductMeasure (E := E) p hp).real Q *
        (bernoulliProductMeasure (E := E) p hp).real R := by
  classical
  set mu := bernoulliProductMeasure (E := E) p hp
  have hQRdep := ibk_disjointOccurrence_dependsOn hQdep hRdep
  calc
    mu.real (disjointOccurrence P (disjointOccurrence Q R)) ≤
        mu.real P * mu.real (disjointOccurrence Q R) :=
      ibk_inequality_of_finite_dependsOn hp F hPdep hQRdep hP
        (disjointOccurrence_isIncreasing hQ hR)
    _ ≤ mu.real P * (mu.real Q * mu.real R) :=
      mul_le_mul_of_nonneg_left
        (ibk_inequality_of_finite_dependsOn hp F hQdep hRdep hQ hR)
        measureReal_nonneg
    _ = mu.real P * mu.real Q * mu.real R := by ring

omit [DecidableEq E] in
/-- Union bound from the three-event BK inequality: if `C ⊆ ⋃ i ∈ s, P i □ (Q i □ R i)` with
all events increasing and depending on a common finite window, then
`P_p(C) ≤ ∑ i ∈ s, P_p(P i) * P_p(Q i) * P_p(R i)`. -/
theorem ibk_criterion_of_finite_dependsOn {I : Type*} {p : ℝ≥0} (hp : p ≤ 1)
    (s : Finset I) (P Q R : I → Set (ConfigSpace E)) (F : Finset E)
    (hPdep : ∀ i ∈ s, DependsOn (P i) (F : Set E))
    (hQdep : ∀ i ∈ s, DependsOn (Q i) (F : Set E))
    (hRdep : ∀ i ∈ s, DependsOn (R i) (F : Set E))
    (hP : ∀ i ∈ s, IsIncreasing (P i))
    (hQ : ∀ i ∈ s, IsIncreasing (Q i))
    (hR : ∀ i ∈ s, IsIncreasing (R i))
    {C : Set (ConfigSpace E)}
    (hC : C ⊆ ⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :
    (bernoulliProductMeasure (E := E) p hp).real C ≤
      ∑ i ∈ s, (bernoulliProductMeasure (E := E) p hp).real (P i) *
        (bernoulliProductMeasure (E := E) p hp).real (Q i) *
        (bernoulliProductMeasure (E := E) p hp).real (R i) := by
  classical
  set mu := bernoulliProductMeasure (E := E) p hp
  calc
    mu.real C ≤ mu.real
        (⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
      measureReal_mono hC (measure_ne_top _ _)
    _ ≤ ∑ i ∈ s, mu.real (disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
      measureReal_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, mu.real (P i) * mu.real (Q i) * mu.real (R i) :=
      Finset.sum_le_sum fun i hi =>
        ibk_triple_of_finite_dependsOn hp F (hPdep i hi) (hQdep i hi)
          (hRdep i hi) (hP i hi) (hQ i hi) (hR i hi)

omit [DecidableEq E] in
/-- Monotonicity in the parameter: for an increasing event `A` depending only on a finite set of
coordinates and `p ≤ q`, `P_p(A) ≤ P_q(A)`. The proof uses Russo's formula. -/
theorem ibk_measure_mono_parameter {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≤ q) {A : Set (ConfigSpace E)} (F : Finset E)
    (hAdep : DependsOn A (F : Set E)) (hAinc : IsIncreasing A) :
    (bernoulliProductMeasure (E := E) p hp).real A ≤
      (bernoulliProductMeasure (E := E) q hq).real A := by
  classical
  let B := F.restrict '' A
  have hdiff : Differentiable ℝ (fun r => prob r B) :=
    differentiable_realProb_cylinder A F
  have hmono : MonotoneOn (fun r => prob r B) (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
      hdiff.continuous.continuousOn hdiff.differentiableOn
    intro r hr
    have hr' : r ∈ Set.Ioo (0 : ℝ) 1 := by
      rwa [interior_Icc] at hr
    rw [deriv_prob_eq_sum_pivotalProb B
      (isIncreasing_restrict_image A hAinc F) r]
    exact Finset.sum_nonneg fun e _ =>
      pivotalProb_nonneg (le_of_lt hr'.1) (le_of_lt hr'.2) B e
  rw [realProb_cylinder_eq_prob p hp A F
      (ih_indicator_dependsOn_of_event hAdep),
    realProb_cylinder_eq_prob q hq A F
      (ih_indicator_dependsOn_of_event hAdep)]
  exact hmono ⟨p.coe_nonneg, by exact_mod_cast hp⟩
    ⟨q.coe_nonneg, by exact_mod_cast hq⟩ (by exact_mod_cast hpq)

end StatMech
