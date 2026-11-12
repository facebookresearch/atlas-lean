/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Probability.InfiniteHarris
import Code.Inequalities.BK

open MeasureTheory Set
open scoped NNReal

namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]



theorem ibk_occursOn_mono_config {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {K : Set E} {omega omega' : ConfigSpace E} (homega : omega ≤ omega')
    (hocc : OccursOn A K omega) : OccursOn A K omega' := by
  classical
  intro z hz
  let z' : ConfigSpace E := fun e => if e ∈ K then omega e else z e
  have hz'A : z' ∈ A := hocc z' (by
    intro e he
    simp [z', he])
  apply hA (b := z) _ hz'A
  intro e
  by_cases he : e ∈ K
  · simp only [z', if_pos he]
    rw [hz e he]
    exact homega e
  · simp only [z', if_neg he]
    exact le_rfl


theorem ibk_disjointOccurrence_isIncreasing {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    IsIncreasing (disjointOccurrence A B) := by
  intro omega omega' homega
  rintro ⟨K, L, hKL, hAK, hBL⟩
  exact ⟨K, L, hKL, ibk_occursOn_mono_config hA homega hAK,
    ibk_occursOn_mono_config hB homega hBL⟩




theorem ibk_occursOn_inter_finite {A : Set (ConfigSpace E)} {F : Finset E}
    {K : Set E} {omega omega' : ConfigSpace E}
    (hA : DependsOn A (F : Set E)) (hocc : OccursOn A K omega)
    (hagree : agreeOn (F : Set E) omega omega') :
    OccursOn A (K ∩ (F : Set E)) omega' := by
  intro z hz
  let z' : ConfigSpace E := fun e => if he : e ∈ F then z e else omega e
  have hz'mem : z' ∈ A := hocc z' (by
    intro e heK
    by_cases heF : e ∈ F
    · simp only [z', dif_pos heF]
      exact (hz e ⟨heK, heF⟩).trans (hagree e heF)
    · simp only [z', dif_neg heF])
  exact (hA z' z (by
    intro e heF
    have heF' : e ∈ F := heF
    simp [z', heF'])).mp hz'mem



theorem ibk_disjointOccurrence_dependsOn {A B : Set (ConfigSpace E)} {F : Finset E}
    (hA : DependsOn A (F : Set E)) (hB : DependsOn B (F : Set E)) :
    DependsOn (disjointOccurrence A B) (F : Set E) := by
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




theorem ibk_inequality_of_finite_dependsOn {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (F : Finset E)
    (hAdep : DependsOn A (F : Set E)) (hBdep : DependsOn B (F : Set E))
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤
      (bernoulliProductMeasure (E := E) p hp).real A *
        (bernoulliProductMeasure (E := E) p hp).real B := by
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
  set mu := bernoulliProductMeasure (E := E) p hp
  have hQRdep := ibk_disjointOccurrence_dependsOn hQdep hRdep
  calc
    mu.real (disjointOccurrence P (disjointOccurrence Q R)) ≤
        mu.real P * mu.real (disjointOccurrence Q R) :=
      ibk_inequality_of_finite_dependsOn hp F hPdep hQRdep hP
        (ibk_disjointOccurrence_isIncreasing hQ hR)
    _ ≤ mu.real P * (mu.real Q * mu.real R) :=
      mul_le_mul_of_nonneg_left
        (ibk_inequality_of_finite_dependsOn hp F hQdep hRdep hQ hR)
        measureReal_nonneg
    _ = mu.real P * mu.real Q * mu.real R := by ring



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

omit [Countable E] in

theorem ibk_configWeight_nonneg [Fintype E] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (omega : ConfigSpace E) : 0 ≤ configWeight r omega := by
  unfold configWeight
  apply Finset.prod_nonneg
  intro e _
  unfold edgeWeight
  split
  · exact hr0
  · linarith


theorem ibk_pivotalProb_nonneg [Fintype E] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (A : Set (ConfigSpace E)) (e : E) : 0 ≤ pivotalProb r A e := by
  unfold pivotalProb
  apply Finset.sum_nonneg
  intro omega _
  exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (ibk_configWeight_nonneg hr0 hr1 omega)



theorem ibk_measure_mono_parameter {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≤ q) {A : Set (ConfigSpace E)} (F : Finset E)
    (hAdep : DependsOn A (F : Set E)) (hAinc : IsIncreasing A) :
    (bernoulliProductMeasure (E := E) p hp).real A ≤
      (bernoulliProductMeasure (E := E) q hq).real A := by
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
      ibk_pivotalProb_nonneg (le_of_lt hr'.1) (le_of_lt hr'.2) B e
  rw [realProb_cylinder_eq_prob p hp A F
      (ih_indicator_dependsOn_of_event hAdep),
    realProb_cylinder_eq_prob q hq A F
      (ih_indicator_dependsOn_of_event hAdep)]
  exact hmono ⟨p.coe_nonneg, by exact_mod_cast hp⟩
    ⟨q.coe_nonneg, by exact_mod_cast hq⟩ (by exact_mod_cast hpq)

end StatMech
