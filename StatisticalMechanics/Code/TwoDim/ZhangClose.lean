/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































































import Code.TwoDim.ZhangLowerBound

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality












theorem zhg_complUnion_fkg_four {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B C D : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) (hC : IsIncreasing C) (hD : IsIncreasing D)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hCm : MeasurableSet C) (hDm : MeasurableSet D) :
    (1 - μ.real A) * (1 - μ.real B) * (1 - μ.real C) * (1 - μ.real D)
      ≤ 1 - μ.real (A ∪ B ∪ C ∪ D) := by
  have nC : (0 : ℝ) ≤ 1 - μ.real C := by
    have := measureReal_le_one (μ := μ) (s := C); linarith
  have nD : (0 : ℝ) ≤ 1 - μ.real D := by
    have := measureReal_le_one (μ := μ) (s := D); linarith
  have h1 := complUnion_fkg_bound μ hpa hA hB hAm hBm
  have h2 := complUnion_fkg_bound μ hpa (hA.union hB) hC (hAm.union hBm) hCm
  have h3 := complUnion_fkg_bound μ hpa ((hA.union hB).union hC) hD
    ((hAm.union hBm).union hCm) hDm
  calc (1 - μ.real A) * (1 - μ.real B) * (1 - μ.real C) * (1 - μ.real D)
      ≤ (1 - μ.real (A ∪ B)) * (1 - μ.real C) * (1 - μ.real D) := by
        apply mul_le_mul_of_nonneg_right _ nD
        exact mul_le_mul_of_nonneg_right h1 nC
    _ ≤ (1 - μ.real (A ∪ B ∪ C)) * (1 - μ.real D) := mul_le_mul_of_nonneg_right h2 nD
    _ ≤ 1 - μ.real (A ∪ B ∪ C ∪ D) := h3














theorem zhg_sqrt_trick_four {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B C D : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) (hC : IsIncreasing C) (hD : IsIncreasing D)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hCm : MeasurableSet C) (hDm : MeasurableSet D)
    (hAB : μ.real A = μ.real B) (hAC : μ.real A = μ.real C) (hAD : μ.real A = μ.real D) :
    1 - (1 - μ.real (A ∪ B ∪ C ∪ D)) ^ ((1 : ℝ) / 4) ≤ μ.real A := by
  have nA : (0 : ℝ) ≤ 1 - μ.real A := by
    have := measureReal_le_one (μ := μ) (s := A); linarith
  
  have hprod := zhg_complUnion_fkg_four μ hpa hA hB hC hD hAm hBm hCm hDm
  have hpow : (1 - μ.real A) ^ 4 ≤ 1 - μ.real (A ∪ B ∪ C ∪ D) := by
    have hrw : (1 - μ.real A) * (1 - μ.real B) * (1 - μ.real C) * (1 - μ.real D)
        = (1 - μ.real A) ^ 4 := by rw [← hAB, ← hAC, ← hAD]; ring
    linarith [hrw ▸ hprod]
  
  set s := μ.real (A ∪ B ∪ C ∪ D) with hs
  have key : (1 - μ.real A) ≤ (1 - s) ^ ((1 : ℝ) / 4) := by
    have hmono : ((1 - μ.real A) ^ 4) ^ ((1 : ℝ) / 4) ≤ (1 - s) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hpow (by norm_num)
    have ereduce : ((1 - μ.real A) ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = 1 - μ.real A := by
      rw [← Real.rpow_natCast (1 - μ.real A) 4, ← Real.rpow_mul nA]
      norm_num
    rwa [ereduce] at hmono
  linarith










theorem zhg_oneSubRpow_tendsto_one {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 1)) :
    Tendsto (fun n => 1 - (1 - u n) ^ ((1 : ℝ) / 4)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => (1 : ℝ) - u n) atTop (𝓝 0) := by
    have := hu.const_sub (1 : ℝ); simpa using this
  have h2 : Tendsto (fun n => (1 - u n) ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := by
    have hca : ContinuousAt (fun x : ℝ => x ^ ((1 : ℝ) / 4)) 0 :=
      Real.continuousAt_rpow_const 0 ((1 : ℝ) / 4) (by right; norm_num)
    have h0 : (0 : ℝ) ^ ((1 : ℝ) / 4) = 0 := by rw [Real.zero_rpow]; norm_num
    have hc : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 4)) (𝓝 0) (𝓝 0) := by
      have := hca.tendsto; rw [h0] at this; exact this
    exact hc.comp h1
  have := h2.const_sub (1 : ℝ); simpa using this







theorem zhg_side_tendsto_one {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {S₀ S₁ S₂ S₃ : ℕ → Set (ConfigSpace E)}
    (h0inc : ∀ n, IsIncreasing (S₀ n)) (h1inc : ∀ n, IsIncreasing (S₁ n))
    (h2inc : ∀ n, IsIncreasing (S₂ n)) (h3inc : ∀ n, IsIncreasing (S₃ n))
    (h0m : ∀ n, MeasurableSet (S₀ n)) (h1m : ∀ n, MeasurableSet (S₁ n))
    (h2m : ∀ n, MeasurableSet (S₂ n)) (h3m : ∀ n, MeasurableSet (S₃ n))
    (hsym1 : ∀ n, μ.real (S₀ n) = μ.real (S₁ n))
    (hsym2 : ∀ n, μ.real (S₀ n) = μ.real (S₂ n))
    (hsym3 : ∀ n, μ.real (S₀ n) = μ.real (S₃ n))
    (hunion : Tendsto (fun n => μ.real (S₀ n ∪ S₁ n ∪ S₂ n ∪ S₃ n)) atTop (𝓝 1)) :
    Tendsto (fun n => μ.real (S₀ n)) atTop (𝓝 1) := by
  have hlb : ∀ n, 1 - (1 - μ.real (S₀ n ∪ S₁ n ∪ S₂ n ∪ S₃ n)) ^ ((1 : ℝ) / 4)
      ≤ μ.real (S₀ n) := fun n =>
    zhg_sqrt_trick_four μ hpa (h0inc n) (h1inc n) (h2inc n) (h3inc n)
      (h0m n) (h1m n) (h2m n) (h3m n) (hsym1 n) (hsym2 n) (hsym3 n)
  have hub : ∀ n, μ.real (S₀ n) ≤ 1 := fun _ => measureReal_le_one
  have hlbtends : Tendsto
      (fun n => 1 - (1 - μ.real (S₀ n ∪ S₁ n ∪ S₂ n ∪ S₃ n)) ^ ((1 : ℝ) / 4))
      atTop (𝓝 1) := zhg_oneSubRpow_tendsto_one hunion
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlbtends tendsto_const_nhds hlb hub





theorem zhg_inter_tendsto_one {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {L R : ℕ → Set (ConfigSpace E)}
    (hLinc : ∀ n, IsIncreasing (L n)) (hRinc : ∀ n, IsIncreasing (R n))
    (hL : Tendsto (fun n => μ.real (L n)) atTop (𝓝 1))
    (hR : Tendsto (fun n => μ.real (R n)) atTop (𝓝 1)) :
    Tendsto (fun n => μ.real (L n ∩ R n)) atTop (𝓝 1) := by
  have lb : ∀ n, μ.real (L n) * μ.real (R n) ≤ μ.real (L n ∩ R n) :=
    fun n => hpa (L n) (R n) (hLinc n) (hRinc n)
  have ub : ∀ n, μ.real (L n ∩ R n) ≤ 1 := fun _ => measureReal_le_one
  have hprod : Tendsto (fun n => μ.real (L n) * μ.real (R n)) atTop (𝓝 1) := by
    have := hL.mul hR; simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hprod tendsto_const_nhds lb ub







theorem zhg_union_tendsto_one_of_merge {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ]
    {A B Err Cap : ℕ → Set (ConfigSpace E)}
    (hsub : ∀ n, Cap n ⊆ (A n ∪ B n) ∪ Err n)
    (hcap : Tendsto (fun n => μ.real (Cap n)) atTop (𝓝 1))
    (herr : Tendsto (fun n => μ.real (Err n)) atTop (𝓝 0)) :
    Tendsto (fun n => μ.real (A n ∪ B n)) atTop (𝓝 1) := by
  have lb : ∀ n, μ.real (Cap n) - μ.real (Err n) ≤ μ.real (A n ∪ B n) := by
    intro n
    have hmono : μ.real (Cap n) ≤ μ.real ((A n ∪ B n) ∪ Err n) :=
      measureReal_mono (hsub n) (measure_ne_top _ _)
    have hunionle : μ.real ((A n ∪ B n) ∪ Err n)
        ≤ μ.real (A n ∪ B n) + μ.real (Err n) := measureReal_union_le _ _
    linarith
  have ub : ∀ n, μ.real (A n ∪ B n) ≤ 1 := fun _ => measureReal_le_one
  have hlb : Tendsto (fun n => μ.real (Cap n) - μ.real (Err n)) atTop (𝓝 1) := by
    have := hcap.sub herr; simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlb tendsto_const_nhds lb ub



























structure ZhangGeometricData {E : Type*} (μ : Measure (ConfigSpace E))
    (A B : ℕ → Set (ConfigSpace E)) where
  S : Fin 4 → ℕ → Set (ConfigSpace E)
  Err : ℕ → Set (ConfigSpace E)
  Sinc : ∀ i n, IsIncreasing (S i n)
  Sm : ∀ i n, MeasurableSet (S i n)
  Ssym : ∀ i n, μ.real (S i n) = μ.real (S 0 n)
  errTendsto : Tendsto (fun n => μ.real (Err n)) atTop (𝓝 0)
  unionTendsto :
    Tendsto (fun n => μ.real (S 0 n ∪ S 1 n ∪ S 2 n ∪ S 3 n)) atTop (𝓝 1)
  merge : ∀ n, S 0 n ∩ S 1 n ⊆ (A n ∪ B n) ∪ Err n









def zhg_geometricData_satisfiable {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] :
    ZhangGeometricData μ (fun _ => (univ : Set (ConfigSpace E))) (fun _ => univ) where
  S := fun _ _ => univ
  Err := fun _ => ∅
  Sinc := fun _ _ => isUpperSet_univ
  Sm := fun _ _ => MeasurableSet.univ
  Ssym := fun _ _ => rfl
  errTendsto := by simp [measureReal_empty]
  unionTendsto := by simp only [Set.union_self, probReal_univ]; exact tendsto_const_nhds
  merge := fun _ => by simp






















theorem zhg_union_of_geometricData {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {A B : ℕ → Set (ConfigSpace E)} (hgeo : ZhangGeometricData μ A B) :
    Tendsto (fun n => μ.real (A n ∪ B n)) atTop (𝓝 1) := by
  
  set S₀ := hgeo.S 0 with hS0
  set S₁ := hgeo.S 1 with hS1
  set S₂ := hgeo.S 2 with hS2
  set S₃ := hgeo.S 3 with hS3
  
  have hsideL : Tendsto (fun n => μ.real (S₀ n)) atTop (𝓝 1) :=
    zhg_side_tendsto_one μ hpa (hgeo.Sinc 0) (hgeo.Sinc 1) (hgeo.Sinc 2) (hgeo.Sinc 3)
      (hgeo.Sm 0) (hgeo.Sm 1) (hgeo.Sm 2) (hgeo.Sm 3)
      (fun n => (hgeo.Ssym 1 n).symm) (fun n => (hgeo.Ssym 2 n).symm)
      (fun n => (hgeo.Ssym 3 n).symm) hgeo.unionTendsto
  
  
  have hsideR : Tendsto (fun n => μ.real (S₁ n)) atTop (𝓝 1) := by
    have hrw : (fun n => μ.real (S₁ n)) = fun n => μ.real (S₀ n) :=
      funext fun n => (hgeo.Ssym 1 n)
    rw [hrw]; exact hsideL
  
  have hinter : Tendsto (fun n => μ.real (S₀ n ∩ S₁ n)) atTop (𝓝 1) :=
    zhg_inter_tendsto_one μ hpa (hgeo.Sinc 0) (hgeo.Sinc 1) hsideL hsideR
  
  exact zhg_union_tendsto_one_of_merge μ (A := A) (B := B) (Err := hgeo.Err)
    (Cap := fun n => S₀ n ∩ S₁ n) hgeo.merge hinter hgeo.errTendsto















theorem zhg_zhangUnion
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated halfMeasure)
    (hgeo : ZhangGeometricData halfMeasure A B) :
    BoxCrossingProperty halfMeasure 2 →
      0 < halfMeasure.real (percolationEvent 2) →
      Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1) :=
  fun _ _ => zhg_union_of_geometricData halfMeasure hpa hgeo




























theorem zhg_corLowerBound
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated halfMeasure)
    (hAinc : ∀ n, IsIncreasing (A n)) (hBinc : ∀ n, IsIncreasing (B n))
    (hBm : ∀ n, MeasurableSet (B n))
    (hHm : ∀ n, MeasurableSet (A n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (A n)ᶜ = (R ∘ dualConfig) ⁻¹' (A n))
    (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
    (hgeo : ZhangGeometricData halfMeasure A B) :
    BoxCrossingProperty halfMeasure 2 →
      percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  kzh_corLowerBound hpa hAinc hBinc hBm hHm hRmeas hRpres hdich heq
    (zhg_zhangUnion hpa hgeo)

end TwoDim

end StatMech
