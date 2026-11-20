/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheEquations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexBetheIntegratingFactor (c x : ℝ) : ℝ :=
  Real.cos x - sixVertexDelta c

theorem sixVertexBetheIntegratingFactor_pos {c : ℝ} (hc : 2 < c) (x : ℝ) :
    0 < sixVertexBetheIntegratingFactor c x := by
  have hdelta := sixVertexDelta_lt_neg_one hc
  have hcos := Real.neg_one_le_cos x
  unfold sixVertexBetheIntegratingFactor
  linarith



def sixVertexThetaDerivativeDenominator (c x y : ℝ) : ℝ :=
  sixVertexThetaDenominator c x y ^ 2 +
    (Real.sin x - Real.sin y) ^ 2

theorem sixVertexThetaDerivativeDenominator_swap (c x y : ℝ) :
    sixVertexThetaDerivativeDenominator c y x =
      sixVertexThetaDerivativeDenominator c x y := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  ring

theorem sixVertexThetaDerivativeDenominator_pos {c : ℝ} (hc : 2 < c)
    (x y : ℝ) : 0 < sixVertexThetaDerivativeDenominator c x y := by
  unfold sixVertexThetaDerivativeDenominator
  have hden := sixVertexThetaDenominator_pos hc x y
  positivity


theorem hasDerivAt_sixVertexTheta_right {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    HasDerivAt (fun t => sixVertexTheta c x t)
      (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y) y := by
  have hleft := (hasDerivAt_sixVertexTheta_left hc y x).neg
  have hfun : (-(fun t => sixVertexTheta c t x)) =
      fun t => sixVertexTheta c x t := by
    funext t
    exact (sixVertexTheta_antisymm c t x).symm
  rw [hfun] at hleft
  convert hleft using 1
  unfold sixVertexBetheIntegratingFactor
    sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  ring


def sixVertexThetaFDeriv (c x y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
        sixVertexThetaDerivativeDenominator c x y) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y)

theorem hasFDerivAt_sixVertexTheta {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    HasFDerivAt (fun xy : ℝ × ℝ => sixVertexTheta c xy.1 xy.2)
      (sixVertexThetaFDeriv c x y) (x, y) := by
  let fx : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let fy : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hx : HasFDerivAt (fun xy : ℝ × ℝ => xy.1) fx (x, y) := fx.hasFDerivAt
  have hy : HasFDerivAt (fun xy : ℝ × ℝ => xy.2) fy (x, y) := fy.hasFDerivAt
  have hsinx : HasFDerivAt (fun xy : ℝ × ℝ => Real.sin xy.1)
      ((Real.cos x) • fx) (x, y) := by
    simpa using (Real.hasDerivAt_sin x).comp_hasFDerivAt (x, y) hx
  have hsiny : HasFDerivAt (fun xy : ℝ × ℝ => Real.sin xy.2)
      ((Real.cos y) • fy) (x, y) := by
    simpa using (Real.hasDerivAt_sin y).comp_hasFDerivAt (x, y) hy
  have hcosx : HasFDerivAt (fun xy : ℝ × ℝ => Real.cos xy.1)
      ((-Real.sin x) • fx) (x, y) := by
    have h := (Real.hasDerivAt_cos x).comp_hasFDerivAt (x, y) hx
    convert h using 1
  have hcosy : HasFDerivAt (fun xy : ℝ × ℝ => Real.cos xy.2)
      ((-Real.sin y) • fy) (x, y) := by
    have h := (Real.hasDerivAt_cos y).comp_hasFDerivAt (x, y) hy
    convert h using 1
  have hnum := hsinx.sub hsiny
  have hden := (hcosx.add hcosy).sub_const (2 * sixVertexDelta c)
  have hden0 : sixVertexThetaDenominator c x y ≠ 0 :=
    (sixVertexThetaDenominator_pos hc x y).ne'
  have hinv := (hasFDerivAt_inv hden0).comp (x, y) hden
  have hratio := hnum.mul hinv
  have harctan := hratio.arctan
  have htheta := (hy.sub hx).add (harctan.const_mul 2)
  let g : ℝ × ℝ → ℝ := fun xy => sixVertexTheta c xy.1 xy.2
  have hgdiff : DifferentiableAt ℝ g (x, y) := by
    dsimp [g, sixVertexTheta]
    simpa only [div_eq_mul_inv] using htheta.differentiableAt
  have hg := hgdiff.hasFDerivAt
  have hlineLeft : HasDerivAt (fun t => g (t, y))
      (fderiv ℝ g (x, y) (1, 0)) x := by
    have hpath := (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    simpa [Function.comp_def] using hg.comp_hasDerivAt x hpath
  have hlineRight : HasDerivAt (fun t => g (x, t))
      (fderiv ℝ g (x, y) (0, 1)) y := by
    have hpath := (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
    simpa [Function.comp_def] using hg.comp_hasDerivAt y hpath
  have hleft : fderiv ℝ g (x, y) (1, 0) =
      4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
        sixVertexThetaDerivativeDenominator c x y := by
    apply hlineLeft.unique
    simpa [g, sixVertexBetheIntegratingFactor,
      sixVertexThetaDerivativeDenominator] using
        hasDerivAt_sixVertexTheta_left hc x y
  have hright : fderiv ℝ g (x, y) (0, 1) =
      -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y := by
    apply hlineRight.unique
    simpa [g] using hasDerivAt_sixVertexTheta_right hc x y
  have hmap : fderiv ℝ g (x, y) = sixVertexThetaFDeriv c x y := by
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    have hdecomp : (u, v) = u • (1, 0) + v • (0, 1) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul, map_smul, hleft, hright]
    simp [sixVertexThetaFDeriv]
  rw [← hmap]
  exact hg



def sixVertexBetheResidual (c : ℝ) (N n : ℕ)
    (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  (N : ℝ) * p j + ∑ k, sixVertexTheta c (p j) (p k) -
    2 * Real.pi * sixVertexCentralQuantumNumber j

theorem sixVertexBetheResidual_eq_zero_iff
    (c : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    (∀ j, sixVertexBetheResidual c N n p j = 0) ↔
      SixVertexSatisfiesBetheEquations c N n p := by
  constructor <;> intro h j
  · have hj := h j
    unfold sixVertexBetheResidual at hj
    linarith
  · unfold sixVertexBetheResidual
    linarith [h j]



def sixVertexNormalizedBetheResidual (c : ℝ) (N n : ℕ)
    (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  sixVertexBetheResidual c N n p j /
    sixVertexBetheIntegratingFactor c (p j)

theorem sixVertexNormalizedBetheResidual_eq_zero_iff
    {c : ℝ} (hc : 2 < c) (N n : ℕ) (p : Fin n → ℝ) :
    (∀ j, sixVertexNormalizedBetheResidual c N n p j = 0) ↔
      SixVertexSatisfiesBetheEquations c N n p := by
  rw [← sixVertexBetheResidual_eq_zero_iff]
  apply forall_congr'
  intro j
  unfold sixVertexNormalizedBetheResidual
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact False.elim ((sixVertexBetheIntegratingFactor_pos hc (p j)).ne' h)
  · intro h
    simp [h]



theorem sixVertexTheta_mixed_integratingFactor {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y) /
        sixVertexBetheIntegratingFactor c x =
      (-4 * sixVertexDelta c) /
        sixVertexThetaDerivativeDenominator c x y := by
  field_simp [(sixVertexBetheIntegratingFactor_pos hc x).ne']

theorem sixVertexTheta_mixed_integratingFactor_symm
    {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y) /
        sixVertexBetheIntegratingFactor c x =
      (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c y x) /
        sixVertexBetheIntegratingFactor c y := by
  rw [sixVertexTheta_mixed_integratingFactor hc,
    sixVertexTheta_mixed_integratingFactor hc,
    sixVertexThetaDerivativeDenominator_swap]



def sixVertexNormalizedTheta (c x y : ℝ) : ℝ :=
  sixVertexTheta c x y / sixVertexBetheIntegratingFactor c x

theorem hasFDerivAt_sixVertexNormalizedTheta {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    HasFDerivAt (fun xy : ℝ × ℝ =>
      sixVertexNormalizedTheta c xy.1 xy.2)
      (fderiv ℝ (fun xy : ℝ × ℝ =>
        sixVertexNormalizedTheta c xy.1 xy.2) (x, y)) (x, y) := by
  apply DifferentiableAt.hasFDerivAt
  unfold sixVertexNormalizedTheta
  have hx : DifferentiableAt ℝ (fun xy : ℝ × ℝ => xy.1) (x, y) := by fun_prop
  have hden : DifferentiableAt ℝ
      (fun xy : ℝ × ℝ => sixVertexBetheIntegratingFactor c xy.1) (x, y) := by
    unfold sixVertexBetheIntegratingFactor
    exact ((Real.hasDerivAt_cos x).comp_hasFDerivAt (x, y)
      hx.hasFDerivAt).differentiableAt.sub_const _
  have hinv := (hasFDerivAt_inv
    (sixVertexBetheIntegratingFactor_pos hc x).ne').comp
      (x, y) hden.hasFDerivAt
  simpa only [div_eq_mul_inv] using
    (hasFDerivAt_sixVertexTheta hc x y).differentiableAt.mul
      hinv.differentiableAt

@[fun_prop] theorem differentiable_sixVertexNormalizedTheta
    {c : ℝ} (hc : 2 < c) :
    Differentiable ℝ (fun xy : ℝ × ℝ =>
      sixVertexNormalizedTheta c xy.1 xy.2) := by
  intro xy
  exact (hasFDerivAt_sixVertexNormalizedTheta hc xy.1 xy.2).differentiableAt

theorem hasDerivAt_sixVertexNormalizedTheta_right
    {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    HasDerivAt (fun t => sixVertexNormalizedTheta c x t)
      ((-4 * sixVertexDelta c) /
        sixVertexThetaDerivativeDenominator c x y) y := by
  unfold sixVertexNormalizedTheta
  have h := (hasDerivAt_sixVertexTheta_right hc x y).div_const
    (sixVertexBetheIntegratingFactor c x)
  convert h using 1
  exact (sixVertexTheta_mixed_integratingFactor hc x y).symm


def sixVertexBethePairOneForm (c : ℝ) (xy : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (sixVertexNormalizedTheta c xy.1 xy.2) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (sixVertexNormalizedTheta c xy.2 xy.1)

theorem differentiable_sixVertexBethePairOneForm
    {c : ℝ} (hc : 2 < c) :
    Differentiable ℝ (sixVertexBethePairOneForm c) := by
  unfold sixVertexBethePairOneForm
  fun_prop

theorem fderiv_sixVertexBethePairOneForm_symmetric
    {c : ℝ} (hc : 2 < c) (xy u v : ℝ × ℝ) :
    fderiv ℝ (sixVertexBethePairOneForm c) xy u v =
      fderiv ℝ (sixVertexBethePairOneForm c) xy v u := by
  let ω := sixVertexBethePairOneForm c
  have hω : DifferentiableAt ℝ ω xy :=
    differentiable_sixVertexBethePairOneForm hc xy
  have hcross₁ : fderiv ℝ ω xy (1, 0) (0, 1) =
      (-4 * sixVertexDelta c) /
        sixVertexThetaDerivativeDenominator c xy.1 xy.2 := by
    have hpath := (hasDerivAt_id xy.1).prodMk
      (hasDerivAt_const xy.1 xy.2)
    have hcomp := hω.hasFDerivAt.comp_hasDerivAt xy.1 hpath
    have heval := (ContinuousLinearMap.apply ℝ ℝ (0, 1)).hasFDerivAt.comp
      xy hω.hasFDerivAt
    have hline : HasDerivAt
        (fun t => ω (t, xy.2) (0, 1))
        (fderiv ℝ ω xy (1, 0) (0, 1)) xy.1 := by
      exact heval.comp_hasDerivAt xy.1 hpath
    apply hline.unique
    convert hasDerivAt_sixVertexNormalizedTheta_right hc xy.2 xy.1 using 1
    · funext t
      simp [ω, sixVertexBethePairOneForm]
    · rw [sixVertexThetaDerivativeDenominator_swap]
  have hcross₂ : fderiv ℝ ω xy (0, 1) (1, 0) =
      (-4 * sixVertexDelta c) /
        sixVertexThetaDerivativeDenominator c xy.1 xy.2 := by
    have hpath := (hasDerivAt_const xy.2 xy.1).prodMk
      (hasDerivAt_id xy.2)
    have heval := (ContinuousLinearMap.apply ℝ ℝ (1, 0)).hasFDerivAt.comp
      xy hω.hasFDerivAt
    have hline : HasDerivAt
        (fun t => ω (xy.1, t) (1, 0))
        (fderiv ℝ ω xy (0, 1) (1, 0)) xy.2 := by
      exact heval.comp_hasDerivAt xy.2 hpath
    apply hline.unique
    simpa [ω, sixVertexBethePairOneForm] using
      hasDerivAt_sixVertexNormalizedTheta_right hc xy.1 xy.2
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hu : (u₁, u₂) = u₁ • (1, 0) + u₂ • (0, 1) := by ext <;> simp
  have hv : (v₁, v₂) = v₁ • (1, 0) + v₂ • (0, 1) := by ext <;> simp
  rw [hu, hv]
  simp only [map_add, map_smul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [hcross₁, hcross₂]
  ring


theorem exists_sixVertexBethePairPotential {c : ℝ} (hc : 2 < c) :
    ∃ H : (ℝ × ℝ) → ℝ, ∀ xy,
      HasFDerivAt H (sixVertexBethePairOneForm c xy) xy := by
  obtain ⟨H, hH⟩ := Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric
    (ω := sixVertexBethePairOneForm c)
    (convex_univ : Convex ℝ (Set.univ : Set (ℝ × ℝ))) isOpen_univ
    (differentiable_sixVertexBethePairOneForm hc).differentiableOn
    (fun xy _ u v => fderiv_sixVertexBethePairOneForm_symmetric hc xy u v)
  exact ⟨H, fun xy => hH xy (Set.mem_univ xy)⟩


def sixVertexBethePairPotential {c : ℝ} (hc : 2 < c) :
    (ℝ × ℝ) → ℝ :=
  Classical.choose (exists_sixVertexBethePairPotential hc)

theorem hasFDerivAt_sixVertexBethePairPotential
    {c : ℝ} (hc : 2 < c) (xy : ℝ × ℝ) :
    HasFDerivAt (sixVertexBethePairPotential hc)
      (sixVertexBethePairOneForm c xy) xy :=
  Classical.choose_spec (exists_sixVertexBethePairPotential hc) xy


def sixVertexBetheOneBodyCoefficient
    (c : ℝ) (N : ℕ) (I x : ℝ) : ℝ :=
  ((N : ℝ) * x - 2 * Real.pi * I) /
    sixVertexBetheIntegratingFactor c x

theorem continuous_sixVertexBetheOneBodyCoefficient
    {c : ℝ} (hc : 2 < c) (N : ℕ) (I : ℝ) :
    Continuous (sixVertexBetheOneBodyCoefficient c N I) := by
  unfold sixVertexBetheOneBodyCoefficient sixVertexBetheIntegratingFactor
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact (sixVertexBetheIntegratingFactor_pos hc x).ne'


def sixVertexBetheOneBodyPotential
    (c : ℝ) (N : ℕ) (I x : ℝ) : ℝ :=
  ∫ t in 0..x, sixVertexBetheOneBodyCoefficient c N I t

theorem hasDerivAt_sixVertexBetheOneBodyPotential
    {c : ℝ} (hc : 2 < c) (N : ℕ) (I x : ℝ) :
    HasDerivAt (sixVertexBetheOneBodyPotential c N I)
      (sixVertexBetheOneBodyCoefficient c N I x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuous_sixVertexBetheOneBodyCoefficient hc N I).intervalIntegrable 0 x
  · exact Continuous.stronglyMeasurableAtFilter
      (continuous_sixVertexBetheOneBodyCoefficient hc N I)
      MeasureTheory.volume (𝓝 x)
  · exact (continuous_sixVertexBetheOneBodyCoefficient hc N I).continuousAt



def sixVertexBethePotential {c : ℝ} (hc : 2 < c) (N n : ℕ)
    (p : Fin n → ℝ) : ℝ :=
  (∑ j, sixVertexBetheOneBodyPotential c N
      (sixVertexCentralQuantumNumber j) (p j)) +
    ∑ j, ∑ k ∈ Finset.Ioi j,
      sixVertexBethePairPotential hc (p j, p k)



def sixVertexBetheOneForm {c : ℝ} (_hc : 2 < c) (N n : ℕ)
    (p : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (∑ j, (sixVertexBetheOneBodyCoefficient c N
      (sixVertexCentralQuantumNumber j) (p j)) •
        (ContinuousLinearMap.proj j)) +
    ∑ j, ∑ k ∈ Finset.Ioi j,
      (sixVertexBethePairOneForm c (p j, p k)).comp
        ((ContinuousLinearMap.proj j).prod
          (ContinuousLinearMap.proj k))

theorem hasFDerivAt_sixVertexBethePotential
    {c : ℝ} (hc : 2 < c) (N n : ℕ) (p : Fin n → ℝ) :
    HasFDerivAt (sixVertexBethePotential hc N n)
      (sixVertexBetheOneForm hc N n p) p := by
  unfold sixVertexBethePotential sixVertexBetheOneForm
  apply HasFDerivAt.add
  · apply HasFDerivAt.fun_sum
    intro j _
    have hj := hasFDerivAt_apply (𝕜 := ℝ) j p
    have h := (hasDerivAt_sixVertexBetheOneBodyPotential hc N
      (sixVertexCentralQuantumNumber j) (p j)).comp_hasFDerivAt p hj
    simpa using h
  · apply HasFDerivAt.fun_sum
    intro j _
    apply HasFDerivAt.fun_sum
    intro k hk
    have hj := hasFDerivAt_apply (𝕜 := ℝ) j p
    have hk' := hasFDerivAt_apply (𝕜 := ℝ) k p
    exact (hasFDerivAt_sixVertexBethePairPotential hc (p j, p k)).comp p
      (hj.prodMk hk')

private theorem sum_Iio_swap {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ j, ∑ k ∈ Finset.Iio j, F j k) =
      ∑ j, ∑ k ∈ Finset.Ioi j, F k j := by
  classical
  have hIio (j : Fin n) : Finset.Iio j =
      Finset.univ.filter fun k => k < j := by
    ext k
    simp
  have hIoi (j : Fin n) : Finset.Ioi j =
      Finset.univ.filter fun k => j < k := by
    ext k
    simp
  calc
    (∑ j, ∑ k ∈ Finset.Iio j, F j k) =
        ∑ j, ∑ k, if k < j then F j k else 0 := by
      simp_rw [hIio, Finset.sum_filter]
    _ = ∑ k, ∑ j, if k < j then F j k else 0 := Finset.sum_comm
    _ = ∑ k, ∑ j ∈ Finset.Ioi k, F j k := by
      simp_rw [hIoi, Finset.sum_filter]

private theorem sum_unorderedPair_expand {n : ℕ}
    (H : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ j, ∑ k ∈ Finset.Ioi j,
      (H j k * v j + H k j * v k)) =
      ∑ j, (∑ k ∈ Finset.univ.erase j, H j k) * v j := by
  classical
  have herase (j : Fin n) : Finset.univ.erase j =
      Finset.Iio j ∪ Finset.Ioi j := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi]
    omega
  have hdisj (j : Fin n) : Disjoint (Finset.Iio j) (Finset.Ioi j) := by
    rw [Finset.disjoint_left]
    intro k hkj hjk
    simp only [Finset.mem_Iio] at hkj
    simp only [Finset.mem_Ioi] at hjk
    omega
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul]
  have hswap := sum_Iio_swap (fun j k => H j k * v j)
  calc
    (∑ x, (∑ j ∈ Finset.Ioi x, H x j) * v x) +
          ∑ x, ∑ j ∈ Finset.Ioi x, H j x * v j =
        (∑ x, (∑ j ∈ Finset.Ioi x, H x j) * v x) +
          ∑ x, ∑ j ∈ Finset.Iio x, H x j * v x := by rw [hswap]
    _ = ∑ j, ((∑ k ∈ Finset.Iio j, H j k) +
          ∑ k ∈ Finset.Ioi j, H j k) * v j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [herase, Finset.sum_union (hdisj j)]

private theorem sum_clm_apply {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → E →L[ℝ] ℝ) (v : E) :
    (∑ i, f i) v = ∑ i, f i v := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

private theorem sum_clm_apply_finset {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (f : ι → E →L[ℝ] ℝ) (v : E) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

theorem sixVertexBetheOneForm_apply
    {c : ℝ} (hc : 2 < c) (N n : ℕ)
    (p v : Fin n → ℝ) :
    sixVertexBetheOneForm hc N n p v =
      ∑ j, sixVertexNormalizedBetheResidual c N n p j * v j := by
  classical
  let H : Fin n → Fin n → ℝ := fun j k =>
    sixVertexNormalizedTheta c (p j) (p k)
  have hpair := sum_unorderedPair_expand H v
  unfold sixVertexBetheOneForm
  rw [ContinuousLinearMap.add_apply,
    sum_clm_apply (fun j =>
      sixVertexBetheOneBodyCoefficient c N
        (sixVertexCentralQuantumNumber j) (p j) •
          ContinuousLinearMap.proj j) v,
    sum_clm_apply (fun j => ∑ k ∈ Finset.Ioi j,
      (sixVertexBethePairOneForm c (p j, p k)).comp
        ((ContinuousLinearMap.proj j).prod
          (ContinuousLinearMap.proj k))) v]
  simp_rw [sum_clm_apply_finset]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply,
    sixVertexBethePairOneForm, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply]
  simp only [smul_eq_mul]
  simp
  have hpair' :
      (∑ j, ∑ k ∈ Finset.Ioi j, (v j * H j k + v k * H k j)) =
        ∑ j, (∑ k ∈ Finset.univ.erase j, H j k) * v j := by
    simpa [mul_comm] using hpair
  rw [hpair', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hself : H j j = 0 := by
    simp [H, sixVertexNormalizedTheta]
  have hsum : (∑ k, H j k) = ∑ k ∈ Finset.univ.erase j, H j k := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hself, add_zero]
  rw [← hsum]
  simp only [H]
  unfold sixVertexNormalizedBetheResidual sixVertexBetheResidual
    sixVertexBetheOneBodyCoefficient sixVertexNormalizedTheta
  rw [← Finset.sum_div]
  ring

theorem sixVertexBetheResidual_eq_updateSub
    {c : ℝ} {N n : ℕ} (hN : 0 < N) (p : Fin n → ℝ) (j : Fin n) :
    sixVertexBetheResidual c N n p j =
      (N : ℝ) * (p j - sixVertexBetheUpdate c N n p j) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold sixVertexBetheResidual sixVertexBetheUpdate
  field_simp [hN0]
  ring

theorem sixVertexBetheOneForm_updateSub
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hN : 0 < N)
    (p : Fin n → ℝ) :
    sixVertexBetheOneForm hc N n p
        (sixVertexBetheUpdate c N n p - p) =
      -(N : ℝ) * ∑ j,
        (sixVertexBetheUpdate c N n p j - p j) ^ 2 /
          sixVertexBetheIntegratingFactor c (p j) := by
  rw [sixVertexBetheOneForm_apply]
  calc
    (∑ j, sixVertexNormalizedBetheResidual c N n p j *
        (sixVertexBetheUpdate c N n p - p) j) =
        ∑ j, -(N : ℝ) *
          ((sixVertexBetheUpdate c N n p j - p j) ^ 2 /
            sixVertexBetheIntegratingFactor c (p j)) := by
      apply Finset.sum_congr rfl
      intro j _
      change sixVertexNormalizedBetheResidual c N n p j *
        (sixVertexBetheUpdate c N n p j - p j) = _
      unfold sixVertexNormalizedBetheResidual
      rw [sixVertexBetheResidual_eq_updateSub hN]
      ring
    _ = _ := by rw [Finset.mul_sum]

theorem sixVertexBetheOneForm_updateSub_neg
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hN : 0 < N)
    (p : Fin n → ℝ)
    (hne : sixVertexBetheUpdate c N n p ≠ p) :
    sixVertexBetheOneForm hc N n p
        (sixVertexBetheUpdate c N n p - p) < 0 := by
  have hex : ∃ j, sixVertexBetheUpdate c N n p j - p j ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    funext j
    linarith [h j]
  have hnonneg (j : Fin n) :
      0 ≤ (sixVertexBetheUpdate c N n p j - p j) ^ 2 /
        sixVertexBetheIntegratingFactor c (p j) :=
    div_nonneg (sq_nonneg _) (sixVertexBetheIntegratingFactor_pos hc _).le
  have hsum : 0 < ∑ j,
      (sixVertexBetheUpdate c N n p j - p j) ^ 2 /
        sixVertexBetheIntegratingFactor c (p j) := by
    apply Finset.sum_pos'
    · intro j _
      exact hnonneg j
    · obtain ⟨j, hj⟩ := hex
      refine ⟨j, Finset.mem_univ j, ?_⟩
      exact div_pos (sq_pos_of_ne_zero hj)
        (sixVertexBetheIntegratingFactor_pos hc _)
  rw [sixVertexBetheOneForm_updateSub hc hN]
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

theorem continuous_sixVertexBethePotential
    {c : ℝ} (hc : 2 < c) (N n : ℕ) :
    Continuous (sixVertexBethePotential hc N n) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact (hasFDerivAt_sixVertexBethePotential hc N n p).continuousAt




theorem exists_sixVertexBetheUpdate_fixedPoint
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hN : 0 < N)
    (hhalf : 2 * n ≤ N) :
    ∃ p : Fin n → ℝ, SixVertexClosedRootSimplex p ∧
      sixVertexBetheUpdate c N n p = p := by
  let S : Set (Fin n → ℝ) :=
    {p | SixVertexClosedRootSimplex p}
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_sixVertexClosedRootSimplex n).exists_isMinOn
      (sixVertexClosedRootSimplex_nonempty n)
      (continuous_sixVertexBethePotential hc N n).continuousOn
  refine ⟨p, hp, ?_⟩
  by_contra hne
  let q := sixVertexBetheUpdate c N n p
  have hq : q ∈ S := by
    exact sixVertexBetheUpdate_mapsTo_closedRootSimplex hc hhalf hp
  have hdir : q - p ∈ posTangentConeAt S p :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_sixVertexClosedRootSimplex n).segment_subset hp hq)
  have hnonneg :
      0 ≤ sixVertexBetheOneForm hc N n p (q - p) :=
    hmin.localize.hasFDerivWithinAt_nonneg
      (hasFDerivAt_sixVertexBethePotential hc N n p).hasFDerivWithinAt
      hdir
  have hneg : sixVertexBetheOneForm hc N n p (q - p) < 0 := by
    simpa only [q] using sixVertexBetheOneForm_updateSub_neg hc hN p hne
  exact (not_lt_of_ge hnonneg) hneg




theorem exists_sixVertexBetheSolution
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N) :
    ∃ p : Fin n → ℝ, SixVertexOpenRootSimplex p ∧
      SixVertexSatisfiesBetheEquations c N n p := by
  by_cases hNzero : N = 0
  · subst N
    have hnzero : n = 0 := by omega
    subst n
    refine ⟨fun j => Fin.elim0 j, ?_, ?_⟩
    · exact ⟨fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    · exact fun i => Fin.elim0 i
  · have hN : 0 < N := Nat.pos_of_ne_zero hNzero
    obtain ⟨p, hp, hfix⟩ :=
      exists_sixVertexBetheUpdate_fixedPoint hc hN hhalf
    exact ⟨p,
      sixVertexBetheUpdate_fixedPoint_mem_open hc hhalf hp hfix,
      sixVertexBetheUpdate_fixedPoint_is_solution hN hfix⟩


noncomputable def sixVertexChosenBetheSolution
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N) :
    Fin n → ℝ :=
  Classical.choose (exists_sixVertexBetheSolution hc hhalf)

theorem sixVertexChosenBetheSolution_mem_open
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N) :
    SixVertexOpenRootSimplex (sixVertexChosenBetheSolution hc hhalf) :=
  (Classical.choose_spec (exists_sixVertexBetheSolution hc hhalf)).1

theorem sixVertexChosenBetheSolution_is_solution
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N) :
    SixVertexSatisfiesBetheEquations c N n
      (sixVertexChosenBetheSolution hc hhalf) :=
  (Classical.choose_spec (exists_sixVertexBetheSolution hc hhalf)).2



theorem sixVertexBetheSolution_quantumSpacing
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin n → ℝ}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    {i j : Fin n} (hij : i < j) :
    2 * Real.pi *
        (sixVertexCentralQuantumNumber j - sixVertexCentralQuantumNumber i) <
      (N : ℝ) * (p j - p i) := by
  have hpij : p i < p j := hopen.1 hij
  letI : Nonempty (Fin n) := ⟨i⟩
  have hsum :
      (∑ k, sixVertexTheta c (p j) (p k)) <
        ∑ k, sixVertexTheta c (p i) (p k) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro k _
    exact strictAnti_sixVertexTheta_left hc (p k) hpij
  have hi := hsol i
  have hj := hsol j
  linarith



theorem sixVertexBetheSolution_adjacentSpacing
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin (n + 1) → ℝ}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (i : Fin n) :
    2 * Real.pi < (N : ℝ) * (p i.succ - p i.castSucc) := by
  have h := sixVertexBetheSolution_quantumSpacing hc hopen hsol
    (i := i.castSucc) (j := i.succ) (by simp)
  have hI : sixVertexCentralQuantumNumber i.succ -
      sixVertexCentralQuantumNumber i.castSucc = 1 := by
    rw [sixVertexCentralQuantumNumber_eq,
      sixVertexCentralQuantumNumber_eq]
    simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    ring
  simpa [hI] using h

end

end StatMech.FrontierD
