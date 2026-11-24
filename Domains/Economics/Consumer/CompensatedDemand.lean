/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.DotProductGradient
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Data.Matrix.Mul

/-!
# The compensated-demand Jacobian is symmetric and negative semidefinite
(Atlas EC04.T05)

Let `e` be an expenditure function (for a fixed utility target) and `h` a
compensated (Hicksian) demand on an open set `U` of prices, related by Shephard's
lemma: on `U`, the derivative of `e` at `q` is `v ↦ v ⬝ᵥ h q` (`Real.dotL (h q)`).
If `h` is differentiable at `p ∈ U` with derivative `Dh`, then

* the substitution (Slutsky) matrix `S i j = ∂hᵢ/∂pⱼ` is symmetric, because it is
  the second derivative of `e` (symmetry of second derivatives);
* if `e` is concave on `U` (as expenditure functions are), `S` is negative
  semidefinite: `x ⬝ᵥ S x ≤ 0`, because `t ↦ h(p + t v) ⬝ᵥ v` is the derivative of
  the concave function `t ↦ e(p + t v)`, hence antitone.

Shephard's lemma is a hypothesis here (it is proved in the open EC04.T03 work);
concavity of expenditure is EC04.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.CompensatedDemand

open Matrix

/-- The compensated-demand (substitution) matrix `S i j = ∂hᵢ/∂pⱼ`, read off the
derivative `Dh` of the compensated demand. -/
def compensatedJacobian {ι : Type*} [DecidableEq ι] (Dh : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j => Dh (Pi.single j 1) i

/-- The map `x ↦ Real.dotL x` as a continuous linear map, used to differentiate
`q ↦ Real.dotL (h q)`. -/
noncomputable def dotLCLM {ι : Type*} [Fintype ι] :
    (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

/-- `dotLCLM` agrees with `Real.dotL`. -/
theorem dotLCLM_apply {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    dotLCLM x = Real.dotL x := by
  ext v
  simp [dotLCLM, dotProduct, mul_comm, ContinuousLinearMap.smulRight_apply,
    Real.dotL_apply]

/-- **Symmetry of compensated price effects.** Under Shephard's lemma on an open
set of prices, the derivative of compensated demand is a symmetric bilinear
form. -/
theorem dotProduct_compensated_symm {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : IsOpen U) {e : (ι → ℝ) → ℝ} {h : (ι → ℝ) → ι → ℝ} {p : ι → ℝ}
    {Dh : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hp : p ∈ U)
    (hShephard : ∀ q ∈ U, HasFDerivAt e (Real.dotL (h q)) q)
    (hh : HasFDerivAt h Dh p) (v w : ι → ℝ) :
    w ⬝ᵥ Dh v = v ⬝ᵥ Dh w := by
  have h₁ : ∀ᶠ q in nhds p, HasFDerivAt e (Real.dotL (h q)) q := by
    filter_upwards [hU.mem_nhds hp] with q hq using hShephard q hq
  have hfun : (⇑dotLCLM : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ) = fun x => Real.dotL x :=
    funext dotLCLM_apply
  have hdot : HasFDerivAt (fun x : ι → ℝ => Real.dotL x) dotLCLM (h p) := by
    rw [← hfun]
    exact dotLCLM.hasFDerivAt
  have h₂ : HasFDerivAt (fun q : ι → ℝ => Real.dotL (h q)) (dotLCLM.comp Dh) p :=
    hdot.comp p hh
  have hsym := second_derivative_symmetric_of_eventually
    (f' := fun q : ι → ℝ => Real.dotL (h q)) h₁ h₂ v w
  simpa [ContinuousLinearMap.comp_apply, dotLCLM_apply] using hsym

/-- **Negative semidefiniteness of compensated price effects.** Under Shephard's
lemma on an open set of prices where expenditure is concave, `v ⬝ᵥ Dh v ≤ 0`. -/
theorem dotProduct_compensated_self_nonpos {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : IsOpen U) {e : (ι → ℝ) → ℝ} {h : (ι → ℝ) → ι → ℝ} {p : ι → ℝ}
    {Dh : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hp : p ∈ U) (hconc : ConcaveOn ℝ U e)
    (hShephard : ∀ q ∈ U, HasFDerivAt e (Real.dotL (h q)) q)
    (hh : HasFDerivAt h Dh p) (v : ι → ℝ) :
    v ⬝ᵥ Dh v ≤ 0 := by
  obtain ⟨-, hjens⟩ := hconc
  have hcont : ContinuousAt (fun t : ℝ => p + t • v) 0 :=
    ((continuous_id.smul (continuous_const (y := v))).const_add p).continuousAt
  have h0mem : (fun t : ℝ => p + t • v) 0 ∈ U := by simpa using hp
  have hev : ∀ᶠ t in nhds (0 : ℝ), p + t • v ∈ U :=
    Filter.Tendsto.eventually hcont
      (Filter.eventually_of_mem (hU.mem_nhds h0mem) (fun _ h => h))
  rw [Metric.eventually_nhds_iff_ball] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  have hmem : ∀ t ∈ Set.Ioo (-δ) δ, p + t • v ∈ U := by
    intro t ht
    refine hδ t ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨ht.1, ht.2⟩
  have hzero : p + (0 : ℝ) • v = p := by simp
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => p + t • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hg : ∀ t ∈ Set.Ioo (-δ) δ,
      HasDerivAt (fun s : ℝ => e (p + s • v)) (v ⬝ᵥ h (p + t • v)) t := by
    intro t ht
    have hcomp := (hShephard _ (hmem t ht)).comp_hasDerivAt t (hline t)
    rw [Real.dotL_apply] at hcomp
    exact hcomp
  have hgconc : ConcaveOn ℝ (Set.Ioo (-δ) δ) (fun t : ℝ => e (p + t • v)) := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro s hs u hu a b ha hb hab
    have hcombo : a • (p + s • v) + b • (p + u • v) = p + (a • s + b • u) • v := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (p i) * hab
    have hjensen := hjens (hmem s hs) (hmem u hu) ha hb hab
    rw [hcombo] at hjensen
    exact hjensen
  have hle : ∀ t ∈ Set.Ioo (0 : ℝ) δ, v ⬝ᵥ h (p + t • v) ≤ v ⬝ᵥ h p := by
    intro t ht
    have htI : t ∈ Set.Ioo (-δ) δ := ⟨by linarith [ht.1, hδpos], ht.2⟩
    have h0I : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith [hδpos], hδpos⟩
    have h1 := ConcaveOn.le_slope_of_hasDerivAt hgconc h0I htI ht.1 (hg t htI)
    have h2 := ConcaveOn.slope_le_of_hasDerivAt hgconc h0I htI ht.1 (hg 0 h0I)
    rw [hzero] at h2
    exact le_trans h1 h2
  have hh0 : HasFDerivAt h Dh ((fun t : ℝ => p + t • v) 0) := by simpa using hh
  have hinner : HasDerivAt (h ∘ fun t : ℝ => p + t • v) (Dh v) 0 :=
    hh0.comp_hasDerivAt 0 (hline 0)
  have hdot : HasFDerivAt (fun w : ι → ℝ => v ⬝ᵥ w) (Real.dotL v) (h p) := by
    have hfun : (fun w : ι → ℝ => v ⬝ᵥ w) = (fun w => w ⬝ᵥ v) := by
      funext w
      exact dotProduct_comm _ _
    rw [hfun]
    exact Real.hasFDerivAt_dotProduct v (h p)
  have hdot0 : HasFDerivAt (fun w : ι → ℝ => v ⬝ᵥ w) (Real.dotL v)
      ((h ∘ fun t : ℝ => p + t • v) 0) := by simpa using hdot
  have hg'0 : HasDerivAt (fun t : ℝ => v ⬝ᵥ h (p + t • v)) (v ⬝ᵥ Dh v) 0 := by
    have hcomp := hdot0.comp_hasDerivAt 0 hinner
    rw [Real.dotL_apply] at hcomp
    have hcomm : (Dh v : ι → ℝ) ⬝ᵥ v = v ⬝ᵥ Dh v := dotProduct_comm _ _
    rw [hcomm] at hcomp
    exact hcomp
  have hsub : Set.Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun t ht => ne_of_gt ht
  have hle' : nhdsWithin 0 (Set.Ioi 0) ≤ nhdsWithin 0 ({0}ᶜ : Set ℝ) :=
    nhdsWithin_mono 0 hsub
  have htend : Filter.Tendsto (fun t : ℝ => (t - (0 : ℝ))⁻¹ •
      ((fun s : ℝ => v ⬝ᵥ h (p + s • v)) t - (fun s : ℝ => v ⬝ᵥ h (p + s • v)) 0))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (v ⬝ᵥ Dh v)) :=
    (HasDerivAt.tendsto_slope hg'0).mono_left hle'
  have hNe : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsGT_neBot 0
  have hevle : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (t - (0 : ℝ))⁻¹ •
      ((fun s : ℝ => v ⬝ᵥ h (p + s • v)) t
        - (fun s : ℝ => v ⬝ᵥ h (p + s • v)) 0) ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT hδpos] with t ht
    have hft : (fun s : ℝ => v ⬝ᵥ h (p + s • v)) t
        ≤ (fun s : ℝ => v ⬝ᵥ h (p + s • v)) 0 := by
      have h := hle t ht
      simpa [hzero] using h
    have hpos : (0 : ℝ) ≤ (t - 0)⁻¹ := by
      apply inv_nonneg.mpr
      linarith [ht.1]
    have hneg : (fun s : ℝ => v ⬝ᵥ h (p + s • v)) t
        - (fun s : ℝ => v ⬝ᵥ h (p + s • v)) 0 ≤ 0 :=
      sub_nonpos.mpr hft
    calc (t - (0 : ℝ))⁻¹ • ((fun s : ℝ => v ⬝ᵥ h (p + s • v)) t
            - (fun s : ℝ => v ⬝ᵥ h (p + s • v)) 0)
        = (t - (0 : ℝ))⁻¹ * ((fun s : ℝ => v ⬝ᵥ h (p + s • v)) t
            - (fun s : ℝ => v ⬝ᵥ h (p + s • v)) 0) := smul_eq_mul _ _
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos hneg
  exact le_of_tendsto htend hevle

/-- The compensated-demand Jacobian matrix is symmetric. -/
theorem compensatedJacobian_isSymm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) {e : (ι → ℝ) → ℝ} {h : (ι → ℝ) → ι → ℝ}
    {p : ι → ℝ} {Dh : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hp : p ∈ U)
    (hShephard : ∀ q ∈ U, HasFDerivAt e (Real.dotL (h q)) q)
    (hh : HasFDerivAt h Dh p) :
    (compensatedJacobian Dh).IsSymm := by
  change (compensatedJacobian Dh)ᵀ = compensatedJacobian Dh
  rw [← Matrix.ext_iff]
  intro i j
  simp only [Matrix.transpose_apply, compensatedJacobian, Matrix.of_apply]
  have h := dotProduct_compensated_symm hU hp hShephard hh
    (Pi.single j 1) (Pi.single i 1)
  simp only [single_one_dotProduct] at h
  exact h.symm

/-- The compensated-demand Jacobian matrix is negative semidefinite. -/
theorem dotProduct_compensatedJacobian_mulVec_nonpos {ι : Type*} [Fintype ι]
    [DecidableEq ι] {U : Set (ι → ℝ)} (hU : IsOpen U) {e : (ι → ℝ) → ℝ}
    {h : (ι → ℝ) → ι → ℝ} {p : ι → ℝ} {Dh : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hp : p ∈ U)
    (hconc : ConcaveOn ℝ U e)
    (hShephard : ∀ q ∈ U, HasFDerivAt e (Real.dotL (h q)) q)
    (hh : HasFDerivAt h Dh p) (x : ι → ℝ) :
    x ⬝ᵥ (compensatedJacobian Dh *ᵥ x) ≤ 0 := by
  have hx : x = ∑ j, x j • Pi.single j (1 : ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hSx : compensatedJacobian Dh *ᵥ x = Dh x := by
    ext i
    conv_rhs => rw [hx]
    rw [map_sum]
    simp [Matrix.mulVec, dotProduct, compensatedJacobian, Matrix.of_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  calc x ⬝ᵥ (compensatedJacobian Dh *ᵥ x) = x ⬝ᵥ Dh x := by rw [hSx]
    _ ≤ 0 := dotProduct_compensated_self_nonpos hU hp hconc hShephard hh x

end MathlibExt.Economics.CompensatedDemand
