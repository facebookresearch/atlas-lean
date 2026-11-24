/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Affine changes of variables for finite-order test functions

Precomposition by an invertible continuous affine map preserves compact support
and the order of differentiability. It is continuous for the canonical LF topology,
because every derivative seminorm on a fixed support is bounded by the corresponding
input seminorm times a power of the norm of the linear part.

Multiplying this map by a scalar gives normalized translations and anisotropic
rescalings, with no extra smoothness or finite-dimensionality assumption.
-/

@[expose] public section

open Set TopologicalSpace
open scoped Topology Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

namespace TestFunction

/-- The homeomorphism with value `L x + b`. -/
def affineHomeomorph (L : E ≃L[ℝ] E) (b : E) : E ≃ₜ E where
  toFun x := L x + b
  invFun x := L.symm (x - b)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := L.continuous.add continuous_const
  continuous_invFun := L.symm.continuous.comp (continuous_id.sub continuous_const)

/-- The affine homeomorphism evaluates as its linear part followed by translation. -/
@[simp]
theorem affineHomeomorph_apply (L : E ≃L[ℝ] E) (b x : E) :
    affineHomeomorph L b x = L x + b := rfl

/-- The inverse affine homeomorphism subtracts the translation and applies the inverse linear map. -/
@[simp]
theorem affineHomeomorph_symm_apply (L : E ≃L[ℝ] E) (b x : E) :
    (affineHomeomorph L b).symm x = L.symm (x - b) := rfl

/-- A support compact pulled back through `x ↦ L x + b`. -/
def affinePullbackCompact (L : E ≃L[ℝ] E) (b : E) (K : Compacts E) : Compacts E :=
  ⟨(affineHomeomorph L b).symm '' (K : Set E),
    K.isCompact.image (affineHomeomorph L b).symm.continuous⟩

/-- A point lies in the pulled-back compact support exactly when its affine image lies in the original
support. -/
@[simp]
theorem mem_affinePullbackCompact (L : E ≃L[ℝ] E) (b : E) (K : Compacts E) (x : E) :
    x ∈ affinePullbackCompact L b K ↔ L x + b ∈ K := by
  change x ∈ (affineHomeomorph L b).symm '' (K : Set E) ↔ L x + b ∈ K
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨L x + b, hx, by simp⟩

/-- Affine precomposition on the underlying finite-order test functions. -/
def affinePrecomp (L : E ≃L[ℝ] E) (b : E) (f : TestFunction (⊤ : Opens E) F n) :
    TestFunction (⊤ : Opens E) F n where
  toFun x := f (L x + b)
  contDiff' := f.contDiff.comp (L.contDiff.add contDiff_const)
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (affineHomeomorph L b)
  tsupport_subset' := by intro x hx; trivial

/-- Affine precomposition of a test function evaluates at the affine image of the point. -/
@[simp]
theorem affinePrecomp_apply (L : E ≃L[ℝ] E) (b x : E) (f : TestFunction (⊤ : Opens E) F n) :
    affinePrecomp L b f x = f (L x + b) := rfl

end TestFunction

namespace ContDiffMapSupportedIn

/-- The derivative bound for affine precomposition on a fixed compact support. -/
theorem norm_iteratedFDeriv_affinePrecomp_le (L : E ≃L[ℝ] E) (b : E) {K : Compacts E}
    (f : ContDiffMapSupportedIn E F n K) (i : ℕ) (hi : i ≤ n) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y => f (L y + b)) x‖ ≤
      ‖(L : E →L[ℝ] E)‖ ^ i * ContDiffMapSupportedIn.seminorm ℝ E F n K i f := by
  have hg : ContDiff ℝ n (fun y => f (y + b)) := f.contDiff.comp (contDiff_id.add contDiff_const)
  change ‖iteratedFDeriv ℝ i ((fun y => f (y + b)) ∘ (L : E →L[ℝ] E)) x‖ ≤ _
  rw [(L : E →L[ℝ] E).iteratedFDeriv_comp_right hg x (mod_cast hi)]
  rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := (f : E → F)) i b
    ((L : E →L[ℝ] E) x)]
  calc
    ‖(iteratedFDeriv ℝ i f (L x + b)).compContinuousLinearMap (fun _ => (L : E →L[ℝ] E))‖
        ≤ ‖iteratedFDeriv ℝ i f (L x + b)‖ * ‖(L : E →L[ℝ] E)‖ ^ i := by
          simpa using (iteratedFDeriv ℝ i f (L x + b)).norm_compContinuousLinearMap_le
            (fun _ : Fin i => (L : E →L[ℝ] E))
    _ ≤ ContDiffMapSupportedIn.seminorm ℝ E F n K i f * ‖(L : E →L[ℝ] E)‖ ^ i :=
      mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_apply_le_seminorm ℝ hi)
        (pow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _

/-- Affine precomposition as a continuous linear map between fixed-support spaces. -/
noncomputable def affinePrecompCLM (L : E ≃L[ℝ] E) (b : E) (K : Compacts E) :
    ContDiffMapSupportedIn E F n K →L[ℝ]
      ContDiffMapSupportedIn E F n (TestFunction.affinePullbackCompact L b K) :=
  ContDiffMapSupportedIn.mkCLM ℝ (fun f x => f (L x + b))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun f => f.contDiff.comp (L.contDiff.add contDiff_const))
    (fun f x hx => f.zero_on_compl (by
      change L x + b ∉ K
      exact (TestFunction.mem_affinePullbackCompact L b K x).not.mp hx))
    (fun i hi => ⟨{i}, ‖(L : E →L[ℝ] E)‖ ^ i, pow_nonneg (norm_nonneg _) _,
      fun f x _ => by simpa using norm_iteratedFDeriv_affinePrecomp_le L b f i hi x⟩)

/-- The continuous affine pullback between fixed-support spaces preserves the expected pointwise
formula. -/
@[simp]
theorem affinePrecompCLM_apply (L : E ≃L[ℝ] E) (b : E) (K : Compacts E)
    (f : ContDiffMapSupportedIn E F n K) (x : E) :
    affinePrecompCLM L b K f x = f (L x + b) := rfl

end ContDiffMapSupportedIn

namespace TestFunction

/-- Affine precomposition is continuous for the canonical finite-order LF topology. -/
noncomputable def affinePrecompCLM (L : E ≃L[ℝ] E) (b : E) :
    TestFunction (⊤ : Opens E) F n →L[ℝ] TestFunction (⊤ : Opens E) F n :=
  TestFunction.limitCLM ℝ (affinePrecomp L b)
    (fun K _ => TestFunction.ofSupportedInCLM ℝ (by intro x hx; trivial) ∘L
      ContDiffMapSupportedIn.affinePrecompCLM L b K)
    (by intro K hK f; rfl)

/-- The continuous affine pullback on the test-function LF space evaluates by affine precomposition. -/
@[simp]
theorem affinePrecompCLM_apply (L : E ≃L[ℝ] E) (b x : E) (f : TestFunction (⊤ : Opens E) F n) :
    affinePrecompCLM L b f x = f (L x + b) := rfl

/-- The support moves by the inverse affine map, with equality. -/
theorem tsupport_affinePrecompCLM (L : E ≃L[ℝ] E) (b : E) (f : TestFunction (⊤ : Opens E) F n) :
    tsupport (affinePrecompCLM L b f) = (affineHomeomorph L b) ⁻¹' tsupport f := by
  exact tsupport_comp_eq_preimage f (affineHomeomorph L b)

/-- A scalar normalization of affine precomposition, still continuous on finite-order tests. -/
noncomputable def affineScaleCLM (c : ℝ) (L : E ≃L[ℝ] E) (b : E) :
    TestFunction (⊤ : Opens E) F n →L[ℝ] TestFunction (⊤ : Opens E) F n :=
  c • affinePrecompCLM L b

/-- Scalar-normalized affine pullback is the scalar times evaluation at the affine image. -/
@[simp]
theorem affineScaleCLM_apply (c : ℝ) (L : E ≃L[ℝ] E) (b x : E)
    (f : TestFunction (⊤ : Opens E) F n) :
    affineScaleCLM c L b f x = c • f (L x + b) := rfl

/-- Scalar normalization cannot enlarge the pulled-back support, including when `c = 0`. -/
theorem tsupport_affineScaleCLM_subset (c : ℝ) (L : E ≃L[ℝ] E) (b : E)
    (f : TestFunction (⊤ : Opens E) F n) :
    tsupport (affineScaleCLM c L b f) ⊆ (affineHomeomorph L b) ⁻¹' tsupport f := by
  exact (tsupport_smul_subset_right (fun _ : E => c) (affinePrecompCLM L b f)).trans_eq
    (tsupport_affinePrecompCLM L b f)

/-- Pullback through the identity affine map is the identity on test functions. -/
@[simp]
theorem affinePrecompCLM_refl (f : TestFunction (⊤ : Opens E) F n) :
    affinePrecompCLM (ContinuousLinearEquiv.refl ℝ E) 0 f = f := by
  ext x
  simp

/-- Pulling a test back through the inverse affine map undoes affine precomposition. -/
theorem affinePrecompCLM_inverse (L : E ≃L[ℝ] E) (b : E)
    (f : TestFunction (⊤ : Opens E) F n) :
    affinePrecompCLM L.symm (-L.symm b) (affinePrecompCLM L b f) = f := by
  ext x
  simp

end TestFunction
