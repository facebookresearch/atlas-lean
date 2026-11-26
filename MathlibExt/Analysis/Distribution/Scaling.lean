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
# Affine pullbacks of compactly supported test functions

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. Pullback P_h f = f ∘ h is a continuous
real-linear map on Dⁿ(E,F), and its support is h⁻¹(tsupport f). For functions supported in a
fixed compact K, the i-th derivative seminorm satisfies pᵢ(P_h f) ≤ ‖L‖^i pᵢ(f) whenever i ≤
n. Multiplying by c ∈ ℝ gives the continuous map f ↦ c f ∘ h, whose support is contained in
h⁻¹(tsupport f), also when c = 0.
-/

@[expose] public section

open Set TopologicalSpace
open scoped Topology Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

namespace TestFunction

/-- **The homeomorphism of an invertible affine map.**

Let E be a normed real vector space, L : E ≃L[ℝ] E a continuous linear equivalence and b ∈ E.
Put h(x) = Lx + b. The map h is a homeomorphism with inverse h⁻¹(x) = L⁻¹(x − b).
-/
def affineHomeomorph (L : E ≃L[ℝ] E) (b : E) : E ≃ₜ E where
  toFun x := L x + b
  invFun x := L.symm (x - b)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := L.continuous.add continuous_const
  continuous_invFun := L.symm.continuous.comp (continuous_id.sub continuous_const)

/-- **Evaluation of the affine homeomorphism.**

Let E be a normed real vector space, L : E ≃L[ℝ] E a continuous linear equivalence and b ∈ E.
Put h(x) = Lx + b. For every x ∈ E, the affine homeomorphism satisfies h(x) = Lx + b.
-/
@[simp]
theorem affineHomeomorph_apply (L : E ≃L[ℝ] E) (b x : E) :
    affineHomeomorph L b x = L x + b := rfl

/-- **Evaluation of the inverse affine homeomorphism.**

Let E be a normed real vector space, L : E ≃L[ℝ] E a continuous linear equivalence and b ∈ E.
Put h(x) = Lx + b. For every x ∈ E, one has h⁻¹(x) = L⁻¹(x − b).
-/
@[simp]
theorem affineHomeomorph_symm_apply (L : E ≃L[ℝ] E) (b x : E) :
    (affineHomeomorph L b).symm x = L.symm (x - b) := rfl

/-- **A compact set pulled back by an affine homeomorphism.**

Let E be a normed real vector space, L : E ≃L[ℝ] E a continuous linear equivalence and b ∈ E.
Put h(x) = Lx + b. For compact K ⊆ E, the preimage K′ = {x : Lx + b ∈ K} is compact.
-/
def affinePullbackCompact (L : E ≃L[ℝ] E) (b : E) (K : Compacts E) : Compacts E :=
  ⟨(affineHomeomorph L b).symm '' (K : Set E),
    K.isCompact.image (affineHomeomorph L b).symm.continuous⟩

/-- **Membership in the pulled-back compact set.**

Let E be a normed real vector space, L : E ≃L[ℝ] E a continuous linear equivalence and b ∈ E.
Put h(x) = Lx + b. For compact K ⊆ E and K′ = h⁻¹(K), one has x ∈ K′ if and only if Lx + b ∈
K.
-/
@[simp]
theorem mem_affinePullbackCompact (L : E ≃L[ℝ] E) (b : E) (K : Compacts E) (x : E) :
    x ∈ affinePullbackCompact L b K ↔ L x + b ∈ K := by
  change x ∈ (affineHomeomorph L b).symm '' (K : Set E) ↔ L x + b ∈ K
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨L x + b, hx, by simp⟩

/-- **Affine precomposition of a test function.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. For f ∈ Dⁿ(E,F), define P_h f by (P_h
f)(x) = f(Lx + b). This function is Cⁿ and compactly supported.
-/
def affinePrecomp (L : E ≃L[ℝ] E) (b : E) (f : TestFunction (⊤ : Opens E) F n) :
    TestFunction (⊤ : Opens E) F n where
  toFun x := f (L x + b)
  contDiff' := f.contDiff.comp (L.contDiff.add contDiff_const)
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (affineHomeomorph L b)
  tsupport_subset' := by intro x hx; trivial

/-- **Evaluation of affine precomposition.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. For f ∈ Dⁿ(E,F) and x ∈ E, one has
(P_h f)(x) = f(Lx + b).
-/
@[simp]
theorem affinePrecomp_apply (L : E ≃L[ℝ] E) (b x : E) (f : TestFunction (⊤ : Opens E) F n) :
    affinePrecomp L b f x = f (L x + b) := rfl

end TestFunction

namespace ContDiffMapSupportedIn

/-- **Derivative bound for an affine pullback.**

Let E,F be normed real vector spaces, n ∈ ℕ ∪ {∞}, K ⊆ E compact, L a continuous linear
equivalence of E, and b ∈ E. Put h(x) = Lx + b and K′ = h⁻¹(K). Let f be Cⁿ and supported in
K, let i ∈ ℕ with i ≤ n, and put pᵢ(f) = sup_y ‖Dⁱf(y)‖, the fixed-support derivative
seminorm. Then for every x ∈ E, ‖Dⁱ(f ∘ h)(x)‖ ≤ ‖L‖^i pᵢ(f).
-/
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

/-- **Continuous affine pullback between fixed-support spaces.**

Let E,F be normed real vector spaces, n ∈ ℕ ∪ {∞}, K ⊆ E compact, L a continuous linear
equivalence of E, and b ∈ E. Put h(x) = Lx + b and K′ = h⁻¹(K). Precomposition f ↦ f ∘ h is a
continuous real-linear map from the Cⁿ functions supported in K to those supported in K′, with
their derivative-seminorm topologies.
-/
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

/-- **Evaluation of the fixed-support pullback.**

Let E,F be normed real vector spaces, n ∈ ℕ ∪ {∞}, K ⊆ E compact, L a continuous linear
equivalence of E, and b ∈ E. Put h(x) = Lx + b and K′ = h⁻¹(K). For the continuous real-linear
pullback P_h between these fixed-support spaces and every f supported in K, one has (P_h f)(x)
= f(Lx + b).
-/
@[simp]
theorem affinePrecompCLM_apply (L : E ≃L[ℝ] E) (b : E) (K : Compacts E)
    (f : ContDiffMapSupportedIn E F n K) (x : E) :
    affinePrecompCLM L b K f x = f (L x + b) := rfl

end ContDiffMapSupportedIn

namespace TestFunction

/-- **Continuous affine pullback on the test-function space.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. Precomposition P_h : f ↦ f ∘ h is a
continuous real-linear endomorphism of Dⁿ(E,F).
-/
noncomputable def affinePrecompCLM (L : E ≃L[ℝ] E) (b : E) :
    TestFunction (⊤ : Opens E) F n →L[ℝ] TestFunction (⊤ : Opens E) F n :=
  TestFunction.limitCLM ℝ (affinePrecomp L b)
    (fun K _ => TestFunction.ofSupportedInCLM ℝ (by intro x hx; trivial) ∘L
      ContDiffMapSupportedIn.affinePrecompCLM L b K)
    (by intro K hK f; rfl)

/-- **Evaluation of the continuous test-function pullback.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. For the continuous real-linear map P_h
on Dⁿ(E,F), one has (P_h f)(x) = f(Lx + b) for all f and x.
-/
@[simp]
theorem affinePrecompCLM_apply (L : E ≃L[ℝ] E) (b x : E) (f : TestFunction (⊤ : Opens E) F n) :
    affinePrecompCLM L b f x = f (L x + b) := rfl

/-- **Support of an affine test-function pullback.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. For f ∈ Dⁿ(E,F), the topological
support satisfies tsupport(P_h f) = h⁻¹(tsupport f), where P_h f = f ∘ h.
-/
theorem tsupport_affinePrecompCLM (L : E ≃L[ℝ] E) (b : E) (f : TestFunction (⊤ : Opens E) F n) :
    tsupport (affinePrecompCLM L b f) = (affineHomeomorph L b) ⁻¹' tsupport f := by
  exact tsupport_comp_eq_preimage f (affineHomeomorph L b)

/-- **A scalar-normalized affine pullback.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. For any c ∈ ℝ, the map S_{c,h} : f ↦
c(f ∘ h) is a continuous real-linear endomorphism of Dⁿ(E,F).
-/
noncomputable def affineScaleCLM (c : ℝ) (L : E ≃L[ℝ] E) (b : E) :
    TestFunction (⊤ : Opens E) F n →L[ℝ] TestFunction (⊤ : Opens E) F n :=
  c • affinePrecompCLM L b

/-- **Evaluation of a scalar-normalized affine pullback.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. For c ∈ ℝ, S_{c,h} f = c(f ∘ h)
satisfies (S_{c,h} f)(x) = c · f(Lx + b).
-/
@[simp]
theorem affineScaleCLM_apply (c : ℝ) (L : E ≃L[ℝ] E) (b x : E)
    (f : TestFunction (⊤ : Opens E) F n) :
    affineScaleCLM c L b f x = c • f (L x + b) := rfl

/-- **Support of a scalar-normalized affine pullback.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. For c ∈ ℝ and S_{c,h} f = c(f ∘ h),
one has tsupport(S_{c,h} f) ⊆ h⁻¹(tsupport f). This includes c = 0, for which the support is
empty.
-/
theorem tsupport_affineScaleCLM_subset (c : ℝ) (L : E ≃L[ℝ] E) (b : E)
    (f : TestFunction (⊤ : Opens E) F n) :
    tsupport (affineScaleCLM c L b f) ⊆ (affineHomeomorph L b) ⁻¹' tsupport f := by
  exact (tsupport_smul_subset_right (fun _ : E => c) (affinePrecompCLM L b f)).trans_eq
    (tsupport_affinePrecompCLM L b f)

/-- **The identity affine pullback.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For h(x) = x, obtained
from L = id and b = 0, the pullback satisfies P_h f = f for every f ∈ Dⁿ(E,F).
-/
@[simp]
theorem affinePrecompCLM_refl (f : TestFunction (⊤ : Opens E) F n) :
    affinePrecompCLM (ContinuousLinearEquiv.refl ℝ E) 0 f = f := by
  ext x
  simp

/-- **Inverse affine pullbacks.**

Let E,F be normed real vector spaces and n ∈ ℕ ∪ {∞}. Let Dⁿ(E,F) be the space of compactly
supported Cⁿ functions E → F with its canonical test-function topology. For a continuous
linear equivalence L of E and b ∈ E, put h(x) = Lx + b. The inverse map is h⁻¹(x) = L⁻¹x −
L⁻¹b. Its pullback satisfies P_{h⁻¹}(P_h f) = f for every f ∈ Dⁿ(E,F).
-/
theorem affinePrecompCLM_inverse (L : E ≃L[ℝ] E) (b : E)
    (f : TestFunction (⊤ : Opens E) F n) :
    affinePrecompCLM L.symm (-L.symm b) (affinePrecompCLM L b f) = f := by
  ext x
  simp

end TestFunction
