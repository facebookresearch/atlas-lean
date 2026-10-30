/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# Nonzero eigenvalues of a product, in either order

For linear maps `f : V →ₗ[𝕜] W` and `g : W →ₗ[𝕜] V` over a field, the nonzero
eigenvalues of `f ∘ₗ g` and of `g ∘ₗ f` coincide, and they do so with the same
geometric multiplicity: the eigenspaces are linearly equivalent, via `g` and a
rescaled `f`. Generalized eigenspaces have equal `Module.finrank` at every
exponent and are finite-dimensional together. In finite dimension the stabilized
generalized eigenspace (for example at exponent `⊤`) measures algebraic multiplicity.

This is the eigenvector-level refinement of the spectrum statement in Mathlib
(`spectrum.nonzero_mul_comm`): the spectrum records only invertibility, while
the statements here compare the eigenspaces themselves. In particular the
characteristic-polynomial identity `Matrix.charpoly_mul_comm` gives equality of
algebraic multiplicities for square matrices, but says nothing about geometric
multiplicities; the linear equivalence below does, and it needs no
finite-dimensionality hypothesis.

The eigenvalue transfer also applies to `T† * T` and `T * T†`, which have the
same nonzero eigenvalues. The bounded-operator version is in
`MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm`.

## Main declarations

* `End.eigenspaceCompEquiv`: for `μ ≠ 0`, the `μ`-eigenspaces of
  `f ∘ₗ g` and of `g ∘ₗ f` are linearly equivalent.
* `End.hasEigenvalue_comp_iff`: `μ ≠ 0` is an eigenvalue of `f ∘ₗ g`
  iff it is an eigenvalue of `g ∘ₗ f`.
* `End.finrank_eigenspace_comp_eq`: eigenspace finranks agree; in finite
  dimension these are the geometric multiplicities.
* `End.finrank_genEigenspace_comp_eq`: the generalized eigenspaces
  have equal `Module.finrank`, for every exponent `k : ℕ∞`.
* `End.finite_genEigenspace_comp_iff`: the generalized eigenspaces are
  finite-dimensional together for every exponent `k : ℕ∞`.
* `End.hasEigenvector_comp`: an eigenvector of `f ∘ₗ g` is sent by `g`
  to an eigenvector of `g ∘ₗ f` for the same nonzero eigenvalue.
* The `*_mul_*` versions: the same statements for endomorphisms, with `*`
  in place of `∘ₗ`.
* `Matrix.hasEigenvalue_mul_iff`, `Matrix.finrank_eigenspace_mul_eq`,
  `Matrix.finrank_genEigenspace_mul_eq`, `Matrix.finite_genEigenspace_mul_iff`:
  the matrix versions, for
  `A : Matrix ι κ 𝕜` and `B : Matrix κ ι 𝕜`.
-/

namespace MathlibExt.LinearAlgebra.Eigenspace.MulComm

open Module

variable {𝕜 V W : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W]
  [Module 𝕜 W]

namespace End

variable {f : V →ₗ[𝕜] W} {g : W →ₗ[𝕜] V} {μ : 𝕜}

/-- `g` sends the `μ`-eigenspace of `f ∘ₗ g` into the `μ`-eigenspace of
`g ∘ₗ f`: if `(f ∘ₗ g) x = μ • x` then `(g ∘ₗ f) (g x) = μ • (g x)`. -/
theorem mapsTo_eigenspace_comp (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V) (μ : 𝕜) :
    Set.MapsTo g (Module.End.eigenspace (f ∘ₗ g) μ)
      (Module.End.eigenspace (g ∘ₗ f) μ) := by
  intro x hx
  simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx ⊢
  calc (g ∘ₗ f) (g x) = ((g ∘ₗ f) ∘ₗ g) x := (LinearMap.comp_apply _ _ _).symm
    _ = (g ∘ₗ (f ∘ₗ g)) x := by rw [LinearMap.comp_assoc]
    _ = g ((f ∘ₗ g) x) := LinearMap.comp_apply _ _ _
    _ = g (μ • x) := by rw [hx]
    _ = μ • g x := map_smul g μ x

/-- The map `g` restricted to the eigenspaces is injective when `μ ≠ 0`: if
`g x = 0` for an eigenvector `x` of `f ∘ₗ g`, then `(f ∘ₗ g) x = 0 = μ • x`,
so `x = 0`. -/
theorem injective_restrict_eigenspace_comp (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    Function.Injective (LinearMap.restrict g (mapsTo_eigenspace_comp f g μ)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hBx : g (x : W) = 0 :=
    congrArg (fun y : ↥(Module.End.eigenspace (g ∘ₗ f) μ) => (y : V)) hx
  have hxfg : (f ∘ₗ g) (x : W) = 0 := by
    rw [LinearMap.comp_apply, hBx, map_zero]
  have hxμ : (f ∘ₗ g) (x : W) = μ • (x : W) :=
    Module.End.mem_eigenspace_iff.mp x.2
  rw [hxfg] at hxμ
  have hx0 : (x : W) = 0 := (smul_eq_zero.mp hxμ.symm).resolve_left hμ
  exact Subtype.ext hx0

/-- The map `g` restricted to the eigenspaces is surjective when `μ ≠ 0`: an
eigenvector `y` of `g ∘ₗ f` is the image of `μ⁻¹ • f y`. -/
theorem surjective_restrict_eigenspace_comp (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    Function.Surjective (LinearMap.restrict g (mapsTo_eigenspace_comp f g μ)) := by
  intro y
  refine ⟨⟨μ⁻¹ • f (y : V), ?_⟩, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    calc (f ∘ₗ g) (μ⁻¹ • f (y : V)) = μ⁻¹ • (f ∘ₗ g) (f (y : V)) := by
          rw [map_smul]
      _ = μ⁻¹ • f ((g ∘ₗ f) (y : V)) := by
          have h1 : (f ∘ₗ g) (f (y : V)) = f ((g ∘ₗ f) (y : V)) := by
            simp only [LinearMap.comp_apply]
          rw [h1]
      _ = μ⁻¹ • f (μ • (y : V)) := by
          rw [Module.End.mem_eigenspace_iff.mp y.2]
      _ = μ⁻¹ • (μ • f (y : V)) := by rw [map_smul]
      _ = f (y : V) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ • (μ⁻¹ • f (y : V)) := by rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
  · apply Subtype.ext
    show g (μ⁻¹ • f (y : V)) = (y : V)
    calc g (μ⁻¹ • f (y : V)) = μ⁻¹ • (g ∘ₗ f) (y : V) := by
          rw [map_smul, ← LinearMap.comp_apply]
      _ = μ⁻¹ • (μ • (y : V)) := by rw [Module.End.mem_eigenspace_iff.mp y.2]
      _ = (y : V) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- For a nonzero eigenvalue, the eigenspaces of `f ∘ₗ g` and of `g ∘ₗ f`
are linearly equivalent, via `g` in one direction. -/
noncomputable def eigenspaceCompEquiv (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V) {μ : 𝕜}
    (hμ : μ ≠ 0) :
    Module.End.eigenspace (f ∘ₗ g) μ ≃ₗ[𝕜] Module.End.eigenspace (g ∘ₗ f) μ :=
  LinearEquiv.ofBijective (LinearMap.restrict g (mapsTo_eigenspace_comp f g μ))
    ⟨injective_restrict_eigenspace_comp f g hμ,
     surjective_restrict_eigenspace_comp f g hμ⟩

/-- The geometric multiplicities of a nonzero eigenvalue of `f ∘ₗ g` and of
`g ∘ₗ f` agree. -/
theorem finrank_eigenspace_comp_eq (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V) {μ : 𝕜}
    (hμ : μ ≠ 0) :
    Module.finrank 𝕜 (Module.End.eigenspace (f ∘ₗ g) μ) =
      Module.finrank 𝕜 (Module.End.eigenspace (g ∘ₗ f) μ) :=
  (eigenspaceCompEquiv f g hμ).finrank_eq

/-- An eigenvector of `f ∘ₗ g` for a nonzero eigenvalue is sent by `g` to an
eigenvector of `g ∘ₗ f` for the same eigenvalue. -/
theorem hasEigenvector_comp {f : V →ₗ[𝕜] W} {g : W →ₗ[𝕜] V} {μ : 𝕜} (hμ : μ ≠ 0)
    {x : W} (hx : Module.End.HasEigenvector (f ∘ₗ g) μ x) : Module.End.HasEigenvector (g ∘ₗ f) μ (g x) := by
  have hxfg : (f ∘ₗ g) x = μ • x := hx.apply_eq_smul
  have hgx : g x ≠ 0 := by
    intro h
    have h0 : (f ∘ₗ g) x = 0 := by rw [LinearMap.comp_apply, h, map_zero]
    rw [hxfg] at h0
    exact hx.2 ((smul_eq_zero.mp h0).resolve_left hμ)
  exact Module.End.hasEigenvector_iff.mpr
    ⟨mapsTo_eigenspace_comp f g μ (Module.End.mem_eigenspace_iff.mpr hxfg), hgx⟩

/-- A nonzero scalar is an eigenvalue of `f ∘ₗ g` iff it is an eigenvalue of
`g ∘ₗ f`. -/
theorem hasEigenvalue_comp_iff (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (f ∘ₗ g) μ ↔ Module.End.HasEigenvalue (g ∘ₗ f) μ := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    exact Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_comp hμ hx)
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    exact Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_comp hμ hx)

/-- `g` sends the generalized `μ`-eigenspace of `f ∘ₗ g` into the generalized
`μ`-eigenspace of `g ∘ₗ f`, for every exponent. This is the intertwining
`(g ∘ₗ f) ∘ₗ g = g ∘ₗ (f ∘ₗ g)` applied to Mathlib's
`Module.End.mapsTo_genEigenspace_of_comp`. -/
theorem mapsTo_genEigenspace_comp (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V) (μ : 𝕜) (k : ℕ∞) :
    Set.MapsTo g (Module.End.genEigenspace (f ∘ₗ g) μ k) (Module.End.genEigenspace (g ∘ₗ f) μ k) :=
  Module.End.mapsTo_genEigenspace_of_comp g (LinearMap.comp_assoc g f g) μ k

/-- If `g x = 0` and `x` lies in the generalized `μ`-eigenspace of `f ∘ₗ g`
with `μ ≠ 0`, then `x = 0`. Indeed, on the kernel of `g` the map `f ∘ₗ g`
vanishes, so `(f ∘ₗ g - μ • 1) ^ l` acts as `(-μ) ^ l • 1` there. -/
theorem eq_zero_of_apply_eq_zero_of_mem_genEigenspace
    {f : V →ₗ[𝕜] W} {g : W →ₗ[𝕜] V} {μ : 𝕜} (hμ : μ ≠ 0) {k : ℕ∞} {x : W}
    (hx : x ∈ Module.End.genEigenspace (f ∘ₗ g) μ k) (hgx : g x = 0) : x = 0 := by
  obtain ⟨l, -, hxl⟩ := Module.End.mem_genEigenspace.mp hx
  rw [LinearMap.mem_ker] at hxl
  have hfg : (f ∘ₗ g) x = 0 := by rw [LinearMap.comp_apply, hgx, map_zero]
  have hpow : ∀ n : ℕ, ((f ∘ₗ g - μ • 1 : Module.End 𝕜 W) ^ n) x = (-μ) ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hT : (f ∘ₗ g - μ • 1 : Module.End 𝕜 W) ((-μ) ^ n • x) =
          (-μ) ^ (n + 1) • x := by
        rw [LinearMap.sub_apply, map_smul, map_smul, LinearMap.smul_apply,
          Module.End.one_apply, hfg, smul_zero, zero_sub, smul_smul, pow_succ,
          mul_neg, neg_smul]
      rw [pow_succ', Module.End.mul_apply, ih, hT]
  rw [hpow l] at hxl
  exact (smul_eq_zero.mp hxl).resolve_left (pow_ne_zero l (neg_ne_zero.mpr hμ))

/-- The restriction of `g` to the generalized `μ`-eigenspaces. -/
noncomputable def genEigenspaceCompMap (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V) (μ : 𝕜)
    (k : ℕ∞) :
    Module.End.genEigenspace (f ∘ₗ g) μ k →ₗ[𝕜] Module.End.genEigenspace (g ∘ₗ f) μ k :=
  LinearMap.restrict g (mapsTo_genEigenspace_comp f g μ k)

/-- The restriction of `g` to a generalized `μ`-eigenspace with `μ ≠ 0` is
injective. -/
theorem injective_genEigenspaceCompMap (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V)
    {μ : 𝕜} (hμ : μ ≠ 0) (k : ℕ∞) :
    Function.Injective (genEigenspaceCompMap f g μ k) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hgx : g (x : W) = 0 :=
    congrArg (fun y : ↥(Module.End.genEigenspace (g ∘ₗ f) μ k) => (y : V)) hx
  have hx0 : (x : W) = 0 :=
    eq_zero_of_apply_eq_zero_of_mem_genEigenspace hμ x.2 hgx
  exact Subtype.ext hx0

/-- For a nonzero scalar, the generalized eigenspaces of `f ∘ₗ g` and of
`g ∘ₗ f` are finite-dimensional together, for every exponent `k : ℕ∞`. -/
theorem finite_genEigenspace_comp_iff (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V) {μ : 𝕜}
    (hμ : μ ≠ 0) (k : ℕ∞) :
    Module.Finite 𝕜 (Module.End.genEigenspace (f ∘ₗ g) μ k) ↔
      Module.Finite 𝕜 (Module.End.genEigenspace (g ∘ₗ f) μ k) := by
  constructor
  · intro hfin
    let := hfin
    exact FiniteDimensional.of_injective (genEigenspaceCompMap g f μ k)
      (injective_genEigenspaceCompMap g f hμ k)
  · intro hfin
    let := hfin
    exact FiniteDimensional.of_injective (genEigenspaceCompMap f g μ k)
      (injective_genEigenspaceCompMap f g hμ k)

set_option linter.style.haveILetI false in
/-- The generalized `μ`-eigenspaces of `f ∘ₗ g` and of `g ∘ₗ f` have equal
`Module.finrank`, for every exponent `k : ℕ∞` and every nonzero `μ`.
They are finite-dimensional together; if both are infinite-dimensional, both
finranks are zero. In finite dimension only the stabilized generalized eigenspace
(for example at exponent `⊤`) measures algebraic multiplicity. -/
theorem finrank_genEigenspace_comp_eq (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] V) {μ : 𝕜}
    (hμ : μ ≠ 0) (k : ℕ∞) :
    Module.finrank 𝕜 (Module.End.genEigenspace (f ∘ₗ g) μ k) =
      Module.finrank 𝕜 (Module.End.genEigenspace (g ∘ₗ f) μ k) := by
  by_cases hfin : Module.Finite 𝕜 (Module.End.genEigenspace (f ∘ₗ g) μ k)
  · let := hfin
    let := (finite_genEigenspace_comp_iff f g hμ k).mp hfin
    exact le_antisymm
      (LinearMap.finrank_le_finrank_of_injective
        (injective_genEigenspaceCompMap f g hμ k))
      (LinearMap.finrank_le_finrank_of_injective
        (injective_genEigenspaceCompMap g f hμ k))
  · have hfin' : ¬ Module.Finite 𝕜 (Module.End.genEigenspace (g ∘ₗ f) μ k) := by
      intro h
      exact hfin ((finite_genEigenspace_comp_iff f g hμ k).mpr h)
    rw [Module.finrank_of_not_finite hfin, Module.finrank_of_not_finite hfin']

section Mul

variable {A B : Module.End 𝕜 V} {μ : 𝕜}

/-- The `*` form of `eigenspaceCompEquiv`, for endomorphisms of one space. -/
noncomputable def eigenspaceMulEquiv (A B : Module.End 𝕜 V) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.End.eigenspace (A * B) μ ≃ₗ[𝕜] Module.End.eigenspace (B * A) μ := by
  simp only [Module.End.mul_eq_comp]
  exact eigenspaceCompEquiv A B hμ

/-- The `*` form of `finrank_eigenspace_comp_eq`. -/
theorem finrank_eigenspace_mul_eq (A B : Module.End 𝕜 V) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.finrank 𝕜 (Module.End.eigenspace (A * B) μ) =
      Module.finrank 𝕜 (Module.End.eigenspace (B * A) μ) := by
  simp only [Module.End.mul_eq_comp]
  exact finrank_eigenspace_comp_eq A B hμ

/-- The `*` form of `hasEigenvector_comp`. -/
theorem hasEigenvector_mul {A B : Module.End 𝕜 V} {μ : 𝕜} (hμ : μ ≠ 0) {x : V}
    (hx : (A * B).HasEigenvector μ x) : (B * A).HasEigenvector μ (B x) := by
  simp only [Module.End.mul_eq_comp] at hx ⊢
  exact hasEigenvector_comp hμ hx

/-- The `*` form of `hasEigenvalue_comp_iff`. -/
theorem hasEigenvalue_mul_iff (A B : Module.End 𝕜 V) {μ : 𝕜} (hμ : μ ≠ 0) :
    (A * B).HasEigenvalue μ ↔ (B * A).HasEigenvalue μ := by
  simp only [Module.End.mul_eq_comp]
  exact hasEigenvalue_comp_iff A B hμ

/-- The `*` form of `finrank_genEigenspace_comp_eq`. -/
theorem finrank_genEigenspace_mul_eq (A B : Module.End 𝕜 V) {μ : 𝕜} (hμ : μ ≠ 0)
    (k : ℕ∞) :
    Module.finrank 𝕜 ((A * B).genEigenspace μ k) =
      Module.finrank 𝕜 ((B * A).genEigenspace μ k) := by
  simp only [Module.End.mul_eq_comp]
  exact finrank_genEigenspace_comp_eq A B hμ k

/-- The `*` form of `finite_genEigenspace_comp_iff`. -/
theorem finite_genEigenspace_mul_iff (A B : Module.End 𝕜 V) {μ : 𝕜} (hμ : μ ≠ 0)
    (k : ℕ∞) :
    Module.Finite 𝕜 ((A * B).genEigenspace μ k) ↔
      Module.Finite 𝕜 ((B * A).genEigenspace μ k) := by
  simp only [Module.End.mul_eq_comp]
  exact finite_genEigenspace_comp_iff A B hμ k

end Mul

end End

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {A : Matrix ι κ 𝕜} {B : Matrix κ ι 𝕜} {μ : 𝕜}

/-- A nonzero scalar is an eigenvalue of the matrix product `A * B` iff it is
an eigenvalue of `B * A`. -/
theorem hasEigenvalue_mul_iff (A : Matrix ι κ 𝕜) (B : Matrix κ ι 𝕜) {μ : 𝕜}
    (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (Matrix.toLin' (A * B)) μ ↔
      Module.End.HasEigenvalue (Matrix.toLin' (B * A)) μ := by
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact End.hasEigenvalue_comp_iff (Matrix.toLin' A) (Matrix.toLin' B) hμ

/-- The geometric multiplicities of a nonzero eigenvalue of `A * B` and of
`B * A` agree. -/
theorem finrank_eigenspace_mul_eq (A : Matrix ι κ 𝕜) (B : Matrix κ ι 𝕜) {μ : 𝕜}
    (hμ : μ ≠ 0) :
    Module.finrank 𝕜 (Module.End.eigenspace (Matrix.toLin' (A * B)) μ) =
      Module.finrank 𝕜 (Module.End.eigenspace (Matrix.toLin' (B * A)) μ) := by
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact End.finrank_eigenspace_comp_eq (Matrix.toLin' A) (Matrix.toLin' B) hμ

/-- The generalized `μ`-eigenspaces of `A * B` and of `B * A` have equal
`Module.finrank`, for every exponent `k : ℕ∞`. -/
theorem finrank_genEigenspace_mul_eq (A : Matrix ι κ 𝕜) (B : Matrix κ ι 𝕜) {μ : 𝕜}
    (hμ : μ ≠ 0) (k : ℕ∞) :
    Module.finrank 𝕜 (Module.End.genEigenspace (Matrix.toLin' (A * B)) μ k) =
      Module.finrank 𝕜 (Module.End.genEigenspace (Matrix.toLin' (B * A)) μ k) := by
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact End.finrank_genEigenspace_comp_eq (Matrix.toLin' A) (Matrix.toLin' B) hμ k

/-- The generalized eigenspaces of rectangular products in opposite orders
are finite-dimensional together for a nonzero scalar and every exponent. -/
theorem finite_genEigenspace_mul_iff (A : Matrix ι κ 𝕜) (B : Matrix κ ι 𝕜) {μ : 𝕜}
    (hμ : μ ≠ 0) (k : ℕ∞) :
    Module.Finite 𝕜 (Module.End.genEigenspace (Matrix.toLin' (A * B)) μ k) ↔
      Module.Finite 𝕜 (Module.End.genEigenspace (Matrix.toLin' (B * A)) μ k) := by
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact End.finite_genEigenspace_comp_iff (Matrix.toLin' A) (Matrix.toLin' B) hμ k

end Matrix

end MathlibExt.LinearAlgebra.Eigenspace.MulComm
