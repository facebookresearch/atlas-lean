/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import MathlibExt.NumberTheory.ModularForms.ToricFrobeniusScalar

@[expose] public section

-- Consumer with the original binders.
example {G : Type*} [Group G]
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [DistribMulAction G V] [SMulCommClass G k V]
    {R : Type*} [CommRing R]
    {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]
    {q : ℕ} {φ : G} {𝒯 : Submodule R J}
    (hfrob : ModularCurve.ToricFrobeniusSq q φ 𝒯)
    (ι : V →+ J) (hinj : Function.Injective ι)
    (hequiv : ∀ g : G, ∀ v : V, ι (g • v) = g • ι v)
    (hsub : ∀ v : V, ι v ∈ 𝒯)
    (lam : k) (hscalar : ∀ v : V, φ • v = lam • v)
    (hrank : Module.finrank k V = 2)
    (hdet : LinearMap.det (DistribSMul.toLinearMap k V φ) = (q : k)) :
    (q : k) = 0 ∨ (q : k) = 1 :=
  ModularCurve.mazurPrinciple_toric_exclusion_of_scalar hfrob ι hinj hequiv hsub
    lam hscalar hrank hdet

-- The dimension-two hypothesis matters: in dimension one, with
-- `G = ℝˣ`, `φ = 2`, `V = J = ℝ`, `𝒯 = ⊤`, `ι = id` and scalar `2`, the
-- toric-square, equivariance, scalar and determinant hypotheses all hold
-- for `q = 2`, the rank is `1` (not `2`), and the conclusion is false.
example :
    ModularCurve.ToricFrobeniusSq (R := ℝ) (J := ℝ) 2
        (Units.mk0 (2 : ℝ) (by norm_num))
        (⊤ : Submodule ℝ ℝ) ∧
      Function.Injective (AddMonoidHom.id ℝ : ℝ →+ ℝ) ∧
      (∀ g : ℝˣ, ∀ v : ℝ, (AddMonoidHom.id ℝ : ℝ →+ ℝ) (g • v) =
        g • (AddMonoidHom.id ℝ : ℝ →+ ℝ) v) ∧
      (∀ v : ℝ, (AddMonoidHom.id ℝ : ℝ →+ ℝ) v ∈ (⊤ : Submodule ℝ ℝ)) ∧
      (∀ v : ℝ, (Units.mk0 (2 : ℝ) (by norm_num)) • v = (2 : ℝ) • v) ∧
      LinearMap.det (DistribSMul.toLinearMap ℝ ℝ
        (Units.mk0 (2 : ℝ) (by norm_num))) = (2 : ℝ) ∧
      Module.finrank ℝ ℝ = 1 ∧ ¬ ((2 : ℝ) = 0 ∨ (2 : ℝ) = 1) := by
  have hdet : LinearMap.det (DistribSMul.toLinearMap ℝ ℝ
      (Units.mk0 (2 : ℝ) (by norm_num))) = (2 : ℝ) := by
    have hmap : DistribSMul.toLinearMap ℝ ℝ
        (Units.mk0 (2 : ℝ) (by norm_num)) =
        (2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
      ext v
      simp [DistribSMul.toLinearMap_apply, smul_eq_mul]
    rw [hmap]
    simp
  refine ⟨?_, Function.injective_id, ?_, fun _ => Submodule.mem_top, ?_, hdet,
    Module.finrank_self ℝ, by norm_num⟩
  · intro x _
    simp [smul_eq_mul, zsmul_eq_mul]
    ring
  · intro g v
    rfl
  · intro v
    simp [smul_eq_mul]
