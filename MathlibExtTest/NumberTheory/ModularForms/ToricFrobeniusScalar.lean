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

-- The dimension-two hypothesis matters: in dimension one the same toric,
-- scalar and determinant data hold for `q = 2` over `ℝ`, while the
-- conclusion `(2 : ℝ) = 0 ∨ (2 : ℝ) = 1` is false.
example : ¬ ((2 : ℝ) = 0 ∨ (2 : ℝ) = 1) := by norm_num
