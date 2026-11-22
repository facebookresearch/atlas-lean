/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.GroupCohomology.UniformCocycleTorsion

@[expose] public section

universe u v w

-- Consumer with the original binders.
example {B : Type u} [CommRing B] [IsNoetherianRing B] {R : Type v} [CommRing R] [Algebra B R]
    [Module.Finite B R] {G : Type w} [Group G] [Finite G] [MulSemiringAction G R]
    [SMulCommClass G B R] (t : B) :
    ∃ e : ℕ, ∀ y : G → R, (∀ g h : G, y (g * h) = g • y h + y g) →
      (∃ (k : ℕ) (z : R), ∀ g : G, t ^ k • y g = g • z - z) →
        ∃ z : R, ∀ g : G, t ^ e • y g = g • z - z :=
  groupCohomology.exists_forall_cocycle_pow_smul_eq_coboundary t

-- Boundary case: the zero cocycle is a coboundary (with `z = 0`), so the
-- uniform exponent works for it with witness `0`.
example {B : Type u} [CommRing B] [IsNoetherianRing B] {R : Type v} [CommRing R] [Algebra B R]
    [Module.Finite B R] {G : Type w} [Group G] [Finite G] [MulSemiringAction G R]
    [SMulCommClass G B R] (t : B) :
    ∃ e : ℕ, ∃ z : R, ∀ g : G, t ^ e • (0 : G → R) g = g • z - z := by
  obtain ⟨e, he⟩ := groupCohomology.exists_forall_cocycle_pow_smul_eq_coboundary
    (B := B) (R := R) (G := G) t
  obtain ⟨z, hz⟩ := he 0 (fun g h => by simp) ⟨0, 0, fun g => by simp⟩
  exact ⟨e, z, hz⟩
