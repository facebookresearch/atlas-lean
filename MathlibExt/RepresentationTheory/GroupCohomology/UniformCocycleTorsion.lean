/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary.lean`
and
`P2M/Sol/S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

universe u v w

/-- In a finite module over a Noetherian ring, the powers of a fixed element
`t` that annihilate individual elements have a uniform exponent: some
`t ^ e` annihilates every `t`-power-torsion element. -/
private theorem exists_forall_pow_smul_eq_zero_of_isNoetherian
    {B : Type u} [CommRing B] [IsNoetherianRing B] {M : Type v} [AddCommGroup M]
    [Module B M] [Module.Finite B M] (t : B) :
    ∃ e : ℕ, ∀ x : M, (∃ k : ℕ, t ^ k • x = 0) → t ^ e • x = 0 := by
  haveI hN : IsNoetherian B M := isNoetherian_of_isNoetherianRing_of_finite B M
  let F : ℕ →o Submodule B M :=
    { toFun := fun k => Submodule.torsionBy B M (t ^ k)
      monotone' := fun k l hkl x hx => by
        rw [Submodule.mem_torsionBy_iff] at hx ⊢
        rw [← Nat.sub_add_cancel hkl, pow_add, mul_smul, hx, smul_zero] }
  obtain ⟨e, he⟩ := (monotone_stabilizes_iff_noetherian.2 hN) F
  refine ⟨e, fun x ⟨k, hk⟩ => ?_⟩
  have hx : x ∈ F (max k e) := F.monotone (le_max_left k e) ((Submodule.mem_torsionBy_iff _ _).2 hk)
  rw [← he (max k e) (le_max_right k e)] at hx
  exact (Submodule.mem_torsionBy_iff _ _).1 hx

namespace groupCohomology

/-- A uniform power of `t` kills every `t`-power-torsion class represented
by an additive `1`-cocycle for a finite group action.

Here `B` is a Noetherian ring, `R` is a finite `B`-module equipped with a
commuting action of a finite group `G`, and a cocycle is a map
`y : G → R` satisfying `y (g * h) = g • y h + y g`. If some power `t ^ k`
of `t` sends a cocycle `y` to a coboundary `g ↦ g • z - z`, then the
uniform power `t ^ e` (independent of `y`) already does so. This is not a
general vanishing statement for group cohomology: the eventual-coboundary
hypothesis on `y` is essential. -/
public theorem exists_forall_cocycle_pow_smul_eq_coboundary
    {B : Type u} [CommRing B] [IsNoetherianRing B] {R : Type v} [CommRing R] [Algebra B R]
    [Module.Finite B R] {G : Type w} [Group G] [Finite G] [MulSemiringAction G R]
    [SMulCommClass G B R] (t : B) :
    ∃ e : ℕ, ∀ y : G → R, (∀ g h : G, y (g * h) = g • y h + y g) →
      (∃ (k : ℕ) (z : R), ∀ g : G, t ^ k • y g = g • z - z) →
        ∃ z : R, ∀ g : G, t ^ e • y g = g • z - z := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let d : R →ₗ[B] (G → R) :=
    { toFun := fun z g => g • z - z
      map_add' := fun z z' => funext fun g => by
        change g • (z + z') - (z + z') = (g • z - z) + (g • z' - z')
        rw [smul_add]; abel
      map_smul' := fun b z => funext fun g => by
        change g • (b • z) - b • z = b • (g • z - z)
        rw [smul_sub, smul_comm] }
  obtain ⟨e, he⟩ :=
    exists_forall_pow_smul_eq_zero_of_isNoetherian (M := (G → R) ⧸ LinearMap.range d) t
  refine ⟨e, fun y _ ⟨k, z, hz⟩ => ?_⟩
  have hk : t ^ k • Submodule.Quotient.mk (p := LinearMap.range d) y = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.2 ⟨z, funext fun g => by
      change g • z - z = t ^ k • y g; exact (hz g).symm⟩
  have hke := he _ ⟨k, hk⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hke
  obtain ⟨z', hz'⟩ := LinearMap.mem_range.1 hke
  exact ⟨z', fun g => by have hg := congrFun hz' g; exact hg.symm⟩

end groupCohomology
