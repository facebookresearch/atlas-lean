/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Irreducibility prerequisites for implementing binary isometries on the spin space. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A semisimple module with only scalar endomorphisms has no proper
nonzero submodule. This uses an actual complementary projection. -/
theorem isSimpleModule_of_scalar_endomorphisms
    {R A V : Type*} [Field R] [Ring A] [AddCommGroup V]
    [Module R V] [Module A V] [Nontrivial V] [IsSemisimpleModule A V]
    (hscalar : ∀ f : V →ₗ[A] V, ∃ c : R, ∀ x, f x = c • x) :
    IsSimpleModule A V := by
  classical
  apply (isSimpleModule_iff A V).mpr
  refine ⟨fun p => or_iff_not_imp_left.mpr (fun hp => ?_)⟩
  obtain ⟨x, hx, hx0⟩ := p.ne_bot_iff.mp hp
  obtain ⟨q, hpq⟩ := exists_isCompl p
  obtain ⟨c, hc⟩ := hscalar (p.projection q hpq)
  have hcx : c • x = x := by
    rw [← hc]
    exact p.projection_apply_left hpq ⟨x, hx⟩
  have hc1 : c = 1 := (smul_left_injective R hx0) (hcx.trans (one_smul R x).symm)
  apply p.eq_top_iff'.mpr
  intro y
  have hy := p.projection_apply_mem hpq y
  rw [hc y, hc1, one_smul] at hy
  exact hy

/-- The already constructed linear spin representation, viewed as a monoid
representation into the algebra of linear endomorphisms. -/
noncomputable def spinLinearRepresentation : Representation ℝ Q SpinSpace where
  toFun q := (spinRepresentation q).toLinearMap
  map_one' := by rw [spinRepresentation.map_one]; rfl
  map_mul' q r := by rw [spinRepresentation.map_mul]; rfl

/-- The actual real Schrödinger representation is irreducible. Maschke
supplies complements, and the proved scalar commutant rules them out. -/
theorem spinLinearRepresentation_irreducible :
    Representation.IsIrreducible spinLinearRepresentation := by
  let : Finite Q := q_finite_coordinates
  let : NeZero (Nat.card Q : ℝ) := ⟨by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card Q ≠ 0)⟩
  let : Nontrivial spinLinearRepresentation.asModule :=
    spinLinearRepresentation.asModuleEquiv.symm.injective.nontrivial
  apply (Representation.irreducible_iff_isSimpleModule_asModule spinLinearRepresentation).mpr
  apply isSimpleModule_of_scalar_endomorphisms (R := ℝ)
  intro f
  let t := (Representation.IntertwiningMap.equivLinearMapAsModule
    spinLinearRepresentation spinLinearRepresentation).symm f
  obtain ⟨c, hc⟩ := spinRepresentation_commutant_linear_scalar t.toLinearMap
    (fun q x => Representation.IntertwiningMap.isIntertwining
      spinLinearRepresentation spinLinearRepresentation t q x)
  refine ⟨c, fun x => ?_⟩
  apply spinLinearRepresentation.asModuleEquiv.injective
  rw [map_smul]
  exact hc (spinLinearRepresentation.asModuleEquiv x)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
