/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NeronModelGroupLaw
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Tests for the group law on a Néron model

A Néron model of an abelian variety over a discrete valuation ring carries a commutative group
law extending that of the generic fibre, and any two such laws agree.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.NeronModelGroupLaw

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.NeronModels
open MathlibExt.AlgebraicGeometry.SemistableModels

universe u

/-- The group structure of the Néron model of an abelian variety over a discrete valuation
ring. -/
example (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K] (A : AbelianScheme (Spec (.of K)))
    (N : NeronModel R K A.model) : N.GroupStructure :=
  N.groupStructure

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Spec (.of K))} [GrpObj A]

/-- The group law extends that of the generic fibre. -/
example (N : NeronModel R K A) : letI := N.grpObj; IsMonHom N.genericIso.hom :=
  N.isMonHom_genericIso_grpObj

/-- Every group law on the model extending that of `A` is `NeronModel.grpObj`. -/
example (N : NeronModel R K A) (g : GrpObj N.model)
    (hg : letI := g; IsMonHom N.genericIso.hom) : g = N.grpObj :=
  N.eq_grpObj_of_isMonHom g hg

/-- The `GroupStructure` built from a commutative `A` has the group law `NeronModel.grpObj`. -/
example [IsCommMonObj A] (N : NeronModel R K A) : N.groupStructure.toGrpObj = N.grpObj := rfl

/-- Existence, uniqueness and commutativity of the group law together, read off for a
commutative `A`. -/
example [IsCommMonObj A] (N : NeronModel R K A) :
    ∃ g : GrpObj N.model, (letI := g; IsMonHom N.genericIso.hom) ∧
      (letI := g; IsCommMonObj N.model) := by
  obtain ⟨g, ⟨hg, hc⟩, -⟩ := N.existsUnique_grpObj
  exact ⟨g, hg, hc inferInstance⟩

end MathlibExtTest.AlgebraicGeometry.NeronModelGroupLaw
