/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed source port from TauCeti, commit62bbc0596dc3539d488232e4e924a338548ea0a9.
Original Apache 2.0 license and author credit are retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicGeometry/ResidueDegree.lean
Only module and namespace paths are adapted for Atlas.
-/

public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue degrees of scheme morphisms

This file develops the elementary functorial API for Mathlib's
`AlgebraicGeometry.Scheme.Hom.residueDegree`. For a scheme morphism `f : X ⟶ Y` and a point
`x : X`, this is the degree `[κ(x) : κ(f(x))]`, with value zero when the field extension is
infinite.

The main result is the tower law `residueDegree_comp`. It identifies the residue degree of a
composite with the product of the two successive residue degrees. We also characterize when a
residue degree is positive and when it is one, and show that a morphism surjective on stalks, such
as a closed immersion, has residue degree one everywhere. These facts supply the residue-field
weights used in degree and pushforward constructions.

The construction follows the residue-degree convention for pushforward of cycles in the
[Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4). The proofs reuse
Mathlib's residue-field maps and the field-extension tower law `Module.finrank_mul_finrank`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}}

/-- The residue degree of a composite is the product of the successive residue degrees:
`[κ(x) : κ(g(f(x)))] = [κ(f(x)) : κ(g(f(x)))] [κ(x) : κ(f(x))]`. -/
@[simp]
theorem residueDegree_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  let : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq' <| by
      rw [RingHom.algebraMap_toAlgebra]
      exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x)
  rw [residueDegree]
  exact (Module.finrank_mul_finrank (Z.residueField (g (f x)))
    (Y.residueField (f x)) (X.residueField x)).symm

/-- A residue degree is positive exactly when the associated residue-field extension is finite. -/
theorem residueDegree_pos_iff (f : X ⟶ Y) (x : X) :
    0 < f.residueDegree x ↔ (f.residueFieldMap x).hom.Finite := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [residueDegree, RingHom.Finite]
  exact ⟨fun h ↦ Module.finite_of_finrank_pos h, fun _ ↦ Module.finrank_pos⟩

/-- A residue degree is nonzero exactly when the associated residue-field extension is finite. -/
theorem residueDegree_ne_zero_iff (f : X ⟶ Y) (x : X) :
    f.residueDegree x ≠ 0 ↔ (f.residueFieldMap x).hom.Finite := by
  rw [← residueDegree_pos_iff, Nat.pos_iff_ne_zero]

/-- A residue-field map is bijective exactly when its residue degree is one. -/
theorem residueDegree_eq_one_iff (f : X ⟶ Y) (x : X) :
    f.residueDegree x = 1 ↔ Function.Bijective (f.residueFieldMap x) := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [residueDegree, Algebra.finrank_eq_one_iff_bijective_algebraMap,
    RingHom.algebraMap_toAlgebra]

/-- A morphism which is surjective on stalks, for instance a closed immersion, an open immersion
or an isomorphism, has residue degree one at every point: its residue-field maps are surjective
field homomorphisms. -/
@[simp]
theorem residueDegree_eq_one_of_surjectiveOnStalks (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    f.residueDegree x = 1 := by
  refine (residueDegree_eq_one_iff f x).mpr ⟨(f.residueFieldMap x).hom.injective, fun z ↦ ?_⟩
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, rfl⟩ := f.stalkMap_surjective x s
  refine ⟨Y.residue (f x) t, ?_⟩
  rw [← CategoryTheory.comp_apply, Scheme.residue_residueFieldMap, CategoryTheory.comp_apply]

end AlgebraicGeometry.Scheme.Hom
