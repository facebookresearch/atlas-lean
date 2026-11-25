/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryDifferential
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Coefficient naturality of arbitrary Schreier transfer

The chosen-transversal Schreier transfer commutes with morphisms of
coefficients on arbitrary inhomogeneous cochains, as a map of cochain
complexes, and on group cohomology in every degree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance corestrictionArbitraryNaturalityFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Mapping coefficients commutes with arbitrary-degree chosen-transversal
Schreier transfer on inhomogeneous cochains. -/
theorem corestrictionCochain_naturality
    {A B : Rep k G} (phi : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin n → H) → A) :
    (fun g ↦ phi.hom (corestrictionCochain A T n f g)) =
      corestrictionCochain B T n (fun h ↦ phi.hom (f h)) := by
  funext g
  rw [corestrictionCochain_apply, corestrictionCochain_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Rep.hom_comm_apply phi (t : G)⁻¹ (f (T.schreierFactorTuple t g))

/-- The arbitrary-degree chosen-transversal transfer is natural as a map of
inhomogeneous cochain complexes. -/
theorem corestrictionCochains_naturality
    {A B : Rep k G} (phi : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] :
    corestrictionCochains A T ≫
        groupCohomology.cochainsMap (MonoidHom.id G) phi =
      groupCohomology.cochainsMap (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map phi) ≫
        corestrictionCochains B T := by
  ext n f g
  exact congrFun (corestrictionCochain_naturality phi T n f) g

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary-degree chosen-transversal corestriction is natural under a
morphism of coefficient representations. -/
theorem corestrictionOfRightTransversal_naturality
    {A B : Rep k G} (phi : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    corestrictionOfRightTransversal A T n ≫
        groupCohomology.map (MonoidHom.id G) phi n =
      groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map phi) n ≫
        corestrictionOfRightTransversal B T n := by
  rw [corestrictionOfRightTransversal,
    corestrictionOfRightTransversal]
  exact HomologicalComplex.homologyMap_square
    (corestrictionCochains_naturality phi T) n

/-- Elementwise coefficient naturality of arbitrary-degree
chosen-transversal corestriction. -/
theorem corestrictionOfRightTransversal_naturality_apply
    {A B : Rep k G} (phi : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (x : groupCohomology (Rep.res (Subgroup.subtype H) A) n) :
    groupCohomology.map (MonoidHom.id G) phi n
        (corestrictionOfRightTransversal A T n x) =
      corestrictionOfRightTransversal B T n
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map phi) n x) := by
  exact ConcreteCategory.congr_hom
    (corestrictionOfRightTransversal_naturality phi T n) x

/-- A chosen right transversal packages arbitrary Schreier transfer as a
natural transformation from restricted-coefficient cochains to ambient
cochains. -/
noncomputable def corestrictionCochainsNatTransOfRightTransversal
    (T : H.RightTransversal) [H.FiniteIndex] :
    Rep.resFunctor (Subgroup.subtype H) ⋙
        groupCohomology.cochainsFunctor k H ⟶
      groupCohomology.cochainsFunctor k G where
  app A := corestrictionCochains A T
  naturality {_A _B} phi :=
    (corestrictionCochains_naturality phi T).symm

/-- In each degree, a chosen right transversal packages arbitrary
corestriction as a natural transformation in the coefficient
representation. -/
noncomputable def corestrictionNatTransOfRightTransversal
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    Rep.resFunctor (Subgroup.subtype H) ⋙
        groupCohomology.functor k H n ⟶
      groupCohomology.functor k G n where
  app A := corestrictionOfRightTransversal A T n
  naturality {_A _B} phi :=
    (corestrictionOfRightTransversal_naturality phi T n).symm

end groupCohomology
