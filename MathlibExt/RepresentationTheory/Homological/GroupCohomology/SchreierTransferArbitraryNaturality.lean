/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryDifferential
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Coefficient naturality of Schreier transfer

Let H ≤ G have finite index and let T be a right transversal. For a G-equivariant k-linear map
φ : A → B, postcomposition of H-cochains with φ commutes with every degree-n Schreier
transfer: φ(cor_Tⁿ(f)) = cor_Tⁿ(φ∘f).

This square commutes as a map of cochain complexes and after passing to Hⁿ. Thus the fixed-
transversal transfers form natural transformations in the G-representation, both on
inhomogeneous cochains and on group cohomology.
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

/-- Finite representatives for coefficient-naturality sums.

A finite-index right transversal is finitely enumerated for the coefficient-map and transfer
sums. -/
noncomputable local instance corestrictionArbitraryNaturalityFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Coefficient maps commute with each tuple transfer.

For a G-equivariant linear φ : A → B, every H-cochain f and every degree n satisfy φ∘cor_Tⁿ(f)
= cor_Tⁿ(φ∘f). -/
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

/-- The coefficient square for transfer cochain maps.

The transfer cochain map for A followed by the G-coefficient map of φ equals the restricted
H-coefficient map of φ followed by the transfer cochain map for B. -/
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
/-- The coefficient square for arbitrary-degree cohomology transfer.

In every degree n, the transfer for A followed by Hⁿ(G,φ) equals Hⁿ(H,φ|H) followed by the
transfer for B. -/
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

/-- Elementwise coefficient naturality of cohomology transfer.

For x ∈ Hⁿ(H,A|H), mapping its transferred class by φ gives the transfer for B of the class
obtained by the restricted coefficient map φ|H. -/
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

/-- The transfer natural transformation on cochain complexes.

For a fixed finite right transversal T, the cochain maps are natural from restriction to H
followed by H-cochains to the G-cochain functor. -/
noncomputable def corestrictionCochainsNatTransOfRightTransversal
    (T : H.RightTransversal) [H.FiniteIndex] :
    Rep.resFunctor (Subgroup.subtype H) ⋙
        groupCohomology.cochainsFunctor k H ⟶
      groupCohomology.cochainsFunctor k G where
  app A := corestrictionCochains A T
  naturality {_A _B} phi :=
    (corestrictionCochains_naturality phi T).symm

/-- The transfer natural transformation in a cohomology degree.

For fixed T and n, the transfers define a natural transformation from Hⁿ(H,A|H) to Hⁿ(G,A) as
A varies through G-representations. -/
noncomputable def corestrictionNatTransOfRightTransversal
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    Rep.resFunctor (Subgroup.subtype H) ⋙
        groupCohomology.functor k H n ⟶
      groupCohomology.functor k G n where
  app A := corestrictionOfRightTransversal A T n
  naturality {_A _B} phi :=
    (corestrictionOfRightTransversal_naturality phi T n).symm

end groupCohomology
