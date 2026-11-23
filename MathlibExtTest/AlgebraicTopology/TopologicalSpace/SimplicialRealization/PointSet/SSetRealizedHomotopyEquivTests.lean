/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv

/-!
# Realized homotopy equivalence clients

Direct universe-zero clients of `SSet.realizedHomotopyEquiv`: its exact
`ContinuousMap.HomotopyEquiv` type plus forward/inverse realized maps, with all
homotopy arguments explicit.

Requires both simplicial homotopies `Hleft` and `Hright`.

Nonclaims: no homeomorphism, weak equivalence, Waldhausen additivity, or
ExtStage opposite homotopy content.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped Simplicial

noncomputable section

namespace SSet

example (X Y : SSet.{0}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj X) (SSet.toTop.obj Y) :=
  SSet.realizedHomotopyEquiv X Y f g Hleft Hright

example (X Y : SSet.{0}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑(SSet.realizedHomotopyEquiv X Y f g Hleft Hright) =
      ⇑(SSet.toTop.map f).hom :=
  SSet.coe_realizedHomotopyEquiv X Y f g Hleft Hright

example (X Y : SSet.{0}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑((SSet.realizedHomotopyEquiv X Y f g Hleft Hright).symm) =
      ⇑(SSet.toTop.map g).hom :=
  SSet.coe_symm_realizedHomotopyEquiv X Y f g Hleft Hright

noncomputable def realizationProductsTestsReflHomotopy
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.Homotopy f f := by
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm f)
    (SSet.RelativeMorphism.botEquiv.symm f)
  exact SSet.RelativeMorphism.Homotopy.refl _

/-- Exact symbolic-universe type of the realized homotopy map. -/
example (X Y : SSet.{u}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj Y :=
  SSet.realizeHomotopyMap X Y f g H

/-- The realized homotopy starts at realized `f`. -/
theorem mapZero_symbolic
    (X Y : SSet.{u}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
        (𝟙 (SSet.toTop.obj X)) ≫
      SSet.realizeHomotopyMap X Y f g H =
    SSet.toTop.map f :=
  SSet.realizeHomotopyMap_zero X Y f g H

/-- The realized homotopy ends at realized `g`. -/
theorem mapOne_symbolic
    (X Y : SSet.{u}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
        (𝟙 (SSet.toTop.obj X)) ≫
      SSet.realizeHomotopyMap X Y f g H =
    SSet.toTop.map g :=
  SSet.realizeHomotopyMap_one X Y f g H

/-- Packaged realized homotopy at a symbolic universe. -/
noncomputable def homotopy_symbolic
    (X Y : SSet.{u}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    ContinuousMap.Homotopy
      (SSet.toTop.map f).hom (SSet.toTop.map g).hom :=
  SSet.realizeHomotopy X Y f g H

/-- Realized homotopy equivalence at a symbolic universe. -/
noncomputable def homotopyEquiv_symbolic
    (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj X) (SSet.toTop.obj Y) :=
  SSet.realizedHomotopyEquiv X Y f g Hleft Hright

/-- The forward coercion is realized `f`. -/
theorem homotopyEquiv_coe_symbolic
    (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑(SSet.realizedHomotopyEquiv X Y f g Hleft Hright) =
      ⇑(SSet.toTop.map f).hom := by
  simp

/-- The backward coercion is realized `g`. -/
theorem homotopyEquiv_symm_coe_symbolic
    (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑((SSet.realizedHomotopyEquiv X Y f g Hleft Hright).symm) =
      ⇑(SSet.toTop.map g).hom := by
  simp

/-- Exact universe-one type of the realized homotopy map. -/
example (X Y : SSet.{1}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    TopCat.I.{1} ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj Y :=
  SSet.realizeHomotopyMap X Y f g H

/-- Universe-one zero endpoint. -/
theorem mapZero_u1
    (X Y : SSet.{1}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    Limits.prod.lift (TopCat.const (0 : TopCat.I.{1}))
        (𝟙 (SSet.toTop.obj X)) ≫
      SSet.realizeHomotopyMap X Y f g H =
    SSet.toTop.map f :=
  SSet.realizeHomotopyMap_zero X Y f g H

/-- Universe-one one endpoint. -/
theorem mapOne_u1
    (X Y : SSet.{1}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    Limits.prod.lift (TopCat.const (1 : TopCat.I.{1}))
        (𝟙 (SSet.toTop.obj X)) ≫
      SSet.realizeHomotopyMap X Y f g H =
    SSet.toTop.map g :=
  SSet.realizeHomotopyMap_one X Y f g H

/-- Packaged realized homotopy at universe one. -/
noncomputable def homotopy_u1
    (X Y : SSet.{1}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    ContinuousMap.Homotopy
      (SSet.toTop.map f).hom (SSet.toTop.map g).hom :=
  SSet.realizeHomotopy X Y f g H

/-- Realized homotopy equivalence at universe one. -/
noncomputable def homotopyEquiv_u1
    (X Y : SSet.{1}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj X) (SSet.toTop.obj Y) :=
  SSet.realizedHomotopyEquiv X Y f g Hleft Hright

/-- Universe-one forward coercion. -/
theorem homotopyEquiv_coe_u1
    (X Y : SSet.{1}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑(SSet.realizedHomotopyEquiv X Y f g Hleft Hright) =
      ⇑(SSet.toTop.map f).hom := by
  simp

/-- Universe-one backward coercion. -/
theorem homotopyEquiv_symm_coe_u1
    (X Y : SSet.{1}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑((SSet.realizedHomotopyEquiv X Y f g Hleft Hright).symm) =
      ⇑(SSet.toTop.map g).hom := by
  simp

/-- Finite-right comparison obtained by swapping the reviewed finite-left result. -/
theorem arbitraryFinite_symbolic
    (Y K : SSet.{u}) [K.Finite] :
    IsIso (Limits.prodComparison SSet.toTop Y K) := by
  let _ : IsIso (Limits.prodComparison SSet.toTop K Y) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary K Y
  exact SSet.isIso_prodComparison_swap K Y

/-- Universe-one standard-simplex-right comparison. -/
theorem arbitraryStandardSimplexRight_u1 (Y : SSet.{1}) :
    IsIso (Limits.prodComparison SSet.toTop Y
      (Δ[2] : SSet.{1})) := by
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[2] : SSet.{1}) Y) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  exact SSet.isIso_prodComparison_swap (Δ[2] : SSet.{1}) Y

/-- A reflexive simplicial homotopy realizes to a constant-in-time homotopy. -/
noncomputable def constantRepresentative_symbolic
    (X Y : SSet.{u}) (f : X ⟶ Y) :
    ContinuousMap.Homotopy
      (SSet.toTop.map f).hom (SSet.toTop.map f).hom :=
  SSet.realizeHomotopy X Y f f
    (realizationProductsTestsReflHomotopy f)

noncomputable def realizationProductsTestsIdentityCompositeHomotopy
    (X : SSet.{u}) :
    SSet.Homotopy ((𝟙 X) ≫ 𝟙 X) (𝟙 X) := by
  rw [Category.id_comp]
  exact realizationProductsTestsReflHomotopy (𝟙 X)

/-- Identity maps realize to a homotopy equivalence. -/
noncomputable def identityEquiv_symbolic
    (X : SSet.{u}) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj X) (SSet.toTop.obj X) :=
  SSet.realizedHomotopyEquiv X X (𝟙 X) (𝟙 X)
    (realizationProductsTestsIdentityCompositeHomotopy X)
    (realizationProductsTestsIdentityCompositeHomotopy X)

/-- Identity equivalence at universe one. -/
noncomputable def identityEquiv_u1
    (X : SSet.{1}) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj X) (SSet.toTop.obj X) :=
  identityEquiv_symbolic X

/-- The identity equivalence coerces to the realized identity map. -/
theorem identityEquiv_coe_symbolic (X : SSet.{u}) :
    ⇑(identityEquiv_symbolic X) =
      ⇑(SSet.toTop.map (𝟙 X)).hom := by
  simp [identityEquiv_symbolic]

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.isIso_prodComparison_deltaGenerated_finite_arbitrary

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.bkHocolimMap_mem_realizationWeakEquivalences

/-- error: Unknown identifier -/
#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.weakEquivalence_map_of_isPushouts_of_cofibrant

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isPushout_mono

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isColimit_nat_mono

#print axioms SSet.realizeHomotopyMap
#print axioms SSet.realizeHomotopyMap_zero
#print axioms SSet.realizeHomotopyMap_one
#print axioms SSet.realizeHomotopy
#print axioms SSet.realizedHomotopyEquiv
#print axioms SSet.coe_realizedHomotopyEquiv
#print axioms SSet.coe_symm_realizedHomotopyEquiv

end SSet
