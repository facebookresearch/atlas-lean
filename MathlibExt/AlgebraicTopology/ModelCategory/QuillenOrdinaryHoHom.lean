/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory

/-!
# Actual ordinary Ho Hom functions of a Quillen adjunction

Good cylinders and path objects are sent through the actual Quillen pair.
Brown's lemma proves that their selected retractions remain weak
equivalences. The original adjunct functions therefore descend to the
homotopy quotients. The fundamental lemma then constructs the two complete
ordinary Ho functions for cofibrant sources and fibrant targets.

The original adjunction, model structures, and canonical localizations are
kept. No Hom bijection or derived adjunction is supplied as an extra input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u₁ u₂ v₁ v₂

open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.QuillenOrdinaryHoHom

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [Adjunction.IsQuillenAdjunction adj]

local notation "HC" => CategoryTheory.MorphismProperty.Q (weakEquivalences C)
local notation "HD" => CategoryTheory.MorphismProperty.Q (weakEquivalences D)

/-- The right adjoint sends the actual good path to a path object with the original maps. -/
def rightPath {Y : D} [IsFibrant Y] (P : PathObject Y) [P.IsGood] :
    PathObject (R.obj Y) where
  toPrepathObject := P.toPrepathObject.map R
  weakEquivalence_ι :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := adj) P.ι

/-- The left adjoint sends the actual good cylinder to a cylinder with the original maps. -/
def leftCylinder {X : C} [IsCofibrant X] (P : Cylinder X) [P.IsGood] :
    Cylinder (L.obj X) where
  toPrecylinder := P.toPrecylinder.map L
  weakEquivalence_π :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adj) P.π

/-- The original forward adjunct sends actual left homotopies to actual left homotopies. -/
theorem adjunct_leftHomotopyRel {X : C} [IsCofibrant X] {Y : D} [IsFibrant Y]
    {f g : L.obj X ⟶ Y} (h : LeftHomotopyRel f g) :
    LeftHomotopyRel (adj.homEquiv X Y f) (adj.homEquiv X Y g) := by
  let : IsCofibrant (L.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  obtain ⟨P, hP, ⟨h⟩⟩ := h.rightHomotopyRel.exists_good_pathObject
  let : P.IsGood := hP
  let h' : (rightPath adj P).RightHomotopy
      (adj.homEquiv X Y f) (adj.homEquiv X Y g) :=
    { h := adj.homEquiv X P.P h.h
      h₀ := by
        change adj.homEquiv X P.P h.h ≫ R.map P.p₀ = adj.homEquiv X Y f
        rw [← adj.homEquiv_naturality_right, h.h₀]
      h₁ := by
        change adj.homEquiv X P.P h.h ≫ R.map P.p₁ = adj.homEquiv X Y g
        rw [← adj.homEquiv_naturality_right, h.h₁] }
  let : IsFibrant (R.obj Y) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) inferInstance
  exact h'.rightHomotopyRel.leftHomotopyRel

/-- The original inverse adjunct sends actual left homotopies through a good cylinder. -/
theorem inverseAdjunct_leftHomotopyRel {X : C} [IsCofibrant X] {Y : D}
    {f g : X ⟶ R.obj Y} (h : LeftHomotopyRel f g) :
    LeftHomotopyRel ((adj.homEquiv X Y).symm f) ((adj.homEquiv X Y).symm g) := by
  obtain ⟨P, hP, ⟨h⟩⟩ := h.exists_good_cylinder
  let : P.IsGood := hP
  let h' : (leftCylinder adj P).LeftHomotopy
      ((adj.homEquiv X Y).symm f) ((adj.homEquiv X Y).symm g) :=
    { h := (adj.homEquiv P.I Y).symm h.h
      h₀ := by
        change L.map P.i₀ ≫ (adj.homEquiv P.I Y).symm h.h =
          (adj.homEquiv X Y).symm f
        rw [← adj.homEquiv_naturality_left_symm, h.h₀]
      h₁ := by
        change L.map P.i₁ ≫ (adj.homEquiv P.I Y).symm h.h =
          (adj.homEquiv X Y).symm g
        rw [← adj.homEquiv_naturality_left_symm, h.h₁] }
  exact h'.leftHomotopyRel

/-- The complete homotopy quotient equivalence uses the two original adjunct functions. -/
def classEquiv (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y] :
    LeftHomotopyClass (L.obj X) Y ≃ LeftHomotopyClass X (R.obj Y) where
  toFun := Quot.lift (fun f => LeftHomotopyClass.mk (adj.homEquiv X Y f))
    (fun _ _ h => LeftHomotopyClass.sound (adjunct_leftHomotopyRel adj h))
  invFun := Quot.lift (fun f => LeftHomotopyClass.mk ((adj.homEquiv X Y).symm f))
    (fun _ _ h => LeftHomotopyClass.sound (inverseAdjunct_leftHomotopyRel adj h))
  left_inv f := by
    obtain ⟨f, rfl⟩ := LeftHomotopyClass.mk_surjective f
    change LeftHomotopyClass.mk ((adj.homEquiv X Y).symm (adj.homEquiv X Y f)) = _
    rw [Equiv.symm_apply_apply]
  right_inv f := by
    obtain ⟨f, rfl⟩ := LeftHomotopyClass.mk_surjective f
    change LeftHomotopyClass.mk (adj.homEquiv X Y ((adj.homEquiv X Y).symm f)) = _
    rw [Equiv.apply_symm_apply]

/-- The entire forward quotient function retains the actual original representative adjunct. -/
theorem classEquiv_mk (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y]
    (f : L.obj X ⟶ Y) :
    classEquiv adj X Y (LeftHomotopyClass.mk f) =
      LeftHomotopyClass.mk (adj.homEquiv X Y f) := rfl

/-- The entire inverse quotient function retains the actual inverse representative adjunct. -/
theorem classEquiv_symm_mk (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y]
    (f : X ⟶ R.obj Y) :
    (classEquiv adj X Y).symm (LeftHomotopyClass.mk f) =
      LeftHomotopyClass.mk ((adj.homEquiv X Y).symm f) := rfl

/-- The actual canonical localizations obtain the complete Hom equivalence from the quotients. -/
def homEquiv (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y] :
    ((HD).obj (L.obj X) ⟶ (HD).obj Y) ≃ ((HC).obj X ⟶ (HC).obj (R.obj Y)) := by
  let : IsCofibrant (L.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  let : IsFibrant (R.obj Y) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) inferInstance
  let eD := Equiv.ofBijective (leftHomotopyClassToHom HD)
    (bijective_leftHomotopyClassToHom HD (L.obj X) Y)
  let eC := Equiv.ofBijective (leftHomotopyClassToHom HC)
    (bijective_leftHomotopyClassToHom HC X (R.obj Y))
  exact eD.symm.trans ((classEquiv adj X Y).trans eC)

/-- Every represented Ho arrow has the original full forward adjunct. -/
theorem homEquiv_map (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y]
    (f : L.obj X ⟶ Y) :
    homEquiv adj X Y ((HD).map f) = (HC).map (adj.homEquiv X Y f) := by
  let : IsCofibrant (L.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  let : IsFibrant (R.obj Y) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) inferInstance
  let e := Equiv.ofBijective (leftHomotopyClassToHom HD)
    (bijective_leftHomotopyClassToHom HD (L.obj X) Y)
  have he : e.symm ((HD).map f) = LeftHomotopyClass.mk f := by
    calc
      e.symm ((HD).map f) = e.symm (e (LeftHomotopyClass.mk f)) := rfl
      _ = LeftHomotopyClass.mk f := e.symm_apply_apply _
  change leftHomotopyClassToHom HC (classEquiv adj X Y (e.symm ((HD).map f))) = _
  rw [he, classEquiv_mk, leftHomotopyClassToHom_mk]

/-- Every represented Ho arrow has the original full inverse adjunct. -/
theorem homEquiv_symm_map (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y]
    (f : X ⟶ R.obj Y) :
    (homEquiv adj X Y).symm ((HC).map f) = (HD).map ((adj.homEquiv X Y).symm f) := by
  apply (homEquiv adj X Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_map, Equiv.apply_symm_apply]

/-- The whole forward Hom function is natural in every actual target map. -/
theorem homEquiv_naturality_right (X : C) [IsCofibrant X]
    {Y Y' : D} [IsFibrant Y] [IsFibrant Y']
    (f : (HD).obj (L.obj X) ⟶ (HD).obj Y) (g : Y ⟶ Y') :
    homEquiv adj X Y' (f ≫ (HD).map g) =
      homEquiv adj X Y f ≫ (HC).map (R.map g) := by
  let : IsCofibrant (L.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization HD (L.obj X) Y f
  rw [← (HD).map_comp, homEquiv_map, homEquiv_map,
    adj.homEquiv_naturality_right, (HC).map_comp]

/-- The whole forward Hom function is natural in every actual cofibrant coefficient map. -/
theorem homEquiv_naturality_left {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (Y : D) [IsFibrant Y] (f : X' ⟶ X) (g : (HD).obj (L.obj X) ⟶ (HD).obj Y) :
    homEquiv adj X' Y ((HD).map (L.map f) ≫ g) =
      (HC).map f ≫ homEquiv adj X Y g := by
  let : IsCofibrant (L.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization HD (L.obj X) Y g
  rw [← (HD).map_comp, homEquiv_map, homEquiv_map,
    adj.homEquiv_naturality_left, (HC).map_comp]

/-- The complete inverse Hom function is natural in every actual target map. -/
theorem homEquiv_symm_naturality_right (X : C) [IsCofibrant X]
    {Y Y' : D} [IsFibrant Y] [IsFibrant Y']
    (f : (HC).obj X ⟶ (HC).obj (R.obj Y)) (g : Y ⟶ Y') :
    (homEquiv adj X Y').symm (f ≫ (HC).map (R.map g)) =
      (homEquiv adj X Y).symm f ≫ (HD).map g := by
  apply (homEquiv adj X Y').injective
  rw [Equiv.apply_symm_apply, homEquiv_naturality_right, Equiv.apply_symm_apply]

/-- The complete inverse Hom function is natural in every actual cofibrant coefficient map. -/
theorem homEquiv_symm_naturality_left {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (Y : D) [IsFibrant Y] (f : X' ⟶ X) (g : (HC).obj X ⟶ (HC).obj (R.obj Y)) :
    (homEquiv adj X' Y).symm ((HC).map f ≫ g) =
      (HD).map (L.map f) ≫ (homEquiv adj X Y).symm g := by
  apply (homEquiv adj X' Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_naturality_left, Equiv.apply_symm_apply]

/-- The actual unit is the forward Ho adjunct of the entire identity map. -/
theorem homEquiv_unit (X : C) [IsCofibrant X] [IsFibrant (L.obj X)] :
    homEquiv adj X (L.obj X) (𝟙 _) = (HC).map (adj.unit.app X) := by
  rw [← (HD).map_id, homEquiv_map, adj.homEquiv_id]

/-- The actual counit is the inverse Ho adjunct of the entire identity map. -/
theorem homEquiv_counit (Y : D) [IsFibrant Y] [IsCofibrant (R.obj Y)] :
    (homEquiv adj (R.obj Y) Y).symm (𝟙 _) = (HD).map (adj.counit.app Y) := by
  rw [← (HC).map_id, homEquiv_symm_map, adj.homEquiv_symm_id]

end HomotopicalAlgebra.QuillenOrdinaryHoHom
