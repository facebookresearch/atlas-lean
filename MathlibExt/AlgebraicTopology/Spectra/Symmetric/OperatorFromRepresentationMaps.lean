/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorToExternal
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorRepresentationMaps

/-!
# Reconstructing every original ordinary module morphism

Whole operator transformations are natural on every original index arrow
and every identity-labelled coefficient. These complete maps reconstruct
the original ordinary sphere-module morphisms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] [MonoidalClosed V]
  {T : V}

/-- Every whole operator transformation is natural at every original finite-index arrow. -/
theorem representationMap_index {X Y : Representation T} (f : X ⟶ Y) {n k : I} (g : n ⟶ k) :
    (ordinaryDiagram X).map g ≫ representationMapComponent f k =
      representationMapComponent f n ≫ (ordinaryDiagram Y).map g := by
  let A := representationObject X n
  let B := representationObject Y n
  let fn : A ⟶ B := representationMapComponent f n
  let fk : representationObject X k ⟶ representationObject Y k := representationMapComponent f k
  let rx : A ⟶ representationObject X k := (ordinaryDiagram X).map g
  let ry : B ⟶ representationObject Y k := (ordinaryDiagram Y).map g
  let e : (𝟙_ V) ⟶ Hom T n k := arrow T g
  have hx : rx = (ρ_ A).inv ≫ (A ◁ e) ≫ representationAction X n k := ordinaryDiagram_map X g
  have hy : ry = (ρ_ B).inv ≫ (B ◁ e) ≫ representationAction Y n k := ordinaryDiagram_map Y g
  have hf : representationAction X n k ≫ fk = (fn ▷ Hom T n k) ≫ representationAction Y n k :=
    (representationMap_comm f n k).symm
  have he : (A ◁ e) ≫ (fn ▷ Hom T n k) = (fn ▷ (𝟙_ V)) ≫ (B ◁ e) := whisker_exchange fn e
  have hr : (ρ_ A).inv ≫ (fn ▷ (𝟙_ V)) = fn ≫ (ρ_ B).inv := (rightUnitor_inv_naturality fn).symm
  change rx ≫ fk = fn ≫ ry
  rw [hx, hy]
  simp only [Category.assoc]
  rw [hf]
  slice_lhs 2 3 => rw [he]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [hr]
  simp only [Category.assoc]

/-- The exact original component family is a natural transformation of the restricted diagrams. -/
def ordinaryTransformation {X Y : Representation T} (f : X ⟶ Y) : ordinaryDiagram X ⟶ ordinaryDiagram Y where
  app n := representationMapComponent f n
  naturality _ _ g := representationMap_index f g

omit [MonoidalClosed V] in
/-- Every whole operator transformation commutes with every complete original coefficient action. -/
theorem representationCoefficient_morphism {X Y : Representation T} (f : X ⟶ Y) (a n : I) :
    representationCoefficient X a n ≫ representationMapComponent f (a ⊗ n) =
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ representationMapComponent f n) ≫
        representationCoefficient Y a n := by
  let P := (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a
  let A := representationObject X n
  let B := representationObject Y n
  let fn : A ⟶ B := representationMapComponent f n
  let fan : representationObject X (a ⊗ n) ⟶ representationObject Y (a ⊗ n) :=
    representationMapComponent f (a ⊗ n)
  let j : P ⟶ Hom T n (a ⊗ n) := generator T a n (a ⊗ n) (𝟙 (a ⊗ n))
  have hf : representationAction X n (a ⊗ n) ≫ fan =
      (fn ▷ Hom T n (a ⊗ n)) ≫ representationAction Y n (a ⊗ n) :=
    (representationMap_comm f n (a ⊗ n)).symm
  have he : (A ◁ j) ≫ (fn ▷ Hom T n (a ⊗ n)) = (fn ▷ P) ≫ (B ◁ j) := whisker_exchange fn j
  have hb : (β_ P A).hom ≫ (fn ▷ P) = (P ◁ fn) ≫ (β_ P B).hom :=
    (braiding_naturality_right P fn).symm
  change representationCoefficient X a n ≫ fan = (P ◁ fn) ≫ representationCoefficient Y a n
  simp only [representationCoefficient, Category.assoc]
  rw [hf]
  slice_lhs 2 3 => rw [he]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [hb]
  simp only [Category.assoc]
  rfl

variable [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The complete original sphere-module morphism reconstructed from a whole operator transformation. -/
def fromRepresentationMap {X Y : Representation T} (f : X ⟶ Y) :
    fromRepresentation X ⟶ fromRepresentation Y where
  map := ordinaryTransformation f
  comm := representationCoefficient_morphism f

/-- Reconstruction is functorial on every original object and whole morphism. -/
def fromRepresentations (T : V) : Representation T ⥤ SphereData T where
  obj := fromRepresentation
  map := fromRepresentationMap
  map_id X := by
    apply DayFunctor.ExternalModule.Data.Hom.ext
    apply NatTrans.ext
    funext n
    rfl
  map_comp f g := by
    apply DayFunctor.ExternalModule.Data.Hom.ext
    apply NatTrans.ext
    funext n
    rfl

/-- Every original transformation component is unchanged by reconstruction. -/
theorem fromRepresentationMap_component {X Y : Representation T} (f : X ⟶ Y) (n : I) :
    (fromRepresentationMap f).map.app n = representationMapComponent f n := rfl

end CategoryTheory.Spectra.Symmetric.OperatorCoend
