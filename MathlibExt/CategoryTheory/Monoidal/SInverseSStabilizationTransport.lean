/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseS

/-!
# Transport of an original diagonal stabilized S⁻¹S arrow

An actual isomorphism of stabilizers and compatible isomorphisms of the
source and target coordinates give a commuting square in the original
stabilizer quotient category. The proof supplies the stabilizer isomorphism
between the two raw composites and checks both coordinate equations.
The only input equation is the original biproduct coordinate square.
-/

noncomputable section

open CategoryTheory Limits ZeroObject

universe uC vC

namespace CategoryTheory.SInverseS

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

private abbrev transportLeftZeroUnit (X : C) : (0 : C) ⊞ X ≅ X :=
  (isoZeroBiprod (isZero_zero C)).symm

private abbrev transportRightZeroUnit (X : C) : X ⊞ (0 : C) ≅ X :=
  (isoBiprodZero (isZero_zero C)).symm

private theorem transportLeftZeroComposition {s X Y Z : C}
    (f : s ⊞ X ≅ Y) (e : Y ≅ Z) :
    (biprod.associator (0 : C) s X).trans
        ((biprod.mapIso (Iso.refl (0 : C)) f).trans
          ((transportLeftZeroUnit Y).trans e)) =
      (biprod.mapIso (transportLeftZeroUnit s) (Iso.refl X)).trans
        (f.trans e) := by
  apply Iso.ext
  change (biprod.associator (0 : C) s X).hom ≫
      biprod.map (𝟙 (0 : C)) f.hom ≫ (transportLeftZeroUnit Y).hom ≫ e.hom =
    biprod.map (transportLeftZeroUnit s).hom (𝟙 X) ≫ f.hom ≫ e.hom
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ e.hom) (rawComp_id_hom f.hom).symm

private theorem transportRightZeroCancellation (s X : C) :
    (biprod.mapIso (transportRightZeroUnit s).symm (Iso.refl X)).trans
        ((biprod.associator s (0 : C) X).trans
          (biprod.mapIso (Iso.refl s) (transportLeftZeroUnit X))) =
      Iso.refl (s ⊞ X) := by
  apply Iso.ext
  change biprod.map (transportRightZeroUnit s).inv (𝟙 X) ≫
      (biprod.associator s (0 : C) X).hom ≫
      biprod.map (𝟙 s) (transportLeftZeroUnit X).hom = 𝟙 (s ⊞ X)
  rw [← rawId_comp_hom]
  apply biprod.hom_ext <;> simp [Category.assoc]

private theorem transportRightZeroComposition {s t X X' Y : C}
    (e : s ≅ t) (u : X ≅ X') (b : t ⊞ X' ≅ Y) :
    (stabilizerIso ((transportLeftZeroUnit s).trans
        (e.trans (transportRightZeroUnit t).symm)) X).trans
        ((biprod.associator t (0 : C) X).trans
          ((biprod.mapIso (Iso.refl t)
            ((transportLeftZeroUnit X).trans u)).trans b)) =
      (biprod.mapIso (transportLeftZeroUnit s) (Iso.refl X)).trans
        ((biprod.mapIso e u).trans b) := by
  apply Iso.ext
  have hsplit :
      biprod.map
          ((transportLeftZeroUnit s).hom ≫ e.hom ≫ (transportRightZeroUnit t).inv)
          (𝟙 X) =
        biprod.map (transportLeftZeroUnit s).hom (𝟙 X) ≫
          biprod.map e.hom (𝟙 X) ≫
          biprod.map (transportRightZeroUnit t).inv (𝟙 X) := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  have hunit :
      biprod.map (𝟙 t) ((transportLeftZeroUnit X).hom ≫ u.hom) =
        biprod.map (𝟙 t) (transportLeftZeroUnit X).hom ≫
          biprod.map (𝟙 t) u.hom := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  have hcancel := congrArg Iso.hom (transportRightZeroCancellation t X)
  change biprod.map (transportRightZeroUnit t).inv (𝟙 X) ≫
      (biprod.associator t (0 : C) X).hom ≫
      biprod.map (𝟙 t) (transportLeftZeroUnit X).hom = 𝟙 (t ⊞ X) at hcancel
  change biprod.map
      ((transportLeftZeroUnit s).hom ≫ e.hom ≫ (transportRightZeroUnit t).inv)
      (𝟙 X) ≫ (biprod.associator t (0 : C) X).hom ≫
      biprod.map (𝟙 t) ((transportLeftZeroUnit X).hom ≫ u.hom) ≫ b.hom =
    biprod.map (transportLeftZeroUnit s).hom (𝟙 X) ≫
      biprod.map e.hom u.hom ≫ b.hom
  rw [hsplit, hunit]
  have hmiddle :
      biprod.map (transportRightZeroUnit t).inv (𝟙 X) ≫
          (biprod.associator t (0 : C) X).hom ≫
          (biprod.map (𝟙 t) (transportLeftZeroUnit X).hom ≫
            biprod.map (𝟙 t) u.hom) =
        biprod.map (𝟙 t) u.hom := by
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun m => m ≫ biprod.map (𝟙 t) u.hom) hcancel
  have hmiddle' := congrArg (fun m => m ≫ b.hom) hmiddle
  simp only [Category.assoc] at hmiddle' ⊢
  rw [hmiddle']
  have hmap : biprod.map e.hom (𝟙 X) ≫ biprod.map (𝟙 t) u.hom =
      biprod.map e.hom u.hom := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  have hmap' := congrArg (fun m => m ≫ b.hom) hmap
  simp only [Category.assoc] at hmap'
  rw [hmap']

private abbrev transportCoordinateRaw {X Y : C} (u : X ≅ Y) :
    RawHom (⟨X, X⟩ : Pair C) ⟨Y, Y⟩ where
  stabilizer := 0
  hom₁ := (transportLeftZeroUnit X).trans u
  hom₂ := (transportLeftZeroUnit X).trans u

private theorem transportCoordinateEquation {s t X X' Y Y' : C}
    (a : s ⊞ X ≅ Y) (b : t ⊞ X' ≅ Y')
    (e : s ≅ t) (u : X ≅ X') (v : Y ≅ Y')
    (h : a.trans v = (biprod.mapIso e u).trans b) :
    (stabilizerIso ((transportLeftZeroUnit s).trans
        (e.trans (transportRightZeroUnit t).symm)) X).trans
        ((biprod.associator t (0 : C) X).trans
          ((biprod.mapIso (Iso.refl t)
            ((transportLeftZeroUnit X).trans u)).trans b)) =
      (biprod.associator (0 : C) s X).trans
        ((biprod.mapIso (Iso.refl (0 : C)) a).trans
          ((transportLeftZeroUnit Y).trans v)) :=
  (transportRightZeroComposition e u b).trans
    ((congrArg
      (fun k => (biprod.mapIso (transportLeftZeroUnit s) (Iso.refl X)).trans k)
      h.symm).trans (transportLeftZeroComposition a v).symm)

private theorem transportRawRelation {s t X X' Y Y' : C}
    (a : s ⊞ X ≅ Y) (b : t ⊞ X' ≅ Y')
    (e : s ≅ t) (u : X ≅ X') (v : Y ≅ Y')
    (h : a.trans v = (biprod.mapIso e u).trans b) :
    ((⟨s, a, a⟩ : RawHom (⟨X, X⟩ : Pair C) ⟨Y, Y⟩).comp
      (transportCoordinateRaw v)).Rel
      ((transportCoordinateRaw u).comp
        (⟨t, b, b⟩ : RawHom (⟨X', X'⟩ : Pair C) ⟨Y', Y'⟩)) := by
  refine ⟨(transportLeftZeroUnit s).trans
    (e.trans (transportRightZeroUnit t).symm), ?_, ?_⟩
  · exact transportCoordinateEquation a b e u v h
  · exact transportCoordinateEquation a b e u v h

/-- Compatible actual source, target and stabilizer isomorphisms transport
the original diagonal stabilized arrow in the S⁻¹S quotient category.
The two coordinate isomorphisms are the canonical core-pair inclusion maps. -/
public theorem diagonalStabilization_transport {s t X X' Y Y' : C}
    (a : s ⊞ X ≅ Y) (b : t ⊞ X' ≅ Y')
    (e : s ≅ t) (u : X ≅ X') (v : Y ≅ Y')
    (h : a.trans v = (biprod.mapIso e u).trans b) :
    Hom.mk (⟨s, a, a⟩ : RawHom (⟨X, X⟩ : Pair C) ⟨Y, Y⟩) ≫
        ((corePairInclusion (C := C)).mapIso
          ((Core.isoMk (x := ⟨Y⟩) (y := ⟨Y'⟩) v).prod
            (Core.isoMk (x := ⟨Y⟩) (y := ⟨Y'⟩) v))).hom =
      ((corePairInclusion (C := C)).mapIso
        ((Core.isoMk (x := ⟨X⟩) (y := ⟨X'⟩) u).prod
          (Core.isoMk (x := ⟨X⟩) (y := ⟨X'⟩) u))).hom ≫
        Hom.mk (⟨t, b, b⟩ : RawHom (⟨X', X'⟩ : Pair C) ⟨Y', Y'⟩) := by
  change Hom.mk
      ((⟨s, a, a⟩ : RawHom (⟨X, X⟩ : Pair C) ⟨Y, Y⟩).comp
        (transportCoordinateRaw v)) =
    Hom.mk ((transportCoordinateRaw u).comp
      (⟨t, b, b⟩ : RawHom (⟨X', X'⟩ : Pair C) ⟨Y', Y'⟩))
  exact Quotient.sound (transportRawRelation a b e u v h)

end CategoryTheory.SInverseS

end
