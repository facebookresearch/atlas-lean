/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.MonoidAction
public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreTranslationAction
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationAction

/-!
# The skeleton action on additive S⁻¹S homology

First-coordinate translation on the additive `S⁻¹S` category depends only
on the skeleton class of the translating object.  Its zero and biproduct
coherence give a strict action on homology and hence an integral
monoid-algebra module.  Second-coordinate translation supplies an inverse
for every skeleton monomial through the two diagonal-addition nerve
homotopies.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

namespace RawHom

omit [HasZeroObject C] in
/-- Naturality in the fixed first summand of the stabilizer swap used by
first-coordinate translation. -/
theorem swapStabilizerIso_natural_first_hom {s t X Y : C} (e : s ≅ t)
    (r : C) (f : r ⊞ X ⟶ Y) :
    (swapStabilizerIso s r X).hom ≫ biprod.map (𝟙 s) f ≫
          biprod.map e.hom (𝟙 Y) =
      biprod.map (𝟙 r) (biprod.map e.hom (𝟙 X)) ≫
        (swapStabilizerIso t r X).hom ≫ biprod.map (𝟙 t) f := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext' <;> simp

/-- Coherence for composing a stabilized arrow with a zero-stabilized
arrow.  The stabilizers on the two sides differ by swapping the zero
summand. -/
theorem zeroStabilized_comp_hom {r X Y : C} (f : r ⊞ X ⟶ Y) :
    biprod.map (biprod.braiding r (0 : C)).hom (𝟙 X) ≫
          (biprod.associator (0 : C) r X).hom ≫
          biprod.map (𝟙 (0 : C)) f ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom =
      (biprod.associator r (0 : C) X).hom ≫
        biprod.map (𝟙 r) (isoZeroBiprod (isZero_zero C)).symm.hom ≫ f := by
  rw [show (isoZeroBiprod (isZero_zero C)).symm.hom =
    (biprod.snd : (0 : C) ⊞ Y ⟶ Y) from rfl,
    biprod.map_snd]
  simpa only [Category.assoc] using congrArg (fun k => k ≫ f)
    (swapZeroUnitCoherence r X)

/-- Commuting a stabilizer past a zero summand and then removing that zero
is the coordinatewise zero-unitor. -/
theorem swapStabilizerIso_zero_hom (r X : C) :
    (swapStabilizerIso (0 : C) r X).hom ≫
        (isoZeroBiprod (isZero_zero C)).symm.hom =
      biprod.map (𝟙 r) (isoZeroBiprod (isZero_zero C)).symm.hom := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext' <;> simp

omit [HasZeroObject C] in
/-- Coherence between translation by a biproduct and two successive
first-coordinate translations. -/
theorem swapStabilizerIso_biprod_hom (s t r X : C) {Y : C}
    (f : r ⊞ X ⟶ Y) :
    (swapStabilizerIso (s ⊞ t) r X).hom ≫
          biprod.map (𝟙 (s ⊞ t)) f ≫
          (biprod.associator s t Y).hom =
      biprod.map (𝟙 r) (biprod.associator s t X).hom ≫
        (swapStabilizerIso s r (t ⊞ X)).hom ≫
        biprod.map (𝟙 s)
          ((swapStabilizerIso t r X).hom ≫
            biprod.map (𝟙 t) f) := by
  apply biprod.hom_ext'
  · simp only [Category.assoc, Category.id_comp,
      inl_swapStabilizerIso_hom_assoc, biprod.inr_map,
      biprod.inr_map_assoc, biprod.inl_map_assoc,
      inr_associator_hom]
  · apply biprod.hom_ext'
    · apply biprod.hom_ext'
      · simp only [Category.id_comp,
          inl_inr_swapStabilizerIso_hom_assoc,
          biprod.inl_map, biprod.inl_map_assoc,
          biprod.inr_map_assoc, inl_inl_associator_hom,
          inl_inl_associator_hom_assoc]
      · simp only [Category.assoc, Category.id_comp,
          inl_inr_swapStabilizerIso_hom_assoc,
          inr_inr_swapStabilizerIso_hom_assoc,
          biprod.inl_map_assoc, biprod.inr_map,
          biprod.inr_map_assoc, inr_inl_associator_hom,
          inr_inl_associator_hom_assoc]
    · simp only [Category.assoc,
        inr_inr_swapStabilizerIso_hom_assoc,
        biprod.inr_map, biprod.inr_map_assoc,
        inr_associator_hom, inr_associator_hom_assoc]

/-- The raw zero-stabilized arrow underlying the coordinate isomorphism in
`Pair C`.  This is only an abbreviation for `RawHom.ofCorePair`. -/
noncomputable abbrev ofCoordinateIsos {X Y : Pair C}
    (e₁ : X.fst ≅ Y.fst) (e₂ : X.snd ≅ Y.snd) : RawHom X Y :=
  RawHom.ofCorePair
    (((Core.isoMk e₁).hom, (Core.isoMk e₂).hom) :
      (⟨X.fst⟩, ⟨X.snd⟩) ⟶ (⟨Y.fst⟩, ⟨Y.snd⟩))

end RawHom

/-- An isomorphism in `Pair C` obtained from isomorphisms in its two
coordinates.  This uses the canonical core-pair inclusion, so its arrows are
the existing zero-stabilized arrows. -/
noncomputable def pairIsoOfCoordinateIsos {X Y : Pair C}
    (e₁ : X.fst ≅ Y.fst) (e₂ : X.snd ≅ Y.snd) : X ≅ Y :=
  (corePairInclusion (C := C)).mapIso
    (Iso.prod (Core.isoMk e₁) (Core.isoMk e₂) :
      (⟨X.fst⟩, ⟨X.snd⟩) ≅ (⟨Y.fst⟩, ⟨Y.snd⟩))

/-- The forward arrow of `pairIsoOfCoordinateIsos` is the canonical
zero-stabilized arrow. -/
@[simp]
theorem pairIsoOfCoordinateIsos_hom {X Y : Pair C}
    (e₁ : X.fst ≅ Y.fst) (e₂ : X.snd ≅ Y.snd) :
    (pairIsoOfCoordinateIsos e₁ e₂).hom =
      Hom.mk (RawHom.ofCoordinateIsos e₁ e₂) :=
  rfl

/-- The inverse arrow of `pairIsoOfCoordinateIsos` is the canonical
zero-stabilized arrow attached to the inverse coordinate isomorphisms. -/
@[simp]
theorem pairIsoOfCoordinateIsos_inv {X Y : Pair C}
    (e₁ : X.fst ≅ Y.fst) (e₂ : X.snd ≅ Y.snd) :
    (pairIsoOfCoordinateIsos e₁ e₂).inv =
      Hom.mk (RawHom.ofCoordinateIsos e₁.symm e₂.symm) :=
  rfl

namespace RawHom

/-- Raw naturality for changing the object translated in the first
coordinate. -/
theorem translateFirst_isoOfIso_naturality_rel {s t : C} (e : s ≅ t)
    {X Y : Pair C} (f : RawHom X Y) :
    ((f.translateFirst s).comp
        (ofCoordinateIsos (X := translateFirstObj s Y)
          (Y := translateFirstObj t Y)
          (biprod.mapIso e (Iso.refl Y.fst))
          (Iso.refl Y.snd))).Rel
      ((ofCoordinateIsos (X := translateFirstObj s X)
          (Y := translateFirstObj t X)
          (biprod.mapIso e (Iso.refl X.fst))
          (Iso.refl X.snd)).comp (f.translateFirst t)) := by
  apply RawHom.Rel.symm
  refine ⟨biprod.braiding f.stabilizer (0 : C), ?_, ?_⟩
  · apply Iso.ext
    dsimp [ofCoordinateIsos, RawHom.comp, translateFirst,
      stabilizerIso]
    simp only [Core.isoMk_hom_iso]
    change
      biprod.map (biprod.braiding f.stabilizer (0 : C)).hom
            (𝟙 (s ⊞ X.fst)) ≫
          (biprod.associator (0 : C) f.stabilizer
            (s ⊞ X.fst)).hom ≫
          biprod.map (𝟙 (0 : C))
            ((swapStabilizerIso s f.stabilizer X.fst).hom ≫
              biprod.map (𝟙 s) f.hom₁.hom) ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫
          biprod.map e.hom (𝟙 Y.fst) =
        (biprod.associator f.stabilizer (0 : C)
            (s ⊞ X.fst)).hom ≫
          biprod.map (𝟙 f.stabilizer)
            ((isoZeroBiprod (isZero_zero C)).symm.hom ≫
              biprod.map e.hom (𝟙 X.fst)) ≫
          (swapStabilizerIso t f.stabilizer X.fst).hom ≫
          biprod.map (𝟙 t) f.hom₁.hom
    rw [show (isoZeroBiprod (isZero_zero C)).symm.hom =
      (biprod.snd : (0 : C) ⊞ (s ⊞ Y.fst) ⟶ s ⊞ Y.fst) from rfl,
      biprod.map_snd_assoc]
    rw [biprodMap_id_comp]
    calc
      _ = (biprod.associator f.stabilizer (0 : C)
              (s ⊞ X.fst)).hom ≫
            biprod.map (𝟙 f.stabilizer)
              (isoZeroBiprod (isZero_zero C)).symm.hom ≫
            (swapStabilizerIso s f.stabilizer X.fst).hom ≫
            biprod.map (𝟙 s) f.hom₁.hom ≫
            biprod.map e.hom (𝟙 Y.fst) := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫
            (swapStabilizerIso s f.stabilizer X.fst).hom ≫
            biprod.map (𝟙 s) f.hom₁.hom ≫
            biprod.map e.hom (𝟙 Y.fst))
          (swapZeroUnitCoherence f.stabilizer (s ⊞ X.fst))
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k =>
            (biprod.associator f.stabilizer (0 : C)
                (s ⊞ X.fst)).hom ≫
              biprod.map (𝟙 f.stabilizer)
                (isoZeroBiprod (isZero_zero C)).symm.hom ≫ k)
          (swapStabilizerIso_natural_first_hom e f.stabilizer
            f.hom₁.hom)
  · apply Iso.ext
    dsimp [ofCoordinateIsos, RawHom.comp, translateFirst,
      stabilizerIso]
    simp only [Core.isoMk_hom_iso, Iso.refl_hom, Iso.trans_refl,
      Category.comp_id]
    change
      biprod.map (biprod.braiding f.stabilizer (0 : C)).hom
            (𝟙 X.snd) ≫
          (biprod.associator (0 : C) f.stabilizer X.snd).hom ≫
          biprod.map (𝟙 (0 : C)) f.hom₂.hom ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom =
        (biprod.associator f.stabilizer (0 : C) X.snd).hom ≫
          biprod.map (𝟙 f.stabilizer)
            (isoZeroBiprod (isZero_zero C)).symm.hom ≫
          f.hom₂.hom
    exact zeroStabilized_comp_hom f.hom₂.hom

/-- Raw naturality for the comparison from first-coordinate translation by
zero to the identity functor. -/
theorem translateFirst_zero_naturality_rel {X Y : Pair C}
    (f : RawHom X Y) :
    ((f.translateFirst (0 : C)).comp
        (ofCoordinateIsos (X := translateFirstObj (0 : C) Y) (Y := Y)
          (isoZeroBiprod (isZero_zero C)).symm
          (Iso.refl Y.snd))).Rel
      ((ofCoordinateIsos (X := translateFirstObj (0 : C) X) (Y := X)
          (isoZeroBiprod (isZero_zero C)).symm
          (Iso.refl X.snd)).comp f) := by
  apply RawHom.Rel.symm
  refine ⟨biprod.braiding f.stabilizer (0 : C), ?_, ?_⟩
  · apply Iso.ext
    dsimp [ofCoordinateIsos, RawHom.comp, translateFirst,
      stabilizerIso]
    simp only [Core.isoMk_hom_iso]
    change
      biprod.map (biprod.braiding f.stabilizer (0 : C)).hom
            (𝟙 ((0 : C) ⊞ X.fst)) ≫
          (biprod.associator (0 : C) f.stabilizer
            ((0 : C) ⊞ X.fst)).hom ≫
          biprod.map (𝟙 (0 : C))
            ((swapStabilizerIso (0 : C) f.stabilizer X.fst).hom ≫
              biprod.map (𝟙 (0 : C)) f.hom₁.hom) ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom =
        (biprod.associator f.stabilizer (0 : C)
            ((0 : C) ⊞ X.fst)).hom ≫
          biprod.map (𝟙 f.stabilizer)
            ((isoZeroBiprod (isZero_zero C)).symm.hom ≫
              (isoZeroBiprod (isZero_zero C)).symm.hom) ≫
          f.hom₁.hom
    have hKey :
        (swapStabilizerIso (0 : C) f.stabilizer X.fst).hom ≫
              biprod.map (𝟙 (0 : C)) f.hom₁.hom ≫
              (isoZeroBiprod (isZero_zero C)).symm.hom =
          biprod.map (𝟙 f.stabilizer)
              (isoZeroBiprod (isZero_zero C)).symm.hom ≫
            f.hom₁.hom := by
      rw [show (isoZeroBiprod (isZero_zero C)).symm.hom =
        (biprod.snd : (0 : C) ⊞ Y.fst ⟶ Y.fst) from rfl,
        biprod.map_snd]
      change
        (swapStabilizerIso (0 : C) f.stabilizer X.fst).hom ≫
              (isoZeroBiprod (isZero_zero C)).symm.hom ≫
              f.hom₁.hom =
          biprod.map (𝟙 f.stabilizer)
              (isoZeroBiprod (isZero_zero C)).symm.hom ≫
            f.hom₁.hom
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ f.hom₁.hom)
        (swapStabilizerIso_zero_hom f.stabilizer X.fst)
    calc
      _ = (biprod.associator f.stabilizer (0 : C)
              ((0 : C) ⊞ X.fst)).hom ≫
            biprod.map (𝟙 f.stabilizer)
              (isoZeroBiprod (isZero_zero C)).symm.hom ≫
            (swapStabilizerIso (0 : C) f.stabilizer X.fst).hom ≫
            biprod.map (𝟙 (0 : C)) f.hom₁.hom ≫
            (isoZeroBiprod (isZero_zero C)).symm.hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫
            (isoZeroBiprod (isZero_zero C)).symm.hom)
          (zeroStabilized_comp_hom
            ((swapStabilizerIso (0 : C) f.stabilizer X.fst).hom ≫
              biprod.map (𝟙 (0 : C)) f.hom₁.hom))
      _ = (biprod.associator f.stabilizer (0 : C)
              ((0 : C) ⊞ X.fst)).hom ≫
            biprod.map (𝟙 f.stabilizer)
              (isoZeroBiprod (isZero_zero C)).symm.hom ≫
            biprod.map (𝟙 f.stabilizer)
              (isoZeroBiprod (isZero_zero C)).symm.hom ≫
            f.hom₁.hom := by
        simpa only [Category.assoc] using congrArg
          (fun k =>
            (biprod.associator f.stabilizer (0 : C)
                ((0 : C) ⊞ X.fst)).hom ≫
              biprod.map (𝟙 f.stabilizer)
                (isoZeroBiprod (isZero_zero C)).symm.hom ≫
              k)
          hKey
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k =>
            (biprod.associator f.stabilizer (0 : C)
                ((0 : C) ⊞ X.fst)).hom ≫ k ≫ f.hom₁.hom)
          (biprodMap_id_comp f.stabilizer
            (isoZeroBiprod (isZero_zero C)).symm.hom
            (isoZeroBiprod (isZero_zero C)).symm.hom).symm
  · apply Iso.ext
    dsimp [ofCoordinateIsos, RawHom.comp, translateFirst,
      stabilizerIso]
    simp only [Core.isoMk_hom_iso, Iso.refl_hom, Iso.trans_refl,
      Category.comp_id]
    change
      biprod.map (biprod.braiding f.stabilizer (0 : C)).hom
            (𝟙 X.snd) ≫
          (biprod.associator (0 : C) f.stabilizer X.snd).hom ≫
          biprod.map (𝟙 (0 : C)) f.hom₂.hom ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom =
        (biprod.associator f.stabilizer (0 : C) X.snd).hom ≫
          biprod.map (𝟙 f.stabilizer)
            (isoZeroBiprod (isZero_zero C)).symm.hom ≫
          f.hom₂.hom
    exact zeroStabilized_comp_hom f.hom₂.hom

/-- Raw naturality for the comparison from translation by a biproduct to
two successive first-coordinate translations. -/
theorem translateFirst_biprod_naturality_rel (s t : C) {X Y : Pair C}
    (f : RawHom X Y) :
    ((f.translateFirst (s ⊞ t)).comp
        (ofCoordinateIsos
          (X := translateFirstObj (s ⊞ t) Y)
          (Y := translateFirstObj s (translateFirstObj t Y))
          (biprod.associator s t Y.fst) (Iso.refl Y.snd))).Rel
      ((ofCoordinateIsos
          (X := translateFirstObj (s ⊞ t) X)
          (Y := translateFirstObj s (translateFirstObj t X))
          (biprod.associator s t X.fst) (Iso.refl X.snd)).comp
        ((f.translateFirst t).translateFirst s)) := by
  apply RawHom.Rel.symm
  refine ⟨biprod.braiding f.stabilizer (0 : C), ?_, ?_⟩
  · apply Iso.ext
    dsimp [ofCoordinateIsos, RawHom.comp, translateFirst,
      stabilizerIso]
    simp only [Core.isoMk_hom_iso]
    change
      biprod.map (biprod.braiding f.stabilizer (0 : C)).hom
            (𝟙 ((s ⊞ t) ⊞ X.fst)) ≫
          (biprod.associator (0 : C) f.stabilizer
            ((s ⊞ t) ⊞ X.fst)).hom ≫
          biprod.map (𝟙 (0 : C))
            ((swapStabilizerIso (s ⊞ t) f.stabilizer X.fst).hom ≫
              biprod.map (𝟙 (s ⊞ t)) f.hom₁.hom) ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫
          (biprod.associator s t Y.fst).hom =
        (biprod.associator f.stabilizer (0 : C)
            ((s ⊞ t) ⊞ X.fst)).hom ≫
          biprod.map (𝟙 f.stabilizer)
            ((isoZeroBiprod (isZero_zero C)).symm.hom ≫
              (biprod.associator s t X.fst).hom) ≫
          (swapStabilizerIso s f.stabilizer (t ⊞ X.fst)).hom ≫
          biprod.map (𝟙 s)
            ((swapStabilizerIso t f.stabilizer X.fst).hom ≫
              biprod.map (𝟙 t) f.hom₁.hom)
    calc
      _ = (biprod.associator f.stabilizer (0 : C)
              ((s ⊞ t) ⊞ X.fst)).hom ≫
            biprod.map (𝟙 f.stabilizer)
              (isoZeroBiprod (isZero_zero C)).symm.hom ≫
            (swapStabilizerIso (s ⊞ t) f.stabilizer X.fst).hom ≫
            biprod.map (𝟙 (s ⊞ t)) f.hom₁.hom ≫
            (biprod.associator s t Y.fst).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ (biprod.associator s t Y.fst).hom)
          (zeroStabilized_comp_hom
            ((swapStabilizerIso (s ⊞ t) f.stabilizer X.fst).hom ≫
              biprod.map (𝟙 (s ⊞ t)) f.hom₁.hom))
      _ = (biprod.associator f.stabilizer (0 : C)
              ((s ⊞ t) ⊞ X.fst)).hom ≫
            biprod.map (𝟙 f.stabilizer)
              (isoZeroBiprod (isZero_zero C)).symm.hom ≫
            biprod.map (𝟙 f.stabilizer)
              (biprod.associator s t X.fst).hom ≫
            (swapStabilizerIso s f.stabilizer (t ⊞ X.fst)).hom ≫
            biprod.map (𝟙 s)
              ((swapStabilizerIso t f.stabilizer X.fst).hom ≫
                biprod.map (𝟙 t) f.hom₁.hom) := by
        simpa only [Category.assoc] using congrArg
          (fun k =>
            (biprod.associator f.stabilizer (0 : C)
                ((s ⊞ t) ⊞ X.fst)).hom ≫
              biprod.map (𝟙 f.stabilizer)
                (isoZeroBiprod (isZero_zero C)).symm.hom ≫ k)
          (swapStabilizerIso_biprod_hom s t f.stabilizer X.fst
            f.hom₁.hom)
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k =>
            (biprod.associator f.stabilizer (0 : C)
                ((s ⊞ t) ⊞ X.fst)).hom ≫ k ≫
              (swapStabilizerIso s f.stabilizer (t ⊞ X.fst)).hom ≫
              biprod.map (𝟙 s)
                ((swapStabilizerIso t f.stabilizer X.fst).hom ≫
                  biprod.map (𝟙 t) f.hom₁.hom))
          (biprodMap_id_comp f.stabilizer
            (isoZeroBiprod (isZero_zero C)).symm.hom
            (biprod.associator s t X.fst).hom).symm
  · apply Iso.ext
    dsimp [ofCoordinateIsos, RawHom.comp, translateFirst,
      stabilizerIso]
    simp only [Core.isoMk_hom_iso, Iso.refl_hom, Iso.trans_refl,
      Category.comp_id]
    change
      biprod.map (biprod.braiding f.stabilizer (0 : C)).hom
            (𝟙 X.snd) ≫
          (biprod.associator (0 : C) f.stabilizer X.snd).hom ≫
          biprod.map (𝟙 (0 : C)) f.hom₂.hom ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom =
        (biprod.associator f.stabilizer (0 : C) X.snd).hom ≫
          biprod.map (𝟙 f.stabilizer)
            (isoZeroBiprod (isZero_zero C)).symm.hom ≫
          f.hom₂.hom
    exact zeroStabilized_comp_hom f.hom₂.hom

end RawHom

/-- Isomorphic translating objects give naturally isomorphic
first-coordinate translation functors on `Pair C`. -/
noncomputable def translateFirstIsoOfIso {s t : C} (e : s ≅ t) :
    translateFirstFunctor s ≅ translateFirstFunctor t :=
  NatIso.ofComponents
    (fun X => pairIsoOfCoordinateIsos
      (biprod.mapIso e (Iso.refl X.fst)) (Iso.refl X.snd)) (by
        intro X Y f
        induction f using Quotient.inductionOn with
        | _ f =>
            exact Quotient.sound
              (RawHom.translateFirst_isoOfIso_naturality_rel e f))

/-- First-coordinate translation by zero is naturally isomorphic to the
identity functor on `Pair C`. -/
noncomputable def translateFirstZeroIso :
    translateFirstFunctor (0 : C) ≅ 𝟭 (Pair C) :=
  NatIso.ofComponents
    (fun X => pairIsoOfCoordinateIsos
      (isoZeroBiprod (isZero_zero C)).symm (Iso.refl X.snd)) (by
        intro X Y f
        induction f using Quotient.inductionOn with
        | _ f =>
            exact Quotient.sound
              (RawHom.translateFirst_zero_naturality_rel f))

/-- Translation by a biproduct is naturally isomorphic to translation by
the second summand followed by translation by the first summand. -/
noncomputable def translateFirstBiprodIso (s t : C) :
    translateFirstFunctor (s ⊞ t) ≅
      translateFirstFunctor t ⋙ translateFirstFunctor s :=
  NatIso.ofComponents
    (fun X => pairIsoOfCoordinateIsos
      (biprod.associator s t X.fst) (Iso.refl X.snd)) (by
        intro X Y f
        induction f using Quotient.inductionOn with
        | _ f =>
            exact Quotient.sound
              (RawHom.translateFirst_biprod_naturality_rel s t f))

/-- Translation by the chosen representative of the zero skeleton class is
naturally isomorphic to the identity. -/
noncomputable def translateFirstSkeletonZeroIso :
    translateFirstFunctor ((0 : Skeleton C).out) ≅ 𝟭 (Pair C) :=
  translateFirstIsoOfIso (fromSkeletonToSkeletonIso (0 : C)) ≪≫
    translateFirstZeroIso

/-- Translation by the chosen representative of a sum of skeleton classes
is naturally isomorphic to the composite of the chosen translations. -/
noncomputable def translateFirstSkeletonAddIso (x y : Skeleton C) :
    translateFirstFunctor (x + y).out ≅
      translateFirstFunctor y.out ⋙ translateFirstFunctor x.out :=
  translateFirstIsoOfIso
      (fromSkeletonToSkeletonIso (x.out ⊞ y.out)) ≪≫
    translateFirstBiprodIso x.out y.out

/-- Second translation of an actual zero-stabilized core-pair arrow has the
same quotient class as the coordinatewise translated zero-stabilized arrow. -/
theorem RawHom.translateSecond_ofCorePair_rel (A : C)
    {X Y : Core C × Core C} (f : X ⟶ Y) :
    ((RawHom.ofCorePair f).translateSecond A).Rel
      (RawHom.ofCoordinateIsos f.1.iso (biprod.mapIso (Iso.refl A) f.2.iso)) := by
  dsimp only [RawHom.ofCorePair, RawHom.ofCoordinateIsos, RawHom.translateSecond]
  refine ⟨Iso.refl (0 : C), ?_, ?_⟩
  · apply Iso.ext
    rw [stabilizerIso_refl, Iso.refl_trans]
    simp only [Core.isoMk_hom_iso]
  · apply Iso.ext
    rw [stabilizerIso_refl, Iso.refl_trans]
    change
      (isoZeroBiprod (isZero_zero C)).symm.hom ≫ biprod.map (𝟙 A) f.2.iso.hom =
        (swapStabilizerIso A (0 : C) X.2.of).hom ≫
          biprod.map (𝟙 A) ((isoZeroBiprod (isZero_zero C)).symm.hom ≫ f.2.iso.hom)
    apply biprod.hom_ext'
    · exact (isZero_zero C).eq_of_src _ _
    · apply biprod.hom_ext' <;> simp [Category.assoc]

/-- The literal second-translation map of an actual core-pair arrow, with
both original coordinate maps retained. -/
theorem translateSecondFunctor_map_ofCorePair (A : C)
    {X Y : Core C × Core C} (f : X ⟶ Y) :
    (translateSecondFunctor A).map ((corePairInclusion (C := C)).map f) =
      (corePairInclusion (C := C)).map
        ((f.1, ⟨biprod.mapIso (Iso.refl A) f.2.iso⟩) :
          (X.1, (⟨A ⊞ X.2.of⟩ : Core C)) ⟶
            (Y.1, (⟨A ⊞ Y.2.of⟩ : Core C))) := by
  change Hom.mk ((RawHom.ofCorePair f).translateSecond A) =
    Hom.mk (RawHom.ofCoordinateIsos f.1.iso (biprod.mapIso (Iso.refl A) f.2.iso))
  exact Quotient.sound (RawHom.translateSecond_ofCorePair_rel A f)

section Homology

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Action of a skeleton class on the homology of the additive `S⁻¹S`
nerve, induced by first-coordinate translation. -/
noncomputable def pairTranslationHomologyMap
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C) :
    (nerve (Pair C)).homology R n ⟶ (nerve (Pair C)).homology R n :=
  SSet.homologyMap (nerveMap (translateFirstFunctor x.out)) R n

/-- On a represented skeleton class, the action agrees with translation by
the representing object itself. -/
theorem pairTranslationHomologyMap_toSkeleton
    (R : AddCommGrpCat.{u}) (n : ℕ) (s : C) :
    pairTranslationHomologyMap C R n (toSkeleton s) =
      SSet.homologyMap (nerveMap (translateFirstFunctor s)) R n :=
  (NatTrans.nerveHomotopy
    (translateFirstIsoOfIso
      (fromSkeletonToSkeletonIso s)).hom).congr_homologyMap R n

/-- The zero skeleton class acts as the identity on `Pair C` homology. -/
theorem pairTranslationHomologyMap_zero
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    pairTranslationHomologyMap C R n 0 = 𝟙 _ := by
  let H : Cat.{u, u} ⥤ AddCommGrpCat.{u} :=
    categoryHomologyFunctor AddCommGrpCat.{u} R n
  have h := categoryHomologyMap_eq_of_natIso AddCommGrpCat.{u}
    (translateFirstSkeletonZeroIso (C := C)) R n
  change H.map
      (translateFirstFunctor ((0 : Skeleton C).out)).toCatHom = 𝟙 _
  calc
    _ = H.map (𝟭 (Pair C)).toCatHom := h
    _ = 𝟙 _ := H.map_id (Cat.of (Pair C))

/-- Addition of skeleton classes acts by composition of the corresponding
first-translation homology maps. -/
theorem pairTranslationHomologyMap_add
    (R : AddCommGrpCat.{u}) (n : ℕ) (x y : Skeleton C) :
    pairTranslationHomologyMap C R n (x + y) =
      pairTranslationHomologyMap C R n y ≫
        pairTranslationHomologyMap C R n x := by
  let H : SSet.{u} ⥤ AddCommGrpCat.{u} := SSet.homologyFunctor R n
  have h := (NatTrans.nerveHomotopy
    (translateFirstSkeletonAddIso x y).hom).congr_homologyMap R n
  have hIso :
      H.map (nerveMap (translateFirstFunctor (x + y).out)) =
        H.map (nerveMap (translateFirstFunctor y.out ⋙
          translateFirstFunctor x.out)) := h
  have hNerve :
      nerveMap (translateFirstFunctor y.out ⋙
          translateFirstFunctor x.out) =
        nerveMap (translateFirstFunctor y.out) ≫
          nerveMap (translateFirstFunctor x.out) :=
    (nerveMap_comp _ _).symm
  change H.map (nerveMap (translateFirstFunctor (x + y).out)) =
    H.map (nerveMap (translateFirstFunctor y.out)) ≫
      H.map (nerveMap (translateFirstFunctor x.out))
  calc
    _ = H.map (nerveMap (translateFirstFunctor y.out ⋙
          translateFirstFunctor x.out)) := hIso
    _ = H.map (nerveMap (translateFirstFunctor y.out) ≫
          nerveMap (translateFirstFunctor x.out)) := by rw [hNerve]
    _ = _ := H.map_comp _ _

/-- Strict action of the multiplicative skeleton monoid on `Pair C`
homology. -/
noncomputable def pairTranslationHomologyAction
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    Action AddCommGrpCat.{u} (Multiplicative (Skeleton C)) where
  V := (nerve (Pair C)).homology R n
  ρ :=
    { toFun := fun x => .of (pairTranslationHomologyMap C R n x.toAdd)
      map_one' := by
        apply End.ext
        exact pairTranslationHomologyMap_zero C R n
      map_mul' := fun x y => by
        apply End.ext
        exact pairTranslationHomologyMap_add C R n x.toAdd y.toAdd }

/-- `Pair C` homology as a module over the integral monoid algebra of the
skeletal additive monoid. -/
noncomputable abbrev pairTranslationHomologyModule
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))) :=
  (Action.monoidAlgebraModuleFunctor
    (Multiplicative (Skeleton C))).obj
      (pairTranslationHomologyAction C R n)

/-- Forgetting the monoid-algebra module structure recovers the original
homology group. -/
noncomputable def pairTranslationHomologyModuleForgetIso
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    (forget₂
      (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{u}).obj (pairTranslationHomologyModule C R n) ≅
        (nerve (Pair C)).homology R n :=
  (Action.monoidAlgebraModuleForgetIso
    (Multiplicative (Skeleton C))).app
      (pairTranslationHomologyAction C R n)

/-- A skeleton monomial acts by the corresponding first-translation
homology map. -/
@[simp↓]
theorem pairTranslationHomologyModuleForgetIso_monomial_smul
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C)
    (z : pairTranslationHomologyModule C R n) :
    (pairTranslationHomologyModuleForgetIso C R n).hom
        (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd x) • z) =
      (pairTranslationHomologyMap C R n x).hom
        ((pairTranslationHomologyModuleForgetIso C R n).hom z) := by
  change
    ((Action.monoidAlgebraModuleForgetIso
      (Multiplicative (Skeleton C))).hom.app
        (pairTranslationHomologyAction C R n))
        (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd x) • z) =
      (((pairTranslationHomologyAction C R n).ρ
        (Multiplicative.ofAdd x)).asHom.hom)
        (((Action.monoidAlgebraModuleForgetIso
          (Multiplicative (Skeleton C))).hom.app
            (pairTranslationHomologyAction C R n)) z)
  exact Action.monoidAlgebraModuleForgetIso_of_smul
    (Multiplicative (Skeleton C))
    (pairTranslationHomologyAction C R n)
    (Multiplicative.ofAdd x) z

/-- Homology map induced by second-coordinate translation by an actual
object. -/
noncomputable def pairSecondTranslationHomologyMap
    (R : AddCommGrpCat.{u}) (n : ℕ) (A : C) :
    (nerve (Pair C)).homology R n ⟶ (nerve (Pair C)).homology R n :=
  SSet.homologyMap (nerveMap (translateSecondFunctor A)) R n

/-- First-coordinate translation by an actual object is an isomorphism on
homology, with second-coordinate translation as inverse. -/
noncomputable def pairTranslationHomologyIsoOfObject
    (R : AddCommGrpCat.{u}) (n : ℕ) (A : C) :
    (nerve (Pair C)).homology R n ≅ (nerve (Pair C)).homology R n where
  hom := SSet.homologyMap (nerveMap (translateFirstFunctor A)) R n
  inv := pairSecondTranslationHomologyMap C R n A
  hom_inv_id := by
    change
      SSet.homologyMap (nerveMap (translateFirstFunctor A)) R n ≫
          SSet.homologyMap (nerveMap (translateSecondFunctor A)) R n =
        𝟙 _
    rw [← SSet.homologyMap_comp,
      ← (translateFirstSecondNerveHomotopy A).congr_homologyMap R n,
      SSet.homologyMap_id]
  inv_hom_id := by
    change
      SSet.homologyMap (nerveMap (translateSecondFunctor A)) R n ≫
          SSet.homologyMap (nerveMap (translateFirstFunctor A)) R n =
        𝟙 _
    rw [← SSet.homologyMap_comp,
      ← (translateSecondFirstNerveHomotopy A).congr_homologyMap R n,
      SSet.homologyMap_id]

/-- On the skeleton class represented by `A`, the first-translation action
is an isomorphism with inverse induced by second-coordinate translation by
`A`. -/
noncomputable def pairTranslationHomologyIsoToSkeleton
    (R : AddCommGrpCat.{u}) (n : ℕ) (A : C) :
    (nerve (Pair C)).homology R n ≅ (nerve (Pair C)).homology R n where
  hom := pairTranslationHomologyMap C R n (toSkeleton A)
  inv := pairSecondTranslationHomologyMap C R n A
  hom_inv_id := by
    rw [pairTranslationHomologyMap_toSkeleton]
    exact (pairTranslationHomologyIsoOfObject C R n A).hom_inv_id
  inv_hom_id := by
    rw [pairTranslationHomologyMap_toSkeleton]
    exact (pairTranslationHomologyIsoOfObject C R n A).inv_hom_id

/-- The action of every skeleton class is an isomorphism on `Pair C`
homology. -/
noncomputable def pairTranslationHomologyIso
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C) :
    (nerve (Pair C)).homology R n ≅ (nerve (Pair C)).homology R n :=
  pairTranslationHomologyIsoOfObject C R n x.out

@[simp]
theorem pairTranslationHomologyIso_hom
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C) :
    (pairTranslationHomologyIso C R n x).hom =
      pairTranslationHomologyMap C R n x :=
  rfl

@[simp]
theorem pairTranslationHomologyIso_inv
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C) :
    (pairTranslationHomologyIso C R n x).inv =
      pairSecondTranslationHomologyMap C R n x.out :=
  rfl

/-- The additive-group automorphism underlying action by the monomial of a
skeleton class. -/
noncomputable def pairTranslationHomologyMonomialIso
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C) :
    (forget₂
      (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{u}).obj (pairTranslationHomologyModule C R n) ≅
    (forget₂
      (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{u}).obj (pairTranslationHomologyModule C R n) :=
  pairTranslationHomologyModuleForgetIso C R n ≪≫
    pairTranslationHomologyIso C R n x ≪≫
      (pairTranslationHomologyModuleForgetIso C R n).symm

/-- The forward map of `pairTranslationHomologyMonomialIso` is literally
scalar multiplication by the corresponding basis monomial. -/
@[simp↓]
theorem pairTranslationHomologyMonomialIso_hom_apply
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C)
    (z : pairTranslationHomologyModule C R n) :
    (pairTranslationHomologyMonomialIso C R n x).hom z =
      MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
        (Multiplicative.ofAdd x) • z := by
  let e := pairTranslationHomologyModuleForgetIso C R n
  apply e.addCommGroupIsoToAddEquiv.injective
  change e.hom ((pairTranslationHomologyMonomialIso C R n x).hom z) =
    e.hom (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
      (Multiplicative.ofAdd x) • z)
  rw [pairTranslationHomologyModuleForgetIso_monomial_smul]
  change e.hom ((pairTranslationHomologyMonomialIso C R n x).hom z) =
    (pairTranslationHomologyIso C R n x).hom (e.hom z)
  simp [pairTranslationHomologyMonomialIso, e]

/-- Scalar multiplication by every skeleton monomial is bijective on the
monoid-algebra module. -/
theorem pairTranslationHomologyModule_monomial_bijective
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C) :
    Function.Bijective (fun z : pairTranslationHomologyModule C R n =>
      MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
        (Multiplicative.ofAdd x) • z) := by
  have hfun :
      (fun z : pairTranslationHomologyModule C R n =>
        MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd x) • z) =
        fun z => (pairTranslationHomologyMonomialIso C R n x).hom z := by
    funext z
    exact (pairTranslationHomologyMonomialIso_hom_apply C R n x z).symm
  rw [hfun]
  exact (pairTranslationHomologyMonomialIso C R n x).addCommGroupIsoToAddEquiv.bijective

end Homology

end SInverseS
end CategoryTheory

end
