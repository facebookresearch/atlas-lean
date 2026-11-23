/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedFiber
public import MathlibExt.KTheory.Exact.Extension.AuxiliaryUnitRow
public import MathlibExt.KTheory.Exact.Extension.SplitRowInclusion
public import MathlibExt.CategoryTheory.Monoidal.CoreRealizedTranslations
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Monoidal.Action.End
public import MathlibExt.CategoryTheory.FiberedCategory.Cofibered
public import MathlibExt.KTheory.Exact.Extension.ZeroFiberLocalization
public import MathlibExt.CategoryTheory.Monoidal.SInverseSBiprodFunctor
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence
public import MathlibExt.CategoryTheory.NerveCommonHom
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaRealization
public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.Topology.Category.TopCat.WeakHomotopyEquivalenceHomotopy

/-!
# Iterated row projection and original comma transitions

The denominator action, two raw quotients, cofibered lifts and completed strict fibers retain
the original extension rows and denominators. The collapse and split-row comparisons use the
positive-first completed coordinates A,D at independent object and morphism universes.
Canonical nerve and cofibered-realization APIs supply the generic comparison infrastructure.
-/

universe u v
@[expose] public section
open CategoryTheory.MonoidalActionCategory

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The auxiliary object is the original given-X row, with no denominator. -/
def forgetDenominatorObject
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    MonoidalActionCategory (Core C) (FixedTargetExtension C X) := ⟨a.of.1⟩

/-- The raw projection keeps the same stabilizer and entire row arrow. -/
def forgetDenominatorRaw
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (r : RawHom a b) :
    RawHom (forgetDenominatorObject a) (forgetDenominatorObject b) where
  stabilizer := r.stabilizer
  hom := r.hom.1

private theorem forgetDenominatorRaw_rel
    {a b : SInverse (Core C) (FixedTargetExtension C X)} {r s : RawHom a b}
    (h : r.Rel s) : (forgetDenominatorRaw r).Rel (forgetDenominatorRaw s) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  exact congrArg
    (fun q : r.stabilizer ⊙ₗ a.of ⟶ b.of => q.1) he

/-- The original q_X:S-inverse-E_X to L_X functor. -/
def forgetDenominatorFunctor : SInverse (Core C) (FixedTargetExtension C X) ⥤
    MonoidalActionCategory (Core C) (FixedTargetExtension C X) where
  obj := forgetDenominatorObject
  map f := _root_.Quotient.map forgetDenominatorRaw
    (by intro r s h; exact forgetDenominatorRaw_rel h) f
  map_id a := rfl
  map_comp f g := by
    refine _root_.Quotient.inductionOn₂ f g ?_
    intro r s
    rfl

/-- On a represented arrow q_X is exactly the original raw positive projection. -/
theorem forgetDenominatorFunctor_map_mk
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (r : RawHom a b) :
    forgetDenominatorFunctor.map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (forgetDenominatorRaw r) := rfl

/-- Original stabilizer arrows are reflected by their fixed-row action.
The proof projects the native middle Iso through the original biproduct inl/fst. -/
theorem stabilizerAction_injective {T U : Core C} (f g : T ⟶ U)
    (E : FixedTargetExtension C X)
    (h : FixedTargetExtension.leftSumMap f (𝟙 E) =
      FixedTargetExtension.leftSumMap g (𝟙 E)) : f = g := by
  have hb : biprod.map f.iso.hom (𝟙 E.B) = biprod.map g.iso.hom (𝟙 E.B) :=
    (FixedTargetExtension.leftSumMap_b_hom f (𝟙 E)).symm.trans
      ((congrArg
        (fun q : FixedTargetExtension.leftSumObj T E ⟶
          FixedTargetExtension.leftSumObj U E => q.b.hom) h).trans
        (FixedTargetExtension.leftSumMap_b_hom g (𝟙 E)))
  have hc := congrArg
    (fun k : T.of ⊞ E.B ⟶ U.of ⊞ E.B =>
      (biprod.inl : T.of ⟶ T.of ⊞ E.B) ≫ k ≫
        (biprod.fst : U.of ⊞ E.B ⟶ U.of)) hb
  simp only [biprod.inl_map_assoc, biprod.inl_fst, Category.comp_id] at hc
  exact Core.hom_ext hc

end AlgebraicKTheory.FixedTargetExtension.IteratedAction

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

omit [ExactCategory C] in
private theorem core_left_hom (T : Core C) {A B : Core C} (f : A ⟶ B) :
    (T ◁ f).iso.hom = biprod.map (𝟙 T.of) f.iso.hom :=
  (coreBiprodTensorLeft_map_iso_hom T f).trans
    (coreLeftBiprodFunctor_map_iso_hom T.of f)

omit [ExactCategory C] in
private theorem core_right_hom {T U : Core C} (f : T ⟶ U) (A : Core C) :
    (f ▷ A).iso.hom = biprod.map f.iso.hom (𝟙 A.of) := by
  rewrite [← tensorHom_id, coreBiprodTensorHom_iso_hom]
  rfl

omit [ExactCategory C] in
private theorem core_left_unitor_hom (D : Core C) :
    (show (0 : C) ⊞ D.of ⟶ D.of from ((λ_ D).hom).iso.hom) =
      (biprod.snd : (0 : C) ⊞ D.of ⟶ D.of) :=
  congrArg Iso.hom (coreBiprodLeftUnitor_iso D)

omit [ExactCategory C] in
private theorem swap_zero_unit (U D : C) :
    (SInverseS.swapStabilizerIso U (0 : C) D).trans
        (biprod.mapIso (Iso.refl U) (isoZeroBiprod (isZero_zero C)).symm) =
      (isoZeroBiprod (X := (0 : C)) (Y := U ⊞ D) (isZero_zero C)).symm := by
  obtain ⟨e, _, h⟩ := SInverseS.RawHom.translateSecond_id_rel U
    (⟨(0 : C), D⟩ : SInverseS.Pair C)
  let e0 : (0 : C) ≅ 0 := e
  have he : e0 = Iso.refl (0 : C) := by
    apply Iso.ext
    exact (isZero_zero C).eq_of_src _ _
  have h0 : (SInverseS.stabilizerIso e0 (U ⊞ D)).trans
      (isoZeroBiprod (isZero_zero C)).symm =
      (SInverseS.swapStabilizerIso U (0 : C) D).trans
        (biprod.mapIso (Iso.refl U) (isoZeroBiprod (isZero_zero C)).symm) := h
  rw [he, SInverseS.stabilizerIso_refl, Iso.refl_trans] at h0
  exact h0.symm

omit [ExactCategory C] in
private theorem swap_zero_unit_hom (U D : C) :
    (SInverseS.swapStabilizerIso U (0 : C) D).hom ≫
        biprod.map (𝟙 U) (biprod.snd : (0 : C) ⊞ D ⟶ D) =
      (biprod.snd : (0 : C) ⊞ (U ⊞ D) ⟶ U ⊞ D) :=
  congrArg Iso.hom (swap_zero_unit U D)

omit [HasZeroObject C] [ExactCategory C] in
private theorem translated_den_rel (U D B R S : C) (e : R ≅ S)
    (r : R ⊞ D ⟶ B) (s : S ⊞ D ⟶ B)
    (h : biprod.map e.hom (𝟙 D) ≫ s = r) :
    biprod.map e.hom (𝟙 (U ⊞ D)) ≫
        (SInverseS.swapStabilizerIso U S D).hom ≫ biprod.map (𝟙 U) s =
      (SInverseS.swapStabilizerIso U R D).hom ≫ biprod.map (𝟙 U) r := by
  have hn : biprod.map e.hom (𝟙 (U ⊞ D)) ≫
      (SInverseS.swapStabilizerIso U S D).hom =
      (SInverseS.swapStabilizerIso U R D).hom ≫
        biprod.map (𝟙 U) (biprod.map e.hom (𝟙 D)) :=
    congrArg Iso.hom (SInverseS.stabilizerIso_trans_swapStabilizerIso U D e)
  rw [← Category.assoc, hn, Category.assoc,
    ← SInverseS.biprodMap_id_comp U, h]

omit [HasZeroObject C] [ExactCategory C] in
private theorem translated_den_comp (U T R D B Z : C)
    (r : R ⊞ D ⟶ B) (s : T ⊞ B ⟶ Z) :
    (SInverseS.swapStabilizerIso U (T ⊞ R) D).hom ≫
        biprod.map (𝟙 U)
          ((biprod.associator T R D).hom ≫ biprod.map (𝟙 T) r ≫ s) =
      (biprod.associator T R (U ⊞ D)).hom ≫
        biprod.map (𝟙 T)
          ((SInverseS.swapStabilizerIso U R D).hom ≫ biprod.map (𝟙 U) r) ≫
        (SInverseS.swapStabilizerIso U T B).hom ≫ biprod.map (𝟙 U) s := by
  simp only [SInverseS.biprodMap_id_comp, Category.assoc]
  rw [SInverseS.swapStabilizerIso_natural_hom_assoc,
    SInverseS.swapStabilizerIso_hexagon_hom_assoc]

/-- Commute the original stabilizer past the fixed left denominator summand. -/
def denominatorInterchangeIso (U T D : Core C) :
    T ⊗ (U ⊗ D) ≅ U ⊗ (T ⊗ D) :=
  Core.isoMk (SInverseS.swapStabilizerIso U.of T.of D.of)

omit [ExactCategory C] in
/-- The native forward coordinate of the same Core interchange. -/
theorem denominatorInterchangeIso_hom (U T D : Core C) :
    (show T.of ⊞ (U.of ⊞ D.of) ⟶ U.of ⊞ (T.of ⊞ D.of) from
      (denominatorInterchangeIso U T D).hom.iso.hom) =
      (SInverseS.swapStabilizerIso U.of T.of D.of).hom := rfl

/-- Left negative translation changes only the original denominator object. -/
def denominatorLeftObject (U : Core C)
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    SInverse (Core C) (FixedTargetExtension C X) := ⟨(a.of.1, U ⊗ a.of.2)⟩

/-- The raw map retains T and gamma and inserts only the actual denominator interchange. -/
def denominatorLeftRaw (U : Core C)
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (r : RawHom a b) :
    RawHom (denominatorLeftObject U a) (denominatorLeftObject U b) where
  stabilizer := r.stabilizer
  hom := (r.hom.1,
    (denominatorInterchangeIso U r.stabilizer a.of.2).hom ≫ U ◁ r.hom.2)

/-- Its denominator is the explicit published native map, at the original endpoints. -/
theorem denominatorLeftRaw_den_hom (U : Core C)
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (r : RawHom a b) :
    (show r.stabilizer.of ⊞ (U.of ⊞ a.of.2.of) ⟶ U.of ⊞ b.of.2.of from
      (denominatorLeftRaw U r).hom.2.iso.hom) =
      (SInverseS.swapStabilizerIso U.of r.stabilizer.of a.of.2.of).hom ≫
        biprod.map (𝟙 U.of) r.hom.2.iso.hom :=
  congrArg
    (fun k : U.of ⊞ (r.stabilizer.of ⊞ a.of.2.of) ⟶ U.of ⊞ b.of.2.of =>
      (SInverseS.swapStabilizerIso U.of r.stabilizer.of a.of.2.of).hom ≫ k)
    (core_left_hom U (A := r.stabilizer ⊗ a.of.2) (B := b.of.2) r.hom.2)

private theorem raw_comp_den_hom
    {a b c : SInverse (Core C) (FixedTargetExtension C X)}
    (r : RawHom a b) (s : RawHom b c) :
    (show (s.stabilizer.of ⊞ r.stabilizer.of) ⊞ a.of.2.of ⟶ c.of.2.of from
      (r.comp s).hom.2.iso.hom) =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.2.of).hom ≫
        biprod.map (𝟙 s.stabilizer.of) r.hom.2.iso.hom ≫ s.hom.2.iso.hom := by
  have ha := congrArg Iso.hom
    (coreBiprodAssociator_iso s.stabilizer r.stabilizer a.of.2)
  have hr := core_left_hom s.stabilizer
    (A := r.stabilizer ⊗ a.of.2) (B := b.of.2) r.hom.2
  exact congrArg₂
    (fun (h : (s.stabilizer.of ⊞ r.stabilizer.of) ⊞ a.of.2.of ⟶
          s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.2.of))
      (k : s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.2.of) ⟶
          s.stabilizer.of ⊞ b.of.2.of) => h ≫ k ≫ s.hom.2.iso.hom) ha hr

private theorem denominatorLeftRaw_rel (U : Core C)
    {a b : SInverse (Core C) (FixedTargetExtension C X)} {r s : RawHom a b}
    (h : r.Rel s) : (denominatorLeftRaw U r).Rel (denominatorLeftRaw U s) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  apply Prod.ext
  · exact congrArg (fun k : r.stabilizer ⊙ₗ a.of ⟶ b.of => k.1) he
  · apply Core.hom_ext
    have hd0 : (e.hom ▷ a.of.2).iso.hom ≫ s.hom.2.iso.hom = r.hom.2.iso.hom :=
      congrArg (fun k : r.stabilizer ⊙ₗ a.of ⟶ b.of => k.2.iso.hom) he
    have hd : biprod.map e.hom.iso.hom (𝟙 a.of.2.of) ≫
        s.hom.2.iso.hom = r.hom.2.iso.hom :=
      (congrArg (fun k : r.stabilizer.of ⊞ a.of.2.of ⟶
          s.stabilizer.of ⊞ a.of.2.of => k ≫ s.hom.2.iso.hom)
        (core_right_hom e.hom a.of.2)).symm.trans hd0
    change (e.hom ▷ (U ⊗ a.of.2)).iso.hom ≫
        (denominatorLeftRaw U s).hom.2.iso.hom =
      (denominatorLeftRaw U r).hom.2.iso.hom
    have hn := translated_den_rel U.of a.of.2.of b.of.2.of
      r.stabilizer.of s.stabilizer.of e.hom.iso r.hom.2.iso.hom s.hom.2.iso.hom hd
    dsimp only [denominatorLeftObject, denominatorLeftRaw, denominatorInterchangeIso,
      coreCategory_comp_iso, Iso.trans_hom, MonoidalActionCategory.diagonalAction,
      MonoidalActionCategory.productAction, CategoryTheory.MonoidalCategory.selfLeftAction]
    simpa only [core_right_hom, core_left_hom, Core.isoMk_hom_iso, coreBiprodTensorObj_of,
      Category.assoc] using hn

omit [ExactCategory C] in
private theorem denominatorInterchange_unit (U D : Core C) :
    (denominatorInterchangeIso U (𝟙_ (Core C)) D).hom ≫ U ◁ (λ_ D).hom =
      (λ_ (U ⊗ D)).hom := by
  apply Core.hom_ext
  have hw : (U ◁ (λ_ D).hom).iso.hom =
      biprod.map (𝟙 U.of) (biprod.snd : (0 : C) ⊞ D.of ⟶ D.of) := by
    have h1 : (U ◁ (λ_ D).hom).iso.hom =
        biprod.map (𝟙 U.of)
          (show (0 : C) ⊞ D.of ⟶ D.of from ((λ_ D).hom).iso.hom) := by
      simpa only [coreBiprodTensorUnit_of, coreBiprodTensorObj_of] using
        (core_left_hom U (A := (𝟙_ (Core C)) ⊗ D) (B := D) (λ_ D).hom)
    have h2 := core_left_unitor_hom D
    exact h1.trans
      (congrArg (fun k : (0 : C) ⊞ D.of ⟶ D.of => biprod.map (𝟙 U.of) k) h2)
  have hz : ((λ_ (U ⊗ D)).hom).iso.hom =
      (biprod.snd : (0 : C) ⊞ (U.of ⊞ D.of) ⟶ U.of ⊞ D.of) := by
    simpa only [coreBiprodTensorObj_of] using core_left_unitor_hom (U ⊗ D)
  change (denominatorInterchangeIso U (𝟙_ (Core C)) D).hom.iso.hom ≫
      (U ◁ (λ_ D).hom).iso.hom = ((λ_ (U ⊗ D)).hom).iso.hom
  have hn := (congrArg
    (fun k : U.of ⊞ ((0 : C) ⊞ D.of) ⟶ U.of ⊞ D.of =>
      (SInverseS.swapStabilizerIso U.of (0 : C) D.of).hom ≫ k) hw).trans
    ((swap_zero_unit_hom U.of D.of).trans hz.symm)
  simpa only [denominatorInterchangeIso, Core.isoMk_hom_iso,
    coreBiprodTensorObj_of, coreBiprodTensorUnit_of] using hn

private theorem denominatorLeftRaw_id (U : Core C)
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    denominatorLeftRaw U (RawHom.id a) = RawHom.id (denominatorLeftObject U a) := by
  let z := denominatorLeftObject U a
  have hh : (denominatorLeftRaw U (RawHom.id a)).hom = (RawHom.id z).hom := by
    apply Prod.ext
    · rfl
    · change (denominatorInterchangeIso U (𝟙_ (Core C)) a.of.2).hom ≫
          U ◁ (λ_ a.of.2).hom = (λ_ (U ⊗ a.of.2)).hom
      exact denominatorInterchange_unit U a.of.2
  exact congrArg
    (fun k : (𝟙_ (Core C)) ⊙ₗ z.of ⟶ z.of => (⟨𝟙_ (Core C), k⟩ : RawHom z z)) hh

private theorem denominatorLeftRaw_comp (U : Core C)
    {a b c : SInverse (Core C) (FixedTargetExtension C X)}
    (r : RawHom a b) (s : RawHom b c) :
    denominatorLeftRaw U (r.comp s) =
      (denominatorLeftRaw U r).comp (denominatorLeftRaw U s) := by
  let T := s.stabilizer ⊗ r.stabilizer
  let z := denominatorLeftObject U a
  let w := denominatorLeftObject U c
  have hh : ((denominatorLeftRaw U (r.comp s)).hom : T ⊙ₗ z.of ⟶ w.of) =
      ((denominatorLeftRaw U r).comp (denominatorLeftRaw U s)).hom := by
    apply Prod.ext
    · rfl
    · apply Core.hom_ext
      have hl : (denominatorLeftRaw U (r.comp s)).hom.2.iso.hom =
          (SInverseS.swapStabilizerIso U.of
            (s.stabilizer.of ⊞ r.stabilizer.of) a.of.2.of).hom ≫
            biprod.map (𝟙 U.of)
              ((biprod.associator s.stabilizer.of r.stabilizer.of a.of.2.of).hom ≫
                biprod.map (𝟙 s.stabilizer.of) r.hom.2.iso.hom ≫ s.hom.2.iso.hom) := by
        have h1 : (denominatorLeftRaw U (r.comp s)).hom.2.iso.hom =
            (SInverseS.swapStabilizerIso U.of
              (s.stabilizer.of ⊞ r.stabilizer.of) a.of.2.of).hom ≫
              biprod.map (𝟙 U.of) (r.comp s).hom.2.iso.hom := by
          have h := denominatorLeftRaw_den_hom U (r.comp s)
          dsimp only [denominatorLeftObject, denominatorLeftRaw, RawHom.comp] at h ⊢
          simpa only [coreBiprodTensorObj_of] using h
        have h2 := raw_comp_den_hom r s
        exact h1.trans
          (congrArg
            (fun k : (s.stabilizer.of ⊞ r.stabilizer.of) ⊞ a.of.2.of ⟶ c.of.2.of =>
              (SInverseS.swapStabilizerIso U.of
                (s.stabilizer.of ⊞ r.stabilizer.of) a.of.2.of).hom ≫
                  biprod.map (𝟙 U.of) k) h2)
      have hr : ((denominatorLeftRaw U r).comp (denominatorLeftRaw U s)).hom.2.iso.hom =
          (biprod.associator s.stabilizer.of r.stabilizer.of (U.of ⊞ a.of.2.of)).hom ≫
            biprod.map (𝟙 s.stabilizer.of)
              ((SInverseS.swapStabilizerIso U.of r.stabilizer.of a.of.2.of).hom ≫
                biprod.map (𝟙 U.of) r.hom.2.iso.hom) ≫
            (SInverseS.swapStabilizerIso U.of s.stabilizer.of b.of.2.of).hom ≫
              biprod.map (𝟙 U.of) s.hom.2.iso.hom := by
        have h1 : ((denominatorLeftRaw U r).comp
              (denominatorLeftRaw U s)).hom.2.iso.hom =
            (biprod.associator s.stabilizer.of r.stabilizer.of (U.of ⊞ a.of.2.of)).hom ≫
              biprod.map (𝟙 s.stabilizer.of) (denominatorLeftRaw U r).hom.2.iso.hom ≫
                (denominatorLeftRaw U s).hom.2.iso.hom := by
          have h := raw_comp_den_hom (denominatorLeftRaw U r) (denominatorLeftRaw U s)
          dsimp only [denominatorLeftObject, denominatorLeftRaw, RawHom.comp] at h ⊢
          simpa only [coreBiprodTensorObj_of] using h
        have h2 := denominatorLeftRaw_den_hom U r
        have h3 := denominatorLeftRaw_den_hom U s
        exact h1.trans
          (congrArg₂
            (fun (f : r.stabilizer.of ⊞ (U.of ⊞ a.of.2.of) ⟶ U.of ⊞ b.of.2.of)
              (g : s.stabilizer.of ⊞ (U.of ⊞ b.of.2.of) ⟶ U.of ⊞ c.of.2.of) =>
              (biprod.associator s.stabilizer.of r.stabilizer.of
                (U.of ⊞ a.of.2.of)).hom ≫ biprod.map (𝟙 s.stabilizer.of) f ≫ g) h2 h3)
      exact hl.trans ((translated_den_comp U.of s.stabilizer.of r.stabilizer.of
        a.of.2.of b.of.2.of c.of.2.of r.hom.2.iso.hom s.hom.2.iso.hom).trans hr.symm)
  exact congrArg (fun k : T ⊙ₗ z.of ⟶ w.of => (⟨T, k⟩ : RawHom z w)) hh

/-- The derived actual left-negative functor on the same original localized rows. -/
def denominatorLeftFunctor (U : Core C) :
    SInverse (Core C) (FixedTargetExtension C X) ⥤
      SInverse (Core C) (FixedTargetExtension C X) where
  obj := denominatorLeftObject U
  map f := _root_.Quotient.map (denominatorLeftRaw U)
    (by intro r s h; exact denominatorLeftRaw_rel U h) f
  map_id a := by
    exact congrArg MonoidalActionCategory.Hom.mk (denominatorLeftRaw_id U a)
  map_comp f g := by
    refine _root_.Quotient.inductionOn₂ f g ?_
    intro r s
    exact congrArg MonoidalActionCategory.Hom.mk (denominatorLeftRaw_comp U r s)

/-- The functor retains the specific translated raw representative. -/
theorem denominatorLeftFunctor_map_mk (U : Core C)
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (r : RawHom a b) :
    (denominatorLeftFunctor U).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (denominatorLeftRaw U r) := rfl

end AlgebraicKTheory.FixedTargetExtension.IteratedAction

end

/-!
Parameter, ordinary-map, unit and associator coherence for the actual
denominator-left functors uses the existing fixed-functor data.
No action or weak-equivalence assertion is introduced here.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

private theorem rawPostMap_rel
    {S : Type*} [Category* S] [MonoidalCategory S]
    {Y : Type*} [Category* Y] [MonoidalLeftAction S Y]
    {a b c : MonoidalActionCategory S Y} (r : RawHom a b) (f : b.of ⟶ c.of) :
    (r.comp (RawHom.ofMap (S := S) f)).Rel
      (⟨r.stabilizer, r.hom ≫ f⟩ : RawHom a c) := by
  refine ⟨λ_ r.stabilizer, ?_⟩
  simp only [RawHom.comp, RawHom.ofMap,
    MonoidalLeftAction.leftUnitor_actionHom, Category.assoc]
  rw [MonoidalLeftAction.actionUnitIso_hom_naturality_assoc]

private theorem rawPreMap_rel
    {S : Type*} [Category* S] [MonoidalCategory S]
    {Y : Type*} [Category* Y] [MonoidalLeftAction S Y]
    {a b c : MonoidalActionCategory S Y} (f : a.of ⟶ b.of) (r : RawHom b c) :
    ((RawHom.ofMap (S := S) f).comp r).Rel
      (⟨r.stabilizer, r.stabilizer ⊴ₗ f ≫ r.hom⟩ : RawHom a c) := by
  refine ⟨ρ_ r.stabilizer, ?_⟩
  simp only [RawHom.comp, RawHom.ofMap,
    MonoidalLeftAction.rightUnitor_actionHom,
    MonoidalLeftAction.actionHomRight_comp, Category.assoc]

omit [HasZeroObject C] [ExactCategory C] in
private theorem biprodMap_comp
    {A B D E F G : C} (f : A ⟶ B) (g : D ⟶ E) (f' : B ⟶ F) (g' : E ⟶ G) :
    biprod.map f g ≫ biprod.map f' g' = biprod.map (f ≫ f') (g ≫ g') := by
  apply biprod.hom_ext <;> simp [Category.assoc]

omit [HasZeroObject C] [ExactCategory C] in
private theorem swap_parameter_hom {U U' : C} (f : U ⟶ U') (T D : C) :
    biprod.map (𝟙 T) (biprod.map f (𝟙 D)) ≫
        (SInverseS.swapStabilizerIso U' T D).hom =
      (SInverseS.swapStabilizerIso U T D).hom ≫
        biprod.map f (𝟙 (T ⊞ D)) := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext' <;> simp

omit [HasZeroObject C] [ExactCategory C] in
private theorem translated_parameter_naturality (T U U' D B : C)
    (f : U ⟶ U') (d : T ⊞ D ⟶ B) :
    (SInverseS.swapStabilizerIso U T D).hom ≫ biprod.map (𝟙 U) d ≫
        biprod.map f (𝟙 B) =
      biprod.map (𝟙 T) (biprod.map f (𝟙 D)) ≫
        (SInverseS.swapStabilizerIso U' T D).hom ≫ biprod.map (𝟙 U') d := by
  have hl : biprod.map (𝟙 U) d ≫ biprod.map f (𝟙 B) = biprod.map f d := by
    rw [biprodMap_comp, Category.id_comp, Category.comp_id]
  have hr : biprod.map f (𝟙 (T ⊞ D)) ≫ biprod.map (𝟙 U') d =
      biprod.map f d := by
    rw [biprodMap_comp, Category.comp_id, Category.id_comp]
  rw [hl, ← Category.assoc, swap_parameter_hom, Category.assoc, hr]

/-- Scalar maps act through the actual ordinary pair inclusion, fixing the row. -/
def denominatorScalarComponent {U U' : Core C} (f : U ⟶ U')
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    denominatorLeftObject U a ⟶ denominatorLeftObject U' a :=
  (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map
    (X := (a.of.1, U ⊗ a.of.2)) (Y := (a.of.1, U' ⊗ a.of.2))
    (𝟙 a.of.1, f ▷ a.of.2)

private theorem denominatorScalar_naturality_raw {U U' : Core C} (f : U ⟶ U')
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (r : RawHom a b) :
    (denominatorLeftRaw U r).hom ≫
        ((𝟙 b.of.1, f ▷ b.of.2) :
          (b.of.1, U ⊗ b.of.2) ⟶ (b.of.1, U' ⊗ b.of.2)) =
      r.stabilizer ⊴ₗ ((𝟙 a.of.1, f ▷ a.of.2) :
        (a.of.1, U ⊗ a.of.2) ⟶ (a.of.1, U' ⊗ a.of.2)) ≫
        (denominatorLeftRaw U' r).hom := by
  apply Prod.ext
  · change r.hom.1 ≫ 𝟙 b.of.1 =
      r.stabilizer ⊴ₗ (𝟙 a.of.1) ≫ r.hom.1
    rw [MonoidalLeftAction.actionHomRight_id, Category.comp_id, Category.id_comp]
  · apply Core.hom_ext
    change (denominatorLeftRaw U r).hom.2.iso.hom ≫ (f ▷ b.of.2).iso.hom =
      (r.stabilizer ◁ (f ▷ a.of.2)).iso.hom ≫
        (denominatorLeftRaw U' r).hom.2.iso.hom
    have hn := translated_parameter_naturality r.stabilizer.of U.of U'.of
      a.of.2.of b.of.2.of f.iso.hom r.hom.2.iso.hom
    dsimp only [denominatorLeftObject, denominatorLeftRaw, denominatorInterchangeIso,
      coreCategory_comp_iso, Iso.trans_hom, MonoidalActionCategory.diagonalAction,
      MonoidalActionCategory.productAction, CategoryTheory.MonoidalCategory.selfLeftAction]
    simpa only [core_right_hom, core_left_hom, Core.isoMk_hom_iso, coreBiprodTensorObj_of,
      Category.assoc] using hn

/-- Parameter naturality is proved for each original quotient arrow, with its actual T/delta. -/
theorem denominatorScalar_naturality {U U' : Core C} (f : U ⟶ U')
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (g : a ⟶ b) :
    (denominatorLeftFunctor U).map g ≫ denominatorScalarComponent f b =
      denominatorScalarComponent f a ≫ (denominatorLeftFunctor U').map g := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep g
  let A := denominatorLeftObject U a
  let B := denominatorLeftObject U' b
  let fa : A.of ⟶ (denominatorLeftObject U' a).of := (𝟙 a.of.1, f ▷ a.of.2)
  let fb : (denominatorLeftObject U b).of ⟶ B.of := (𝟙 b.of.1, f ▷ b.of.2)
  let l : RawHom A B := ⟨r.stabilizer, (denominatorLeftRaw U r).hom ≫ fb⟩
  let h : RawHom A B :=
    ⟨r.stabilizer, r.stabilizer ⊴ₗ fa ≫ (denominatorLeftRaw U' r).hom⟩
  have hlh : l = h := congrArg
    (fun k : r.stabilizer ⊙ₗ A.of ⟶ B.of => (⟨r.stabilizer, k⟩ : RawHom A B))
    (denominatorScalar_naturality_raw f r)
  change MonoidalActionCategory.Hom.mk
      ((denominatorLeftRaw U r).comp (RawHom.ofMap (S := Core C) fb)) =
    MonoidalActionCategory.Hom.mk ((RawHom.ofMap (S := Core C) fa).comp (denominatorLeftRaw U' r))
  exact (_root_.Quotient.sound (rawPostMap_rel (denominatorLeftRaw U r) fb)).trans
    ((congrArg MonoidalActionCategory.Hom.mk hlh).trans
      (_root_.Quotient.sound (rawPreMap_rel fa (denominatorLeftRaw U' r))).symm)

/-- The parameter transformation, derived from the original scalar component. -/
def denominatorScalarNatTrans {U U' : Core C} (f : U ⟶ U') :
    denominatorLeftFunctor (C := C) (X := X) U ⟶ denominatorLeftFunctor U' where
  app := denominatorScalarComponent f
  naturality {a b} g := by
    exact denominatorScalar_naturality f g

private theorem denominatorScalar_id (U : Core C)
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    denominatorScalarComponent (𝟙 U) a = 𝟙 (denominatorLeftObject U a) := by
  change (MonoidalActionCategory.inclusion (Core C)
      (FixedTargetExtension C X × Core C)).map
      ((𝟙 a.of.1, (𝟙 U) ▷ a.of.2) :
        (a.of.1, U ⊗ a.of.2) ⟶ (a.of.1, U ⊗ a.of.2)) = 𝟙 _
  rw [MonoidalCategory.id_whiskerRight]
  exact CategoryTheory.Functor.map_id _ _

private theorem denominatorScalar_comp {U U' U'' : Core C} (f : U ⟶ U') (g : U' ⟶ U'')
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    denominatorScalarComponent f a ≫ denominatorScalarComponent g a =
      denominatorScalarComponent (f ≫ g) a := by
  let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
  change I.map ((𝟙 a.of.1, f ▷ a.of.2) :
      (a.of.1, U ⊗ a.of.2) ⟶ (a.of.1, U' ⊗ a.of.2)) ≫
      I.map ((𝟙 a.of.1, g ▷ a.of.2) :
        (a.of.1, U' ⊗ a.of.2) ⟶ (a.of.1, U'' ⊗ a.of.2)) =
    I.map ((𝟙 a.of.1, (f ≫ g) ▷ a.of.2) :
      (a.of.1, U ⊗ a.of.2) ⟶ (a.of.1, U'' ⊗ a.of.2))
  rw [← CategoryTheory.Functor.map_comp]
  apply congrArg (fun k : (a.of.1, U ⊗ a.of.2) ⟶
      (a.of.1, U'' ⊗ a.of.2) => I.map k)
  apply Prod.ext
  · exact Category.id_comp _
  · exact (MonoidalCategory.comp_whiskerRight f g a.of.2).symm

/-- The actual family of left-denominator functors, including scalar maps. -/
def denominatorLeftCurriedFunctor : Core C ⥤
    (SInverse (Core C) (FixedTargetExtension C X) ⥤
      SInverse (Core C) (FixedTargetExtension C X)) where
  obj := denominatorLeftFunctor
  map := denominatorScalarNatTrans
  map_id U := by
    apply NatTrans.ext
    funext a
    change denominatorScalarComponent (𝟙 U) a = 𝟙 (denominatorLeftObject U a)
    exact denominatorScalar_id U a
  map_comp f g := by
    apply NatTrans.ext
    funext a
    change denominatorScalarComponent (f ≫ g) a =
      denominatorScalarComponent f a ≫ denominatorScalarComponent g a
    exact (denominatorScalar_comp f g a).symm



/-- Ordinary original row/core maps are translated by the original Core tensor map. -/
theorem denominatorLeftFunctor_map_inclusion (U : Core C)
    {E F : FixedTargetExtension C X} {D D' : Core C} (g : E ⟶ F) (d : D ⟶ D') :
    (denominatorLeftFunctor U).map
        ((MonoidalActionCategory.inclusion (Core C)
          (FixedTargetExtension C X × Core C)).map
          (X := (E, D)) (Y := (F, D')) (g, d)) =
      (MonoidalActionCategory.inclusion (Core C)
        (FixedTargetExtension C X × Core C)).map
        (X := (E, U ⊗ D)) (Y := (F, U ⊗ D')) (g, U ◁ d) := by
  let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
  let a : SInverse (Core C) (FixedTargetExtension C X) := I.obj (E, D)
  let b : SInverse (Core C) (FixedTargetExtension C X) := I.obj (F, D')
  let r : RawHom a b := RawHom.ofMap (S := Core C)
    (show (E, D) ⟶ (F, D') from (g, d))
  let t : RawHom (denominatorLeftObject U a) (denominatorLeftObject U b) :=
    RawHom.ofMap (S := Core C)
      (show (E, U ⊗ D) ⟶ (F, U ⊗ D') from (g, U ◁ d))
  have hi : (denominatorInterchangeIso U (𝟙_ (Core C)) D).hom ≫
      U ◁ (λ_ D).hom = (λ_ (U ⊗ D)).hom :=
    denominatorInterchange_unit U D
  have hh : (denominatorLeftRaw U r).hom = t.hom := by
    apply Prod.ext
    · rfl
    · change (denominatorInterchangeIso U (𝟙_ (Core C)) D).hom ≫
          U ◁ ((λ_ D).hom ≫ d) = (λ_ (U ⊗ D)).hom ≫ U ◁ d
      rw [MonoidalCategory.whiskerLeft_comp, ← Category.assoc, hi]
  have ht : denominatorLeftRaw U r = t := congrArg
    (fun k : (𝟙_ (Core C)) ⊙ₗ (denominatorLeftObject U a).of ⟶
        (denominatorLeftObject U b).of =>
      (⟨𝟙_ (Core C), k⟩ :
        RawHom (denominatorLeftObject U a) (denominatorLeftObject U b))) hh
  change MonoidalActionCategory.Hom.mk (denominatorLeftRaw U r) = MonoidalActionCategory.Hom.mk t
  exact congrArg MonoidalActionCategory.Hom.mk ht

omit [ExactCategory C] in
private theorem swap_fixed_zero_hom (T D : C) :
    (SInverseS.swapStabilizerIso (0 : C) T D).hom ≫
        (biprod.snd : (0 : C) ⊞ (T ⊞ D) ⟶ T ⊞ D) =
      biprod.map (𝟙 T) (biprod.snd : (0 : C) ⊞ D ⟶ D) := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext'
    · exact (isZero_zero C).eq_of_src _ _
    · simp

omit [ExactCategory C] in
private theorem translated_zero_naturality (T D B : C) (d : T ⊞ D ⟶ B) :
    (SInverseS.swapStabilizerIso (0 : C) T D).hom ≫
        biprod.map (𝟙 (0 : C)) d ≫ (biprod.snd : (0 : C) ⊞ B ⟶ B) =
      biprod.map (𝟙 T) (biprod.snd : (0 : C) ⊞ D ⟶ D) ≫ d := by
  rw [biprod.map_snd, ← Category.assoc, swap_fixed_zero_hom]

omit [ExactCategory C] in
private theorem denominatorInterchange_left_unit (T D : Core C) :
    (denominatorInterchangeIso (𝟙_ (Core C)) T D).hom ≫ (λ_ (T ⊗ D)).hom =
      T ◁ (λ_ D).hom := by
  apply Core.hom_ext
  have hn := swap_fixed_zero_hom T.of D.of
  dsimp only [denominatorInterchangeIso, coreCategory_comp_iso, Iso.trans_hom]
  simpa only [Core.isoMk_hom_iso, core_left_unitor_hom, core_left_hom,
    coreBiprodTensorObj_of, coreBiprodTensorUnit_of] using hn

/-- The ordinary zero-left unitor component at the original inner denominator. -/
def denominatorUnitComponent (a : SInverse (Core C) (FixedTargetExtension C X)) :
    denominatorLeftObject (𝟙_ (Core C)) a ≅ a :=
  (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).mapIso
    ((Iso.refl a.of.1).prod (λ_ a.of.2))

private theorem denominatorUnit_naturality_raw
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (r : RawHom a b) :
    (denominatorLeftRaw (𝟙_ (Core C)) r).hom ≫
        ((𝟙 b.of.1, (λ_ b.of.2).hom) :
          (b.of.1, (𝟙_ (Core C)) ⊗ b.of.2) ⟶ b.of) =
      r.stabilizer ⊴ₗ ((𝟙 a.of.1, (λ_ a.of.2).hom) :
        (a.of.1, (𝟙_ (Core C)) ⊗ a.of.2) ⟶ a.of) ≫ r.hom := by
  apply Prod.ext
  · change r.hom.1 ≫ 𝟙 b.of.1 =
      r.stabilizer ⊴ₗ (𝟙 a.of.1) ≫ r.hom.1
    rw [MonoidalLeftAction.actionHomRight_id, Category.comp_id, Category.id_comp]
  · change
      ((denominatorInterchangeIso (𝟙_ (Core C)) r.stabilizer a.of.2).hom ≫
        ((𝟙_ (Core C)) ◁ r.hom.2)) ≫ (λ_ b.of.2).hom =
      (r.stabilizer ◁ (λ_ a.of.2).hom) ≫ r.hom.2
    rw [Category.assoc, MonoidalCategory.leftUnitor_naturality,
      ← Category.assoc, denominatorInterchange_left_unit]

/-- The unit comparison is natural for every original raw stabilizer and denominator. -/
theorem denominatorUnit_naturality
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (f : a ⟶ b) :
    (denominatorLeftFunctor (𝟙_ (Core C))).map f ≫ (denominatorUnitComponent b).hom =
      (denominatorUnitComponent a).hom ≫ f := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  let A := denominatorLeftObject (𝟙_ (Core C)) a
  let fa : A.of ⟶ a.of := (𝟙 a.of.1, (λ_ a.of.2).hom)
  let fb : (denominatorLeftObject (𝟙_ (Core C)) b).of ⟶ b.of :=
    (𝟙 b.of.1, (λ_ b.of.2).hom)
  let l : RawHom A b :=
    ⟨r.stabilizer, (denominatorLeftRaw (𝟙_ (Core C)) r).hom ≫ fb⟩
  let h : RawHom A b := ⟨r.stabilizer, r.stabilizer ⊴ₗ fa ≫ r.hom⟩
  have hlh : l = h := congrArg
    (fun k : r.stabilizer ⊙ₗ A.of ⟶ b.of => (⟨r.stabilizer, k⟩ : RawHom A b))
    (denominatorUnit_naturality_raw r)
  change MonoidalActionCategory.Hom.mk
      ((denominatorLeftRaw (𝟙_ (Core C)) r).comp (RawHom.ofMap (S := Core C) fb)) =
    MonoidalActionCategory.Hom.mk ((RawHom.ofMap (S := Core C) fa).comp r)
  exact (_root_.Quotient.sound
      (rawPostMap_rel (denominatorLeftRaw (𝟙_ (Core C)) r) fb)).trans
    ((congrArg MonoidalActionCategory.Hom.mk hlh).trans
      (_root_.Quotient.sound (rawPreMap_rel fa r)).symm)

/-- The actual unit NatIso; no unit coherence or equivalence is supplied. -/
def denominatorUnitNatIso : denominatorLeftFunctor (C := C) (X := X)
    (𝟙_ (Core C)) ≅ 𝟭 (SInverse (Core C) (FixedTargetExtension C X)) :=
  NatIso.ofComponents denominatorUnitComponent (by
    intro a b f
    exact denominatorUnit_naturality f)

omit [HasZeroObject C] [ExactCategory C] in
private theorem swap_fixed_sum_hom (U V T D : C) :
    (SInverseS.swapStabilizerIso (U ⊞ V) T D).hom ≫
        (biprod.associator U V (T ⊞ D)).hom =
      biprod.map (𝟙 T) (biprod.associator U V D).hom ≫
        (SInverseS.swapStabilizerIso U T (V ⊞ D)).hom ≫
        biprod.map (𝟙 U) (SInverseS.swapStabilizerIso V T D).hom := by
  apply biprod.hom_ext
  · simp [SInverseS.swapStabilizerIso, biprod.associator, Category.assoc]
  · apply biprod.hom_ext
    · simp [SInverseS.swapStabilizerIso, biprod.associator, Category.assoc]
    · apply biprod.hom_ext
      · simp [SInverseS.swapStabilizerIso, biprod.associator, Category.assoc]
      · simp [SInverseS.swapStabilizerIso, biprod.associator, Category.assoc]

omit [HasZeroObject C] [ExactCategory C] in
private theorem translated_associator_naturality (U V T D B : C) (d : T ⊞ D ⟶ B) :
    (SInverseS.swapStabilizerIso (U ⊞ V) T D).hom ≫
        biprod.map (𝟙 (U ⊞ V)) d ≫ (biprod.associator U V B).hom =
      biprod.map (𝟙 T) (biprod.associator U V D).hom ≫
        (SInverseS.swapStabilizerIso U T (V ⊞ D)).hom ≫
        biprod.map (𝟙 U)
          ((SInverseS.swapStabilizerIso V T D).hom ≫ biprod.map (𝟙 V) d) := by
  have hid : biprod.map (𝟙 U) (𝟙 V) = 𝟙 (U ⊞ V) := by
    apply biprod.hom_ext <;> simp
  have hn : biprod.map (𝟙 (U ⊞ V)) d ≫ (biprod.associator U V B).hom =
      (biprod.associator U V (T ⊞ D)).hom ≫
        biprod.map (𝟙 U) (biprod.map (𝟙 V) d) := by
    have h := biprod.associator_natural (𝟙 U) (𝟙 V) d
    rw [hid] at h
    exact h
  rw [hn]
  simp only [SInverseS.biprodMap_id_comp]
  have h := congrArg
    (fun k : T ⊞ ((U ⊞ V) ⊞ D) ⟶ U ⊞ (V ⊞ (T ⊞ D)) =>
      k ≫ biprod.map (𝟙 U) (biprod.map (𝟙 V) d)) (swap_fixed_sum_hom U V T D)
  simp only [Category.assoc] at h
  exact h

omit [ExactCategory C] in
private theorem core_associator_hom (U V D : Core C) :
    ((α_ U V D).hom).iso.hom = (biprod.associator U.of V.of D.of).hom :=
  congrArg Iso.hom (coreBiprodAssociator_iso U V D)

/-- The actual associator of the two prepended denominator summands. -/
def denominatorAssocComponent (U V : Core C)
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    denominatorLeftObject (U ⊗ V) a ≅
      denominatorLeftObject U (denominatorLeftObject V a) :=
  (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).mapIso
    ((Iso.refl a.of.1).prod (α_ U V a.of.2))

private theorem denominatorAssoc_naturality_raw (U V : Core C)
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (r : RawHom a b) :
    (denominatorLeftRaw (U ⊗ V) r).hom ≫
        ((𝟙 b.of.1, (α_ U V b.of.2).hom) :
          (b.of.1, (U ⊗ V) ⊗ b.of.2) ⟶ (b.of.1, U ⊗ (V ⊗ b.of.2))) =
      r.stabilizer ⊴ₗ ((𝟙 a.of.1, (α_ U V a.of.2).hom) :
        (a.of.1, (U ⊗ V) ⊗ a.of.2) ⟶ (a.of.1, U ⊗ (V ⊗ a.of.2))) ≫
        (denominatorLeftRaw U (denominatorLeftRaw V r)).hom := by
  apply Prod.ext
  · change r.hom.1 ≫ 𝟙 b.of.1 =
      r.stabilizer ⊴ₗ (𝟙 a.of.1) ≫ r.hom.1
    rw [MonoidalLeftAction.actionHomRight_id, Category.comp_id, Category.id_comp]
  · apply Core.hom_ext
    change (denominatorLeftRaw (U ⊗ V) r).hom.2.iso.hom ≫
        ((α_ U V b.of.2).hom).iso.hom =
      (r.stabilizer ◁ (α_ U V a.of.2).hom).iso.hom ≫
        (denominatorLeftRaw U (denominatorLeftRaw V r)).hom.2.iso.hom
    have hn := translated_associator_naturality U.of V.of r.stabilizer.of
      a.of.2.of b.of.2.of r.hom.2.iso.hom
    dsimp only [denominatorLeftObject, denominatorLeftRaw, denominatorInterchangeIso,
      coreCategory_comp_iso, Iso.trans_hom, MonoidalActionCategory.diagonalAction,
      MonoidalActionCategory.productAction, CategoryTheory.MonoidalCategory.selfLeftAction]
    simpa only [core_left_hom, core_associator_hom, coreCategory_comp_iso,
      Iso.trans_hom, Core.isoMk_hom_iso, coreBiprodTensorObj_of, Category.assoc] using hn

/-- The denominator associator is natural on every original quotient arrow. -/
theorem denominatorAssoc_naturality (U V : Core C)
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (f : a ⟶ b) :
    (denominatorLeftFunctor (U ⊗ V)).map f ≫ (denominatorAssocComponent U V b).hom =
      (denominatorAssocComponent U V a).hom ≫
        (denominatorLeftFunctor U).map ((denominatorLeftFunctor V).map f) := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  let A := denominatorLeftObject (U ⊗ V) a
  let B := denominatorLeftObject U (denominatorLeftObject V b)
  let fa : A.of ⟶ (denominatorLeftObject U (denominatorLeftObject V a)).of :=
    (𝟙 a.of.1, (α_ U V a.of.2).hom)
  let fb : (denominatorLeftObject (U ⊗ V) b).of ⟶ B.of :=
    (𝟙 b.of.1, (α_ U V b.of.2).hom)
  let l : RawHom A B := ⟨r.stabilizer, (denominatorLeftRaw (U ⊗ V) r).hom ≫ fb⟩
  let h : RawHom A B :=
    ⟨r.stabilizer, r.stabilizer ⊴ₗ fa ≫
      (denominatorLeftRaw U (denominatorLeftRaw V r)).hom⟩
  have hlh : l = h := congrArg
    (fun k : r.stabilizer ⊙ₗ A.of ⟶ B.of => (⟨r.stabilizer, k⟩ : RawHom A B))
    (denominatorAssoc_naturality_raw U V r)
  change MonoidalActionCategory.Hom.mk ((denominatorLeftRaw (U ⊗ V) r).comp
      (RawHom.ofMap (S := Core C) fb)) =
    MonoidalActionCategory.Hom.mk ((RawHom.ofMap (S := Core C) fa).comp
      (denominatorLeftRaw U (denominatorLeftRaw V r)))
  exact (_root_.Quotient.sound (rawPostMap_rel (denominatorLeftRaw (U ⊗ V) r) fb)).trans
    ((congrArg MonoidalActionCategory.Hom.mk hlh).trans
      (_root_.Quotient.sound
        (rawPreMap_rel fa (denominatorLeftRaw U (denominatorLeftRaw V r)))).symm)

/-- Translation by U tensor V is translation by V followed by U. -/
def denominatorAssocNatIso (U V : Core C) :
    denominatorLeftFunctor (C := C) (X := X) (U ⊗ V) ≅
      denominatorLeftFunctor V ⋙ denominatorLeftFunctor U :=
  NatIso.ofComponents (denominatorAssocComponent U V) (by
    intro a b f
    exact denominatorAssoc_naturality U V f)

attribute [local instance] endofunctorMonoidalCategory

/-- The actual scalar family in the composition monoidal-opposite of endofunctors. -/
def denominatorLeftCurriedMop : Core C ⥤
    (SInverse (Core C) (FixedTargetExtension C X) ⥤
      SInverse (Core C) (FixedTargetExtension C X))ᴹᵒᵖ :=
  denominatorLeftCurriedFunctor ⋙ CategoryTheory.mopFunctor _

/-- All monoidal data are the original pair unitors/associators. Their five
coherence equations are derived below; none is supplied as a witness. -/
def denominatorLeftCoreMonoidal :
    (denominatorLeftCurriedMop (C := C) (X := X)).CoreMonoidal where
  εIso := (CategoryTheory.mopFunctor _).mapIso
    (denominatorUnitNatIso.symm)
  μIso U V :=
    (CategoryTheory.mopFunctor _).mapIso
      ((denominatorAssocNatIso U V).symm)
  μIso_hom_natural_left {U U'} f V := by
    apply MonoidalOpposite.hom_ext
    apply NatTrans.ext
    funext a
    change denominatorScalarComponent f (denominatorLeftObject V a) ≫
        (denominatorAssocComponent U' V a).inv =
      (denominatorAssocComponent U V a).inv ≫ denominatorScalarComponent (f ▷ V) a
    let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
    change I.map ((𝟙 a.of.1, f ▷ (V ⊗ a.of.2)) :
        (a.of.1, U ⊗ (V ⊗ a.of.2)) ⟶ (a.of.1, U' ⊗ (V ⊗ a.of.2))) ≫
        I.map ((𝟙 a.of.1, (α_ U' V a.of.2).inv) :
          (a.of.1, U' ⊗ (V ⊗ a.of.2)) ⟶ (a.of.1, (U' ⊗ V) ⊗ a.of.2)) =
      I.map ((𝟙 a.of.1, (α_ U V a.of.2).inv) :
        (a.of.1, U ⊗ (V ⊗ a.of.2)) ⟶ (a.of.1, (U ⊗ V) ⊗ a.of.2)) ≫
        I.map ((𝟙 a.of.1, (f ▷ V) ▷ a.of.2) :
          (a.of.1, (U ⊗ V) ⊗ a.of.2) ⟶ (a.of.1, (U' ⊗ V) ⊗ a.of.2))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    apply congrArg (fun k : (a.of.1, U ⊗ (V ⊗ a.of.2)) ⟶
        (a.of.1, (U' ⊗ V) ⊗ a.of.2) => I.map k)
    apply Prod.ext
    · rfl
    · exact MonoidalCategory.associator_inv_naturality_left f V a.of.2
  μIso_hom_natural_right {V V'} U f := by
    apply MonoidalOpposite.hom_ext
    apply NatTrans.ext
    funext a
    change (denominatorLeftFunctor U).map (denominatorScalarComponent f a) ≫
        (denominatorAssocComponent U V' a).inv =
      (denominatorAssocComponent U V a).inv ≫ denominatorScalarComponent (U ◁ f) a
    let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
    have hPair :
        (@CategoryStruct.comp (FixedTargetExtension C X × Core C) _
        (a.of.1, U ⊗ (V ⊗ a.of.2)) (a.of.1, U ⊗ (V' ⊗ a.of.2))
        (a.of.1, (U ⊗ V') ⊗ a.of.2)
        (𝟙 a.of.1, U ◁ (f ▷ a.of.2))
        (𝟙 a.of.1, (α_ U V' a.of.2).inv)) =
        (@CategoryStruct.comp (FixedTargetExtension C X × Core C) _
        (a.of.1, U ⊗ (V ⊗ a.of.2)) (a.of.1, (U ⊗ V) ⊗ a.of.2)
        (a.of.1, (U ⊗ V') ⊗ a.of.2)
        (𝟙 a.of.1, (α_ U V a.of.2).inv)
        (𝟙 a.of.1, (U ◁ f) ▷ a.of.2)) := by
      apply Prod.ext
      · rfl
      · change (U ◁ (f ▷ a.of.2)) ≫ (α_ U V' a.of.2).inv =
          (α_ U V a.of.2).inv ≫ ((U ◁ f) ▷ a.of.2)
        exact MonoidalCategory.associator_inv_naturality_middle U f a.of.2
    have hMap := congrArg
      (fun k : (a.of.1, U ⊗ (V ⊗ a.of.2)) ⟶
        (a.of.1, (U ⊗ V') ⊗ a.of.2) => I.map k) hPair
    simp only [CategoryTheory.Functor.map_comp] at hMap
    have hTranslated :
        (denominatorLeftFunctor U).map (X := denominatorLeftObject V a)
          (Y := denominatorLeftObject V' a) (denominatorScalarComponent f a) =
        I.map (X := (a.of.1, U ⊗ (V ⊗ a.of.2)))
          (Y := (a.of.1, U ⊗ (V' ⊗ a.of.2)))
          (𝟙 a.of.1, U ◁ (f ▷ a.of.2)) := by
      change (denominatorLeftFunctor U).map
          (I.map (X := (a.of.1, V ⊗ a.of.2)) (Y := (a.of.1, V' ⊗ a.of.2))
            (𝟙 a.of.1, f ▷ a.of.2)) = _
      exact denominatorLeftFunctor_map_inclusion U (𝟙 a.of.1) (f ▷ a.of.2)
    dsimp only [denominatorLeftFunctor] at hTranslated ⊢
    rw [hTranslated]
    simpa only [I, denominatorScalarComponent, denominatorAssocComponent,
      CategoryTheory.Functor.mapIso_inv, Iso.prod, Iso.refl,
      denominatorLeftObject, MonoidalActionCategory.inclusion] using hMap
  associativity U V W := by
    apply MonoidalOpposite.hom_ext
    apply NatTrans.ext
    funext a
    change (denominatorAssocComponent U V (denominatorLeftObject W a)).inv ≫
        (denominatorAssocComponent (U ⊗ V) W a).inv ≫
        denominatorScalarComponent (α_ U V W).hom a =
      (𝟙 (denominatorLeftObject U
        (denominatorLeftObject V (denominatorLeftObject W a)))) ≫
        (denominatorLeftFunctor U).map ((denominatorAssocComponent V W a).inv) ≫
          (denominatorAssocComponent U (V ⊗ W) a).inv
    rw [Category.id_comp]
    let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
    have hPair :
        (@CategoryStruct.comp (FixedTargetExtension C X × Core C) _
        (a.of.1, U ⊗ (V ⊗ (W ⊗ a.of.2))) (a.of.1, (U ⊗ V) ⊗ (W ⊗ a.of.2))
        (a.of.1, (U ⊗ (V ⊗ W)) ⊗ a.of.2)
        (𝟙 a.of.1, (α_ U V (W ⊗ a.of.2)).inv)
        (@CategoryStruct.comp (FixedTargetExtension C X × Core C) _
        (a.of.1, (U ⊗ V) ⊗ (W ⊗ a.of.2)) (a.of.1, ((U ⊗ V) ⊗ W) ⊗ a.of.2)
        (a.of.1, (U ⊗ (V ⊗ W)) ⊗ a.of.2)
        (𝟙 a.of.1, (α_ (U ⊗ V) W a.of.2).inv)
        (𝟙 a.of.1, (α_ U V W).hom ▷ a.of.2))) =
        (@CategoryStruct.comp (FixedTargetExtension C X × Core C) _
        (a.of.1, U ⊗ (V ⊗ (W ⊗ a.of.2))) (a.of.1, U ⊗ ((V ⊗ W) ⊗ a.of.2))
        (a.of.1, (U ⊗ (V ⊗ W)) ⊗ a.of.2)
        (𝟙 a.of.1, U ◁ (α_ V W a.of.2).inv)
        (𝟙 a.of.1, (α_ U (V ⊗ W) a.of.2).inv)) := by
      apply Prod.ext
      · change (𝟙 a.of.1) ≫ 𝟙 a.of.1 ≫ 𝟙 a.of.1 = (𝟙 a.of.1) ≫ 𝟙 a.of.1
        simp only [Category.id_comp]
      · change (α_ U V (W ⊗ a.of.2)).inv ≫
          (α_ (U ⊗ V) W a.of.2).inv ≫ ((α_ U V W).hom ▷ a.of.2) =
          (U ◁ (α_ V W a.of.2).inv) ≫ (α_ U (V ⊗ W) a.of.2).inv
        exact MonoidalCategory.pentagon_inv_inv_hom_inv_inv
    have hMap := congrArg
      (fun k : (a.of.1, U ⊗ (V ⊗ (W ⊗ a.of.2))) ⟶
        (a.of.1, (U ⊗ (V ⊗ W)) ⊗ a.of.2) => I.map k) hPair
    simp only [CategoryTheory.Functor.map_comp] at hMap
    have hTranslated :
        (denominatorLeftFunctor U).map
          (X := denominatorLeftObject V (denominatorLeftObject W a))
          (Y := denominatorLeftObject (V ⊗ W) a) (denominatorAssocComponent V W a).inv =
        I.map (X := (a.of.1, U ⊗ (V ⊗ (W ⊗ a.of.2))))
          (Y := (a.of.1, U ⊗ ((V ⊗ W) ⊗ a.of.2)))
          (𝟙 a.of.1, U ◁ (α_ V W a.of.2).inv) := by
      change (denominatorLeftFunctor U).map
          (I.map (X := (a.of.1, V ⊗ (W ⊗ a.of.2)))
            (Y := (a.of.1, (V ⊗ W) ⊗ a.of.2))
            (𝟙 a.of.1, (α_ V W a.of.2).inv)) = _
      exact denominatorLeftFunctor_map_inclusion U (𝟙 a.of.1) (α_ V W a.of.2).inv
    dsimp only [denominatorLeftFunctor] at hTranslated ⊢
    rw [hTranslated]
    simpa only [I, denominatorScalarComponent, denominatorAssocComponent,
      CategoryTheory.Functor.mapIso_inv, Iso.prod, Iso.refl,
      denominatorLeftObject, MonoidalActionCategory.inclusion] using hMap
  left_unitality U := by
    apply MonoidalOpposite.hom_ext
    apply NatTrans.ext
    funext a
    change (𝟙 (denominatorLeftObject U a)) =
      (denominatorUnitComponent (denominatorLeftObject U a)).inv ≫
        (denominatorAssocComponent (𝟙_ (Core C)) U a).inv ≫
          denominatorScalarComponent (λ_ U).hom a
    let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
    dsimp only [denominatorLeftObject]
    change 𝟙 (I.obj (a.of.1, U ⊗ a.of.2)) = _
    rw [← I.map_id (a.of.1, U ⊗ a.of.2)]
    change I.map (𝟙 (a.of.1, U ⊗ a.of.2)) =
      I.map ((𝟙 a.of.1, (λ_ (U ⊗ a.of.2)).inv) :
        (a.of.1, U ⊗ a.of.2) ⟶ (a.of.1, (𝟙_ (Core C)) ⊗ (U ⊗ a.of.2))) ≫
        I.map ((𝟙 a.of.1, (α_ (𝟙_ (Core C)) U a.of.2).inv) :
          (a.of.1, (𝟙_ (Core C)) ⊗ (U ⊗ a.of.2)) ⟶
            (a.of.1, ((𝟙_ (Core C)) ⊗ U) ⊗ a.of.2)) ≫
        I.map ((𝟙 a.of.1, (λ_ U).hom ▷ a.of.2) :
          (a.of.1, ((𝟙_ (Core C)) ⊗ U) ⊗ a.of.2) ⟶ (a.of.1, U ⊗ a.of.2))
    simp only [← CategoryTheory.Functor.map_comp]
    apply congrArg (fun k : (a.of.1, U ⊗ a.of.2) ⟶
        (a.of.1, U ⊗ a.of.2) => I.map k)
    apply Prod.ext
    · simp
    · change 𝟙 (U ⊗ a.of.2) = (λ_ (U ⊗ a.of.2)).inv ≫
        (α_ (𝟙_ (Core C)) U a.of.2).inv ≫ ((λ_ U).hom ▷ a.of.2)
      rw [← MonoidalCategory.leftUnitor_tensor_hom, Iso.inv_hom_id]
  right_unitality U := by
    apply MonoidalOpposite.hom_ext
    apply NatTrans.ext
    funext a
    change (𝟙 (denominatorLeftObject U a)) =
      (denominatorLeftFunctor U).map ((denominatorUnitComponent a).inv) ≫
        (denominatorAssocComponent U (𝟙_ (Core C)) a).inv ≫
          denominatorScalarComponent (ρ_ U).hom a
    let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
    have hPair :
        (𝟙 (a.of.1, U ⊗ a.of.2)) =
        ((𝟙 a.of.1, U ◁ (λ_ a.of.2).inv) :
          (a.of.1, U ⊗ a.of.2) ⟶ (a.of.1, U ⊗ ((𝟙_ (Core C)) ⊗ a.of.2))) ≫
          ((𝟙 a.of.1, (α_ U (𝟙_ (Core C)) a.of.2).inv) :
            (a.of.1, U ⊗ ((𝟙_ (Core C)) ⊗ a.of.2)) ⟶
              (a.of.1, (U ⊗ (𝟙_ (Core C))) ⊗ a.of.2)) ≫
          ((𝟙 a.of.1, (ρ_ U).hom ▷ a.of.2) :
            (a.of.1, (U ⊗ (𝟙_ (Core C))) ⊗ a.of.2) ⟶ (a.of.1, U ⊗ a.of.2)) := by
      apply Prod.ext
      · change 𝟙 a.of.1 = (𝟙 a.of.1) ≫ 𝟙 a.of.1 ≫ 𝟙 a.of.1
        simp only [Category.id_comp]
      · change 𝟙 (U ⊗ a.of.2) = (U ◁ (λ_ a.of.2).inv) ≫
          (α_ U (𝟙_ (Core C)) a.of.2).inv ≫ ((ρ_ U).hom ▷ a.of.2)
        rw [← MonoidalCategory.triangle, Iso.inv_hom_id_assoc,
          ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
          MonoidalCategory.whiskerLeft_id]
    have hMap := congrArg
      (fun k : (a.of.1, U ⊗ a.of.2) ⟶ (a.of.1, U ⊗ a.of.2) => I.map k) hPair
    simp only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp] at hMap
    have hTranslated :
        (denominatorLeftFunctor U).map (X := a)
          (Y := denominatorLeftObject (𝟙_ (Core C)) a) (denominatorUnitComponent a).inv =
        I.map (X := (a.of.1, U ⊗ a.of.2))
          (Y := (a.of.1, U ⊗ ((𝟙_ (Core C)) ⊗ a.of.2)))
          (𝟙 a.of.1, U ◁ (λ_ a.of.2).inv) := by
      change (denominatorLeftFunctor U).map
          (I.map (X := a.of) (Y := (a.of.1, (𝟙_ (Core C)) ⊗ a.of.2))
            (𝟙 a.of.1, (λ_ a.of.2).inv)) = _
      exact denominatorLeftFunctor_map_inclusion U (𝟙 a.of.1) (λ_ a.of.2).inv
    dsimp only [denominatorLeftFunctor] at hTranslated ⊢
    rw [hTranslated]
    simpa only [I, denominatorScalarComponent,
      denominatorAssocComponent,
      CategoryTheory.Functor.mapIso_inv, Iso.prod, Iso.refl, denominatorLeftObject,
      MonoidalActionCategory.inclusion] using hMap

/-- The full denominator-left action is derived by Mathlib's monoidal-functor
construction from the explicitly proved scalar/unit/associator data. -/
@[instance_reducible]
def denominatorLeftAction :
    MonoidalLeftAction (Core C) (SInverse (Core C) (FixedTargetExtension C X)) := by
  letI : (denominatorLeftCurriedMop (C := C) (X := X)).Monoidal :=
    (denominatorLeftCoreMonoidal (C := C) (X := X)).toMonoidal
  exact MonoidalLeftAction.actionOfMonoidalFunctorToEndofunctorMop
    (denominatorLeftCurriedMop (C := C) (X := X))

attribute [local instance] denominatorLeftAction

/-- The derived action is literally the left-denominator object formula. -/
theorem denominatorLeftAction_obj (U : Core C)
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    U ⊙ₗ a = denominatorLeftObject U a := rfl

/-- The action on an original represented arrow is the actual translated raw arrow. -/
theorem denominatorLeftAction_map_mk (U : Core C)
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (r : RawHom a b) :
    CategoryTheory.MonoidalCategory.MonoidalLeftActionStruct.actionHomRight U
        (d := a) (d' := b) (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (denominatorLeftRaw U r) := by
  change (denominatorLeftFunctor U).map (X := a) (Y := b)
      (MonoidalActionCategory.Hom.mk r) =
    MonoidalActionCategory.Hom.mk (denominatorLeftRaw U r)
  exact denominatorLeftFunctor_map_mk U r

/-- Scalar action is the actual original pair inclusion, with no row change. -/
theorem denominatorLeftAction_scalar {U U' : Core C} (f : U ⟶ U')
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    f ⊵ₗ a = denominatorScalarComponent f a := rfl

/-- The derived action unit is the recorded ordinary pair-unitor component. -/
theorem denominatorLeftAction_unit_hom
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    (λₗ[Core C] a).hom = (denominatorUnitComponent a).hom := rfl

/-- The action associator has the actual forward alpha.hom denominator coordinate. -/
theorem denominatorLeftAction_assoc_hom (U V : Core C)
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    (αₗ U V a).hom = (denominatorAssocComponent U V a).hom := rfl

end AlgebraicKTheory.FixedTargetExtension.IteratedAction

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- The canonical iterated localization has both original denominator coordinates. -/
abbrev iteratedLocalizedRows (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] (X : C) :=
  SInverse (Core C) (SInverse (Core C) (FixedTargetExtension C X))

/-- On an ordinary original pair arrow q_X is the row inclusion. -/
theorem forgetDenominatorFunctor_map_inclusion
    {E F : FixedTargetExtension C X} {D D' : Core C} (g : E ⟶ F) (d : D ⟶ D') :
    forgetDenominatorFunctor.map
        ((MonoidalActionCategory.inclusion (Core C)
          (FixedTargetExtension C X × Core C)).map
          (X := (E, D)) (Y := (F, D')) (g, d)) =
      (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X)).map g := rfl

/-- q_X strictly ignores the fixed left-denominator translation. -/
theorem forgetDenominatorFunctor_map_translation (U : Core C)
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (f : a ⟶ b) :
    forgetDenominatorFunctor.map ((denominatorLeftFunctor U).map f) =
      forgetDenominatorFunctor.map f := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  rfl

/-- The scalar action has literal identity row image under q_X. -/
theorem forgetDenominatorFunctor_map_scalar {U U' : Core C} (e : U ⟶ U')
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    forgetDenominatorFunctor.map (denominatorScalarComponent e a) =
      𝟙 (forgetDenominatorObject a) := by
  change forgetDenominatorFunctor.map
      ((MonoidalActionCategory.inclusion (Core C)
        (FixedTargetExtension C X × Core C)).map
        (X := (a.of.1, U ⊗ a.of.2)) (Y := (a.of.1, U' ⊗ a.of.2))
        (𝟙 a.of.1, e ▷ a.of.2)) = 𝟙 (forgetDenominatorObject a)
  rw [forgetDenominatorFunctor_map_inclusion]
  exact CategoryTheory.Functor.map_id _ _

/-- The original action-unit row image is the identity, with no object replacement. -/
theorem forgetDenominatorFunctor_map_unit
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    forgetDenominatorFunctor.map (denominatorUnitComponent a).hom =
      𝟙 (forgetDenominatorObject a) := by
  change forgetDenominatorFunctor.map
      ((MonoidalActionCategory.inclusion (Core C)
        (FixedTargetExtension C X × Core C)).map
        (X := (a.of.1, (𝟙_ (Core C)) ⊗ a.of.2)) (Y := a.of)
        (𝟙 a.of.1, (λ_ a.of.2).hom)) = 𝟙 (forgetDenominatorObject a)
  rw [forgetDenominatorFunctor_map_inclusion]
  exact CategoryTheory.Functor.map_id _ _

/-- The actual action associator changes only the denominator under q_X. -/
theorem forgetDenominatorFunctor_map_assoc (U V : Core C)
    (a : SInverse (Core C) (FixedTargetExtension C X)) :
    forgetDenominatorFunctor.map (denominatorAssocComponent U V a).hom =
      𝟙 (forgetDenominatorObject a) := by
  change forgetDenominatorFunctor.map
      ((MonoidalActionCategory.inclusion (Core C)
        (FixedTargetExtension C X × Core C)).map
        (X := (a.of.1, (U ⊗ V) ⊗ a.of.2))
        (Y := (a.of.1, U ⊗ (V ⊗ a.of.2)))
        (𝟙 a.of.1, (α_ U V a.of.2).hom)) = 𝟙 (forgetDenominatorObject a)
  rw [forgetDenominatorFunctor_map_inclusion]
  exact CategoryTheory.Functor.map_id _ _

/-- pi_N sends ((E,D),A) to the exact original auxiliary object E. -/
def iteratedRowProjectionObject (a : iteratedLocalizedRows C X) :
    MonoidalActionCategory (Core C) (FixedTargetExtension C X) :=
  forgetDenominatorObject a.of.1

/-- On an outer raw arrow pi_N is q_X of its actual inner quotient arrow. -/
def iteratedRowProjectionRawMap {a b : iteratedLocalizedRows C X} (r : RawHom a b) :
    iteratedRowProjectionObject a ⟶ iteratedRowProjectionObject b :=
  (forgetDenominatorFunctor (C := C) (X := X)).map
    (X := (r.stabilizer ⊙ₗ a.of).1) (Y := b.of.1) r.hom.1

private theorem iteratedRowProjectionRawMap_rel
    {a b : iteratedLocalizedRows C X} {r s : RawHom a b} (h : r.Rel s) :
    iteratedRowProjectionRawMap r = iteratedRowProjectionRawMap s := by
  obtain ⟨e, he⟩ := h
  have hInner : e.hom ⊵ₗ a.of.1 ≫ s.hom.1 = r.hom.1 :=
    congrArg (fun k : r.stabilizer ⊙ₗ a.of ⟶ b.of => k.1) he
  change denominatorScalarComponent e.hom a.of.1 ≫ s.hom.1 = r.hom.1 at hInner
  let q := forgetDenominatorFunctor (C := C) (X := X)
  let A := iteratedRowProjectionObject a
  let B := iteratedRowProjectionObject b
  let qr : A ⟶ B := q.map
    (X := denominatorLeftObject r.stabilizer a.of.1) (Y := b.of.1) r.hom.1
  let qs : A ⟶ B := q.map
    (X := denominatorLeftObject s.stabilizer a.of.1) (Y := b.of.1) s.hom.1
  let qe : A ⟶ A := q.map
    (X := denominatorLeftObject r.stabilizer a.of.1)
    (Y := denominatorLeftObject s.stabilizer a.of.1)
    (denominatorScalarComponent e.hom a.of.1)
  have hMapped : qe ≫ qs = qr := by
    have hm := congrArg
      (fun k : denominatorLeftObject r.stabilizer a.of.1 ⟶ b.of.1 =>
        q.map (X := denominatorLeftObject r.stabilizer a.of.1) (Y := b.of.1) k) hInner
    exact (q.map_comp (denominatorScalarComponent e.hom a.of.1) s.hom.1).symm.trans hm
  have hScalar : qe = 𝟙 A := forgetDenominatorFunctor_map_scalar e.hom a.of.1
  change qr = qs
  rw [hScalar, Category.id_comp] at hMapped
  exact hMapped.symm

private theorem iteratedRowProjectionRawMap_id (a : iteratedLocalizedRows C X) :
    iteratedRowProjectionRawMap (RawHom.id a) = 𝟙 (iteratedRowProjectionObject a) := by
  change (forgetDenominatorFunctor (C := C) (X := X)).map
      (X := (𝟙_ (Core C)) ⊙ₗ a.of.1) (Y := a.of.1) (λₗ[Core C] a.of.1).hom =
    𝟙 (forgetDenominatorObject a.of.1)
  rw [denominatorLeftAction_unit_hom]
  exact forgetDenominatorFunctor_map_unit a.of.1

private theorem denominatorLeftAction_map_eq (U : Core C)
    {a b : SInverse (Core C) (FixedTargetExtension C X)} (f : a ⟶ b) :
    U ⊴ₗ f = (denominatorLeftFunctor U).map f := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  exact (denominatorLeftAction_map_mk U r).trans (denominatorLeftFunctor_map_mk U r).symm

private theorem iteratedRowProjectionRawMap_comp
    {a b c : iteratedLocalizedRows C X} (r : RawHom a b) (s : RawHom b c) :
    iteratedRowProjectionRawMap (r.comp s) =
      iteratedRowProjectionRawMap r ≫ iteratedRowProjectionRawMap s := by
  let q := forgetDenominatorFunctor (C := C) (X := X)
  let A := iteratedRowProjectionObject a
  let B := iteratedRowProjectionObject b
  let C' := iteratedRowProjectionObject c
  let qr : A ⟶ B := q.map
    (X := denominatorLeftObject r.stabilizer a.of.1) (Y := b.of.1) r.hom.1
  let qs : B ⟶ C' := q.map
    (X := denominatorLeftObject s.stabilizer b.of.1) (Y := c.of.1) s.hom.1
  let qa : A ⟶ A := q.map
    (X := denominatorLeftObject (s.stabilizer ⊗ r.stabilizer) a.of.1)
    (Y := denominatorLeftObject s.stabilizer (denominatorLeftObject r.stabilizer a.of.1))
    (denominatorAssocComponent s.stabilizer r.stabilizer a.of.1).hom
  let qt : A ⟶ B := q.map
    (X := denominatorLeftObject s.stabilizer (denominatorLeftObject r.stabilizer a.of.1))
    (Y := denominatorLeftObject s.stabilizer b.of.1)
    ((denominatorLeftFunctor s.stabilizer).map r.hom.1)
  have hAssoc : qa = 𝟙 A :=
    forgetDenominatorFunctor_map_assoc s.stabilizer r.stabilizer a.of.1
  have hTranslated : qt = qr :=
    forgetDenominatorFunctor_map_translation s.stabilizer r.hom.1
  have hFirst : q.map
      (X := denominatorLeftObject (s.stabilizer ⊗ r.stabilizer) a.of.1) (Y := c.of.1)
      ((denominatorAssocComponent s.stabilizer r.stabilizer a.of.1).hom ≫
        (denominatorLeftFunctor s.stabilizer).map r.hom.1 ≫ s.hom.1) =
      qa ≫ q.map
        (X := denominatorLeftObject s.stabilizer (denominatorLeftObject r.stabilizer a.of.1))
        (Y := c.of.1)
        ((denominatorLeftFunctor s.stabilizer).map r.hom.1 ≫ s.hom.1) :=
    q.map_comp _ _
  have hSecond : q.map
      (X := denominatorLeftObject s.stabilizer (denominatorLeftObject r.stabilizer a.of.1))
      (Y := c.of.1)
      ((denominatorLeftFunctor s.stabilizer).map r.hom.1 ≫ s.hom.1) = qt ≫ qs :=
    q.map_comp _ _
  have hMapped : iteratedRowProjectionRawMap (r.comp s) = qa ≫ qt ≫ qs := by
    change q.map
        (X := (s.stabilizer ⊗ r.stabilizer) ⊙ₗ a.of.1) (Y := c.of.1)
        ((αₗ s.stabilizer r.stabilizer a.of.1).hom ≫
          s.stabilizer ⊴ₗ r.hom.1 ≫ s.hom.1) = qa ≫ qt ≫ qs
    erw [denominatorLeftAction_assoc_hom, denominatorLeftAction_map_eq]
    exact hFirst.trans (congrArg (fun k : A ⟶ C' => qa ≫ k) hSecond)
  change iteratedRowProjectionRawMap (r.comp s) = qr ≫ qs
  exact hMapped.trans (by rw [hAssoc, hTranslated, Category.id_comp])

/-- The literal pi_N functor descends the actual outer Raw.Rel quotient. -/
def iteratedRowProjectionFunctor : iteratedLocalizedRows C X ⥤
    MonoidalActionCategory (Core C) (FixedTargetExtension C X) where
  obj := iteratedRowProjectionObject
  map f := _root_.Quotient.lift iteratedRowProjectionRawMap
    (by intro r s h; exact iteratedRowProjectionRawMap_rel h) f
  map_id a := by
    exact iteratedRowProjectionRawMap_id a
  map_comp f g := by
    refine _root_.Quotient.inductionOn₂ f g ?_
    intro r s
    exact iteratedRowProjectionRawMap_comp r s

/-- The actual outer quotient representative maps through its original inner arrow. -/
theorem iteratedRowProjectionFunctor_map_mk
    {a b : iteratedLocalizedRows C X} (r : RawHom a b) :
    iteratedRowProjectionFunctor.map (MonoidalActionCategory.Hom.mk r) =
      (forgetDenominatorFunctor (C := C) (X := X)).map
        (X := (r.stabilizer ⊙ₗ a.of).1) (Y := b.of.1) r.hom.1 :=
  rfl

end AlgebraicKTheory.FixedTargetExtension.IteratedAction

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- For the same two original row representatives the stabilizer alignment
is unique: their row arrows are monic and the stabilizer action is faithful. -/
theorem auxiliaryRaw_alignment_unique
    {a b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    {r s : RawHom a b} (e d : r.stabilizer ≅ s.stabilizer)
    (he : e.hom ⊵ₗ a.of ≫ s.hom = r.hom)
    (hd : d.hom ⊵ₗ a.of ≫ s.hom = r.hom) : e = d := by
  have h : e.hom ⊵ₗ a.of = d.hom ⊵ₗ a.of :=
    (cancel_mono s.hom).mp (he.trans hd.symm)
  change FixedTargetExtension.leftSumMap e.hom (𝟙 a.of) =
    FixedTargetExtension.leftSumMap d.hom (𝟙 a.of) at h
  exact Iso.ext (stabilizerAction_injective e.hom d.hom a.of h)

/-- Equality of actual auxiliary quotient arrows determines one stabilizer Iso. -/
theorem auxiliaryRaw_alignment_existsUnique
    {a b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r s : RawHom a b) (h : MonoidalActionCategory.Hom.mk r = MonoidalActionCategory.Hom.mk s) :
    ∃! e : r.stabilizer ≅ s.stabilizer, e.hom ⊵ₗ a.of ≫ s.hom = r.hom := by
  obtain ⟨e, he⟩ := (MonoidalActionCategory.Hom.mk_eq_mk_iff r s).mp h
  refine ⟨e, he, ?_⟩
  intro d hd
  exact auxiliaryRaw_alignment_unique (r := r) (s := s) d e hd he

/-- The lift's target retains the outer A and puts T on the original inner D. -/
def iteratedLiftObject (a : iteratedLocalizedRows C X)
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b) : iteratedLocalizedRows C X :=
  ⟨((⟨(b.of, r.stabilizer ⊗ a.of.1.of.2)⟩ :
      SInverse (Core C) (FixedTargetExtension C X)), a.of.2)⟩

/-- The represented inner lift uses exactly gamma and T acting on the zero-left unitor. -/
def iteratedLiftInnerRaw (a : iteratedLocalizedRows C X)
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b) :
    RawHom (denominatorLeftObject (𝟙_ (Core C)) a.of.1)
      (iteratedLiftObject a r).of.1 where
  stabilizer := r.stabilizer
  hom := (r.hom, r.stabilizer ◁ (λ_ a.of.1.of.2).hom)

/-- The actual outer unit lift is formed from its genuine inner quotient arrow. -/
def iteratedLiftRaw (a : iteratedLocalizedRows C X)
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b) :
    RawHom a (iteratedLiftObject a r) where
  stabilizer := 𝟙_ (Core C)
  hom := (MonoidalActionCategory.Hom.mk (iteratedLiftInnerRaw a r), (λ_ a.of.2).hom)

/-- The outer lift maps to the same original base representative, not a selected substitute. -/
theorem iteratedLiftRaw_projection (a : iteratedLocalizedRows C X)
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b) :
    iteratedRowProjectionFunctor.map (MonoidalActionCategory.Hom.mk (iteratedLiftRaw a r)) =
      MonoidalActionCategory.Hom.mk r := rfl

end AlgebraicKTheory.FixedTargetExtension.IteratedAction

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- The completed coefficient source of an arrow with original base stabilizer T. -/
def relativeCoefficientSource (T : Core C) (a : iteratedLocalizedRows C X) :
    SInverse (Core C) (Core C) := ⟨(a.of.2, T ⊗ a.of.1.of.2)⟩

/-- The completed coefficient target retains the exact outer/inner denominator coordinates. -/
def relativeCoefficientTarget (b : iteratedLocalizedRows C X) :
    SInverse (Core C) (Core C) := ⟨(b.of.2, b.of.1.of.2)⟩

/-- Normalize only the inner stabilizer, using its actual alignment with T.
The returned Core representative keeps the original outer U and epsilon. -/
def relativeCoefficientRaw (T U : Core C) {a b : iteratedLocalizedRows C X}
    (r : RawHom (denominatorLeftObject U a.of.1) b.of.1)
    (epsilon : U ⊗ a.of.2 ⟶ b.of.2) (e : r.stabilizer ≅ T) :
    RawHom (relativeCoefficientSource T a) (relativeCoefficientTarget b) where
  stabilizer := U
  hom := (epsilon,
    (denominatorInterchangeIso U T a.of.1.of.2).inv ≫
      e.inv ▷ (U ⊗ a.of.1.of.2) ≫ r.hom.2)

/-- Reconstruct the actual inner arrow over the given base representative.
The original row gamma is used, and the coefficient denominator is transported
through the forward interchange to its exact inner source. -/
def relativeReconstructInnerRaw {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (k : RawHom (relativeCoefficientSource r.stabilizer a) (relativeCoefficientTarget b)) :
    RawHom (denominatorLeftObject k.stabilizer a.of.1) b.of.1 where
  stabilizer := r.stabilizer
  hom := (r.hom,
    (denominatorInterchangeIso k.stabilizer r.stabilizer a.of.1.of.2).hom ≫ k.hom.2)

/-- The coefficient reconstructs a literal outer representative in the original N. -/
def relativeReconstructOuterRaw {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (k : RawHom (relativeCoefficientSource r.stabilizer a) (relativeCoefficientTarget b)) :
    RawHom a b where
  stabilizer := k.stabilizer
  hom := (MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r k), k.hom.1)

/-- Reconstruction lies over the exact original auxiliary representative. -/
theorem relativeReconstruct_projection {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (k : RawHom (relativeCoefficientSource r.stabilizer a) (relativeCoefficientTarget b)) :
    iteratedRowProjectionFunctor.map
        (MonoidalActionCategory.Hom.mk (relativeReconstructOuterRaw r k)) =
      MonoidalActionCategory.Hom.mk r := rfl

/-- Reconstruction recovers the original inner class using the actual
base stabilizer alignment and leaves the original outer epsilon unchanged. -/
theorem relativeReconstructInnerRaw_rel {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (U : Core C) (s : RawHom (denominatorLeftObject U a.of.1) b.of.1)
    (epsilon : U ⊗ a.of.2 ⟶ b.of.2) (e : s.stabilizer ≅ r.stabilizer)
    (he : e.hom ⊵ₗ a.of.1.of.1 ≫ r.hom = s.hom.1) :
    s.Rel (relativeReconstructInnerRaw r
      (relativeCoefficientRaw r.stabilizer U s epsilon e)) := by
  dsimp only [iteratedRowProjectionObject, forgetDenominatorObject,
    relativeCoefficientSource, relativeCoefficientTarget, denominatorLeftObject,
    iteratedLiftObject] at *
  let delta : s.stabilizer ⊗ (U ⊗ a.of.1.of.2) ⟶ b.of.1.of.2 := s.hom.2
  refine ⟨e, ?_⟩
  apply Prod.ext
  · exact he
  · change e.hom ▷ (U ⊗ a.of.1.of.2) ≫
        (denominatorInterchangeIso U r.stabilizer a.of.1.of.2).hom ≫
        (denominatorInterchangeIso U r.stabilizer a.of.1.of.2).inv ≫
        e.inv ▷ (U ⊗ a.of.1.of.2) ≫ delta = delta
    rw [Iso.hom_inv_id_assoc, MonoidalCategory.hom_inv_whiskerRight_assoc]

/-- At the already normalized base stabilizer the complete coefficient raw arrow is recovered. -/
theorem relativeCoefficientRaw_reconstruct {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (k : RawHom (relativeCoefficientSource r.stabilizer a) (relativeCoefficientTarget b)) :
    relativeCoefficientRaw r.stabilizer k.stabilizer
        (relativeReconstructInnerRaw r k) k.hom.1 (Iso.refl r.stabilizer) = k := by
  dsimp only [iteratedRowProjectionObject, forgetDenominatorObject,
    relativeCoefficientSource, relativeCoefficientTarget, denominatorLeftObject,
    iteratedLiftObject] at *
  cases k with
  | mk U h =>
    let delta : U ⊗ (r.stabilizer ⊗ a.of.1.of.2) ⟶ b.of.1.of.2 := h.2
    apply congrArg (fun p : U ⊙ₗ (relativeCoefficientSource r.stabilizer a).of ⟶
      (relativeCoefficientTarget b).of =>
        (⟨U, p⟩ : RawHom (relativeCoefficientSource r.stabilizer a)
          (relativeCoefficientTarget b)))
    apply Prod.ext
    · rfl
    · change (denominatorInterchangeIso U r.stabilizer a.of.1.of.2).inv ≫
          (Iso.refl r.stabilizer).inv ▷ (U ⊗ a.of.1.of.2) ≫
          (denominatorInterchangeIso U r.stabilizer a.of.1.of.2).hom ≫ delta = delta
      rw [Iso.refl_inv, MonoidalCategory.id_whiskerRight, Category.id_comp]
      exact Iso.inv_hom_id_assoc _ delta

end AlgebraicKTheory.FixedTargetExtension.IteratedAction

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [exactC : ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

omit exactC in
/-- Moving an actual outer scalar across the interchange preserves the inner T and D. -/
theorem denominatorInterchangeIso_natural_parameter
    {U U' : Core C}
    (f : U ⟶ U') (T D : Core C) :
    T ◁ (f ▷ D) ≫ (denominatorInterchangeIso U' T D).hom =
      (denominatorInterchangeIso U T D).hom ≫ f ▷ (T ⊗ D) := by
  apply Core.hom_ext
  have h := swap_parameter_hom f.iso.hom T.of D.of
  simpa only [coreCategory_comp_iso, Iso.trans_hom, core_left_hom,
    core_right_hom, denominatorInterchangeIso_hom, coreBiprodTensorObj_of] using h

/-- A coefficient stabilizer relation reconstructs the actual outer relation in N.
The first coordinate keeps epsilon; the second uses the same delta via interchange. -/
theorem relativeReconstructOuterRaw_rel {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    {k l : RawHom (relativeCoefficientSource r.stabilizer a) (relativeCoefficientTarget b)}
    (h : k.Rel l) :
    (relativeReconstructOuterRaw r k).Rel (relativeReconstructOuterRaw r l) := by
  dsimp only [iteratedRowProjectionObject, forgetDenominatorObject,
    relativeCoefficientSource, relativeCoefficientTarget, denominatorLeftObject,
    iteratedLiftObject] at *
  obtain ⟨e, he⟩ := h
  let gamma : leftSumObj r.stabilizer a.of.1.of.1 ⟶ b.of.1.of.1 := r.hom
  let deltaK : k.stabilizer ⊗ (r.stabilizer ⊗ a.of.1.of.2) ⟶ b.of.1.of.2 := k.hom.2
  let deltaL : l.stabilizer ⊗ (r.stabilizer ⊗ a.of.1.of.2) ⟶ b.of.1.of.2 := l.hom.2
  have hEpsilon : (e.hom ▷ a.of.2) ≫ l.hom.1 = k.hom.1 :=
    congrArg
      (fun f : k.stabilizer ⊙ₗ (relativeCoefficientSource r.stabilizer a).of ⟶
        (relativeCoefficientTarget b).of => f.1) he
  have hDelta : (e.hom ▷ (r.stabilizer ⊗ a.of.1.of.2)) ≫ l.hom.2 = k.hom.2 :=
    congrArg
      (fun f : k.stabilizer ⊙ₗ (relativeCoefficientSource r.stabilizer a).of ⟶
        (relativeCoefficientTarget b).of => f.2) he
  change (e.hom ▷ (r.stabilizer ⊗ a.of.1.of.2)) ≫ deltaL = deltaK at hDelta
  let phi : (denominatorLeftObject k.stabilizer a.of.1).of ⟶
      (denominatorLeftObject l.stabilizer a.of.1).of :=
    (𝟙 a.of.1.of.1, e.hom ▷ a.of.1.of.2)
  let s := relativeReconstructInnerRaw r l
  have hPre : (⟨r.stabilizer, r.stabilizer ⊴ₗ phi ≫ s.hom⟩ :
      RawHom (denominatorLeftObject k.stabilizer a.of.1) b.of.1) =
      relativeReconstructInnerRaw r k := by
    apply congrArg
      (fun f : r.stabilizer ⊙ₗ (denominatorLeftObject k.stabilizer a.of.1).of ⟶
        b.of.1.of =>
          (⟨r.stabilizer, f⟩ :
            RawHom (denominatorLeftObject k.stabilizer a.of.1) b.of.1))
    apply Prod.ext
    · change leftSumMap (𝟙 r.stabilizer) (𝟙 a.of.1.of.1) ≫ gamma = gamma
      rw [leftSumMap_id, Category.id_comp]
    · change r.stabilizer ◁ (e.hom ▷ a.of.1.of.2) ≫
          ((denominatorInterchangeIso l.stabilizer r.stabilizer a.of.1.of.2).hom ≫
            deltaL) =
        (denominatorInterchangeIso k.stabilizer r.stabilizer a.of.1.of.2).hom ≫ deltaK
      rw [← Category.assoc, denominatorInterchangeIso_natural_parameter,
        Category.assoc, hDelta]
  have hInner : denominatorScalarComponent e.hom a.of.1 ≫ MonoidalActionCategory.Hom.mk s =
      MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r k) := by
    change MonoidalActionCategory.Hom.mk ((RawHom.ofMap (S := Core C) phi).comp s) =
      MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r k)
    exact (_root_.Quotient.sound (rawPreMap_rel phi s)).trans
      (congrArg MonoidalActionCategory.Hom.mk hPre)
  refine ⟨e, ?_⟩
  apply Prod.ext
  · change e.hom ⊵ₗ a.of.1 ≫ MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r l) =
      MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r k)
    rw [denominatorLeftAction_scalar]
    exact hInner
  · exact hEpsilon

/-- The actual coefficient quotient maps to N; no representatives are supplied externally. -/
def relativeReconstructHom {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (f : relativeCoefficientSource r.stabilizer a ⟶ relativeCoefficientTarget b) : a ⟶ b :=
  _root_.Quotient.map (relativeReconstructOuterRaw r)
    (by intro k l h; exact relativeReconstructOuterRaw_rel r h) f

/-- Each original coefficient representative retains its literal reconstructed class. -/
theorem relativeReconstructHom_mk {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (k : RawHom (relativeCoefficientSource r.stabilizer a) (relativeCoefficientTarget b)) :
    relativeReconstructHom r (MonoidalActionCategory.Hom.mk k) =
      MonoidalActionCategory.Hom.mk (relativeReconstructOuterRaw r k) := rfl

/-- Every coefficient quotient reconstructs over the given original auxiliary arrow. -/
theorem relativeReconstructHom_projection {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (f : relativeCoefficientSource r.stabilizer a ⟶ relativeCoefficientTarget b) :
    iteratedRowProjectionFunctor.map (relativeReconstructHom r f) =
      MonoidalActionCategory.Hom.mk r := by
  refine _root_.Quotient.inductionOn f ?_
  intro k
  exact relativeReconstruct_projection r k

/-- An aligned inner representative reconstructs its original outer class.
This is a derived relation with the identity outer Iso, not a fiber-equivalence premise. -/
theorem relativeReconstructOuterRaw_normalizes {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (U : Core C) (s : RawHom (denominatorLeftObject U a.of.1) b.of.1)
    (epsilon : U ⊗ a.of.2 ⟶ b.of.2) (e : s.stabilizer ≅ r.stabilizer)
    (he : e.hom ⊵ₗ a.of.1.of.1 ≫ r.hom = s.hom.1) :
    (relativeReconstructOuterRaw r
      (relativeCoefficientRaw r.stabilizer U s epsilon e)).Rel
      (⟨U, (MonoidalActionCategory.Hom.mk s, epsilon)⟩ : RawHom a b) := by
  dsimp only [iteratedRowProjectionObject, forgetDenominatorObject,
    relativeCoefficientSource, relativeCoefficientTarget, denominatorLeftObject,
    iteratedLiftObject] at *
  refine ⟨Iso.refl U, ?_⟩
  erw [Iso.refl_hom, MonoidalLeftAction.id_actionHomLeft, Category.id_comp]
  apply Prod.ext
  · exact _root_.Quotient.sound (relativeReconstructInnerRaw_rel r U s epsilon e he)
  · rfl

/-- An outer relation between reconstructed representatives reflects the original K relation.
Its inner stabilizer automorphism is the identity, by monicity of the original row map. -/
theorem relativeReconstructOuterRaw_rel_reflect {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    {k l : RawHom (relativeCoefficientSource r.stabilizer a) (relativeCoefficientTarget b)}
    (h : (relativeReconstructOuterRaw r k).Rel (relativeReconstructOuterRaw r l)) :
    k.Rel l := by
  dsimp only [iteratedRowProjectionObject, forgetDenominatorObject,
    relativeCoefficientSource, relativeCoefficientTarget, denominatorLeftObject,
    iteratedLiftObject] at *
  obtain ⟨e, he⟩ := h
  dsimp only [relativeReconstructOuterRaw] at e he
  let gamma : leftSumObj r.stabilizer a.of.1.of.1 ⟶ b.of.1.of.1 := r.hom
  let deltaK : k.stabilizer ⊗ (r.stabilizer ⊗ a.of.1.of.2) ⟶ b.of.1.of.2 := k.hom.2
  let deltaL : l.stabilizer ⊗ (r.stabilizer ⊗ a.of.1.of.2) ⟶ b.of.1.of.2 := l.hom.2
  have hInner : denominatorScalarComponent e.hom a.of.1 ≫
      MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r l) =
      MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r k) := by
    have hi := congrArg (fun f : k.stabilizer ⊙ₗ a.of ⟶ b.of => f.1) he
    change e.hom ⊵ₗ a.of.1 ≫ MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r l) =
      MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r k) at hi
    rw [denominatorLeftAction_scalar] at hi
    exact hi
  have hEpsilon : (e.hom ▷ a.of.2) ≫ l.hom.1 = k.hom.1 :=
    congrArg (fun f : k.stabilizer ⊙ₗ a.of ⟶ b.of => f.2) he
  let phi : (denominatorLeftObject k.stabilizer a.of.1).of ⟶
      (denominatorLeftObject l.stabilizer a.of.1).of :=
    (𝟙 a.of.1.of.1, e.hom ▷ a.of.1.of.2)
  let s := relativeReconstructInnerRaw r l
  let p : RawHom (denominatorLeftObject k.stabilizer a.of.1) b.of.1 :=
    ⟨r.stabilizer, r.stabilizer ⊴ₗ phi ≫ s.hom⟩
  have hPre : denominatorScalarComponent e.hom a.of.1 ≫ MonoidalActionCategory.Hom.mk s =
      MonoidalActionCategory.Hom.mk p := by
    change MonoidalActionCategory.Hom.mk ((RawHom.ofMap (S := Core C) phi).comp s) =
      MonoidalActionCategory.Hom.mk p
    exact _root_.Quotient.sound (rawPreMap_rel phi s)
  have hClass : MonoidalActionCategory.Hom.mk p =
      MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r k) :=
    hPre.symm.trans hInner
  obtain ⟨d, hd⟩ :=
    (MonoidalActionCategory.Hom.mk_eq_mk_iff p (relativeReconstructInnerRaw r k)).mp hClass
  dsimp only [relativeReconstructInnerRaw] at d hd
  have hRow : d.hom ⊵ₗ a.of.1.of.1 ≫ r.hom = r.hom := by
    have hr := congrArg
      (fun f : r.stabilizer ⊙ₗ (denominatorLeftObject k.stabilizer a.of.1).of ⟶
        b.of.1.of => f.1) hd
    change leftSumMap d.hom (𝟙 a.of.1.of.1) ≫ gamma =
      leftSumMap (𝟙 r.stabilizer) (𝟙 a.of.1.of.1) ≫ gamma at hr
    rw [leftSumMap_id, Category.id_comp] at hr
    exact hr
  have hId : d = Iso.refl r.stabilizer :=
    auxiliaryRaw_alignment_unique (r := r) (s := r) d (Iso.refl r.stabilizer) hRow (by
      rw [Iso.refl_hom, MonoidalLeftAction.id_actionHomLeft, Category.id_comp])
  have hDen := congrArg
    (fun f : r.stabilizer ⊙ₗ (denominatorLeftObject k.stabilizer a.of.1).of ⟶
      b.of.1.of => f.2) hd
  change d.hom ▷ (k.stabilizer ⊗ a.of.1.of.2) ≫
      ((denominatorInterchangeIso k.stabilizer r.stabilizer a.of.1.of.2).hom ≫
        deltaK) =
    r.stabilizer ◁ (e.hom ▷ a.of.1.of.2) ≫
      ((denominatorInterchangeIso l.stabilizer r.stabilizer a.of.1.of.2).hom ≫
        deltaL) at hDen
  rw [hId, Iso.refl_hom, id_whiskerRight, Category.id_comp,
    ← Category.assoc, denominatorInterchangeIso_natural_parameter,
    Category.assoc] at hDen
  have hDelta : (e.hom ▷ (r.stabilizer ⊗ a.of.1.of.2)) ≫ l.hom.2 = k.hom.2 :=
    (cancel_epi
      (denominatorInterchangeIso k.stabilizer r.stabilizer a.of.1.of.2).hom).mp hDen.symm
  refine ⟨e, ?_⟩
  apply Prod.ext
  · exact hEpsilon
  · exact hDelta

/-- Coefficient reconstruction is injective on the genuine quotient morphisms. -/
theorem relativeReconstructHom_injective {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b)) :
    Function.Injective (relativeReconstructHom r) := by
  intro f g
  refine _root_.Quotient.inductionOn₂ f g ?_
  intro k l h
  change MonoidalActionCategory.Hom.mk (relativeReconstructOuterRaw r k) =
    MonoidalActionCategory.Hom.mk (relativeReconstructOuterRaw r l) at h
  exact _root_.Quotient.sound
    (relativeReconstructOuterRaw_rel_reflect r
      ((MonoidalActionCategory.Hom.mk_eq_mk_iff (relativeReconstructOuterRaw r k)
        (relativeReconstructOuterRaw r l)).mp h))

/-- The relative arrow type is defined using the actual pi_N equality. -/
abbrev relativeArrow {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b)) :=
  {f : a ⟶ b // iteratedRowProjectionFunctor.map f = MonoidalActionCategory.Hom.mk r}

/-- Reconstruction gives an actual relative arrow over the given original base representative. -/
def relativeReconstructArrow {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (f : relativeCoefficientSource r.stabilizer a ⟶ relativeCoefficientTarget b) :
    relativeArrow r :=
  ⟨relativeReconstructHom r f, by exact relativeReconstructHom_projection r f⟩

/-- Every arrow over r has a coefficient, derived from its own two quotient representatives.
The unique base alignment preserves the incoming stabilizers and the whole delta. -/
theorem relativeReconstructArrow_surjective {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b)) :
    Function.Surjective (relativeReconstructArrow r) := by
  dsimp only [iteratedRowProjectionObject, forgetDenominatorObject,
    relativeCoefficientSource, relativeCoefficientTarget, denominatorLeftObject,
    iteratedLiftObject] at *
  intro f
  rcases f with ⟨f, hf⟩
  obtain ⟨eta, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  cases eta with
  | mk U h =>
    rcases h with ⟨sigma, epsilon⟩
    obtain ⟨s, rfl⟩ := MonoidalActionCategory.Hom.exists_rep sigma
    let rs : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b) :=
      ⟨s.stabilizer, s.hom.1⟩
    have hBase : MonoidalActionCategory.Hom.mk rs = MonoidalActionCategory.Hom.mk r := by
      change (MonoidalActionCategory.Hom.mk rs :
          iteratedRowProjectionObject a ⟶ iteratedRowProjectionObject b) =
        MonoidalActionCategory.Hom.mk r at hf
      exact hf
    obtain ⟨e, he, _⟩ := auxiliaryRaw_alignment_existsUnique rs r hBase
    let k := relativeCoefficientRaw r.stabilizer U s epsilon e
    refine ⟨MonoidalActionCategory.Hom.mk k, ?_⟩
    apply Subtype.ext
    change MonoidalActionCategory.Hom.mk (relativeReconstructOuterRaw r k) =
      MonoidalActionCategory.Hom.mk (⟨U, (MonoidalActionCategory.Hom.mk s, epsilon)⟩ : RawHom a b)
    exact _root_.Quotient.sound (relativeReconstructOuterRaw_normalizes r U s epsilon e he)

/-- The genuine relative-Hom equivalence is derived from both original raw quotients.
Its forward map is reconstruction; no fiber-equivalence or lifting result is a premise. -/
def relativeHomEquiv {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b)) :
    (relativeCoefficientSource r.stabilizer a ⟶ relativeCoefficientTarget b) ≃
      relativeArrow r :=
  Equiv.ofBijective (relativeReconstructArrow r) ⟨by
    intro f g h
    exact relativeReconstructHom_injective r (congrArg Subtype.val h),
    relativeReconstructArrow_surjective r⟩

end AlgebraicKTheory.FixedTargetExtension.IteratedAction

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- The original localized lift adds T to D, retaining the actual target row. -/
def localizedBaseLiftObject (a : SInverse (Core C) (FixedTargetExtension C X))
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (forgetDenominatorObject a) b) :
    SInverse (Core C) (FixedTargetExtension C X) := ⟨(b.of, r.stabilizer ⊗ a.of.2)⟩

/-- Its whole denominator arrow is the identity at the actual T tensor D. -/
def localizedBaseLiftRaw (a : SInverse (Core C) (FixedTargetExtension C X))
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (forgetDenominatorObject a) b) : RawHom a (localizedBaseLiftObject a r) where
  stabilizer := r.stabilizer
  hom := (r.hom, 𝟙 (r.stabilizer ⊗ a.of.2))

/-- The original localized lift uses its own unchanged raw stabilizer and row map. -/
def localizedBaseLiftHom (a : SInverse (Core C) (FixedTargetExtension C X))
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (forgetDenominatorObject a) b) : a ⟶ localizedBaseLiftObject a r :=
  MonoidalActionCategory.Hom.mk (localizedBaseLiftRaw a r)

/-- The literal N lift, with the original outer unit and epsilon lambda_A. -/
def iteratedLiftHom (a : iteratedLocalizedRows C X)
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b) : a ⟶ iteratedLiftObject a r :=
  MonoidalActionCategory.Hom.mk (iteratedLiftRaw a r)

/-- The original N lift is the ordinary pair inclusion of the localized lift and Id_A.
The negative action unitor is accounted for by the actual inner precomposition relation. -/
theorem iteratedLiftHom_asOrdinary (a : iteratedLocalizedRows C X)
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b) :
    (MonoidalActionCategory.inclusion (Core C)
      (SInverse (Core C) (FixedTargetExtension C X) × Core C)).map
      (X := a.of) (Y := (iteratedLiftObject a r).of)
      (localizedBaseLiftHom a.of.1 r, 𝟙 a.of.2) = iteratedLiftHom a r := by
  dsimp only [iteratedRowProjectionObject, forgetDenominatorObject,
    relativeCoefficientSource, relativeCoefficientTarget, denominatorLeftObject,
    iteratedLiftObject] at *
  let gamma : leftSumObj r.stabilizer a.of.1.of.1 ⟶ b.of := r.hom
  let phi : (denominatorLeftObject (𝟙_ (Core C)) a.of.1).of ⟶ a.of.1.of :=
    (𝟙 a.of.1.of.1, (λ_ a.of.1.of.2).hom)
  let q := localizedBaseLiftRaw a.of.1 r
  have hRaw : (⟨r.stabilizer, r.stabilizer ⊴ₗ phi ≫ q.hom⟩ :
      RawHom (denominatorLeftObject (𝟙_ (Core C)) a.of.1)
        (iteratedLiftObject a r).of.1) = iteratedLiftInnerRaw a r := by
    apply congrArg
      (fun h : r.stabilizer ⊙ₗ (denominatorLeftObject (𝟙_ (Core C)) a.of.1).of ⟶
        (iteratedLiftObject a r).of.1.of =>
          (⟨r.stabilizer, h⟩ :
            RawHom (denominatorLeftObject (𝟙_ (Core C)) a.of.1)
              (iteratedLiftObject a r).of.1))
    apply Prod.ext
    · change leftSumMap (𝟙 r.stabilizer) (𝟙 a.of.1.of.1) ≫ gamma = gamma
      rw [leftSumMap_id, Category.id_comp]
    · change r.stabilizer ◁ (λ_ a.of.1.of.2).hom ≫
          𝟙 (r.stabilizer ⊗ a.of.1.of.2) = r.stabilizer ◁ (λ_ a.of.1.of.2).hom
      exact Category.comp_id _
  have hInner : (denominatorUnitComponent a.of.1).hom ≫
      localizedBaseLiftHom a.of.1 r = MonoidalActionCategory.Hom.mk (iteratedLiftInnerRaw a r) := by
    change MonoidalActionCategory.Hom.mk ((RawHom.ofMap (S := Core C) phi).comp q) =
      MonoidalActionCategory.Hom.mk (iteratedLiftInnerRaw a r)
    exact (_root_.Quotient.sound (rawPreMap_rel phi q)).trans
      (congrArg MonoidalActionCategory.Hom.mk hRaw)
  change MonoidalActionCategory.Hom.mk (⟨𝟙_ (Core C),
      ((λₗ[Core C] a.of.1).hom ≫ localizedBaseLiftHom a.of.1 r,
        (λ_ a.of.2).hom ≫ 𝟙 a.of.2)⟩ : RawHom a (iteratedLiftObject a r)) =
    MonoidalActionCategory.Hom.mk (iteratedLiftRaw a r)
  erw [denominatorLeftAction_unit_hom, hInner, Category.comp_id]; rfl

/-- The original localized base lifts compose through the actual denominator associator. -/
theorem localizedBaseLiftHom_composition
    (a : SInverse (Core C) (FixedTargetExtension C X))
    {b c : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (forgetDenominatorObject a) b) (s : RawHom b c) :
    localizedBaseLiftHom a r ≫ localizedBaseLiftHom (localizedBaseLiftObject a r) s =
      localizedBaseLiftHom a (r.comp s) ≫
        (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map
          (X := (c.of, (s.stabilizer ⊗ r.stabilizer) ⊗ a.of.2))
          (Y := (c.of, s.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)))
          (𝟙 c.of, (α_ s.stabilizer r.stabilizer a.of.2).hom) := by
  let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
  let phi : (c.of, (s.stabilizer ⊗ r.stabilizer) ⊗ a.of.2) ⟶
      (c.of, s.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)) :=
    (𝟙 c.of, (α_ s.stabilizer r.stabilizer a.of.2).hom)
  let rr := localizedBaseLiftRaw a r
  let ss := localizedBaseLiftRaw (localizedBaseLiftObject a r) s
  let q := localizedBaseLiftRaw a (r.comp s)
  let k : RawHom a (localizedBaseLiftObject (localizedBaseLiftObject a r) s) :=
    ⟨s.stabilizer ⊗ r.stabilizer,
      ((r.comp s).hom, (α_ s.stabilizer r.stabilizer a.of.2).hom)⟩
  have hComp : rr.comp ss = k := by
    apply congrArg
      (fun h : (s.stabilizer ⊗ r.stabilizer) ⊙ₗ a.of ⟶
        (localizedBaseLiftObject (localizedBaseLiftObject a r) s).of =>
          (⟨s.stabilizer ⊗ r.stabilizer, h⟩ :
            RawHom a (localizedBaseLiftObject (localizedBaseLiftObject a r) s)))
    apply Prod.ext
    · rfl
    · change (α_ s.stabilizer r.stabilizer a.of.2).hom ≫
          s.stabilizer ◁ 𝟙 (r.stabilizer ⊗ a.of.2) ≫
          𝟙 (s.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)) =
        (α_ s.stabilizer r.stabilizer a.of.2).hom
      rw [whiskerLeft_id, Category.id_comp, Category.comp_id]
  have hPost : (⟨s.stabilizer ⊗ r.stabilizer, q.hom ≫ phi⟩ :
      RawHom a (localizedBaseLiftObject (localizedBaseLiftObject a r) s)) = k := by
    apply congrArg
      (fun h : (s.stabilizer ⊗ r.stabilizer) ⊙ₗ a.of ⟶
        (localizedBaseLiftObject (localizedBaseLiftObject a r) s).of =>
          (⟨s.stabilizer ⊗ r.stabilizer, h⟩ :
            RawHom a (localizedBaseLiftObject (localizedBaseLiftObject a r) s)))
    apply Prod.ext
    · change (r.comp s).hom ≫ 𝟙 c.of = (r.comp s).hom
      exact Category.comp_id _
    · change 𝟙 ((s.stabilizer ⊗ r.stabilizer) ⊗ a.of.2) ≫
          (α_ s.stabilizer r.stabilizer a.of.2).hom =
        (α_ s.stabilizer r.stabilizer a.of.2).hom
      exact Category.id_comp _
  have hLeft : localizedBaseLiftHom a r ≫
      localizedBaseLiftHom (localizedBaseLiftObject a r) s = MonoidalActionCategory.Hom.mk k :=
    (MonoidalActionCategory.Hom.mk_comp rr ss).trans (congrArg MonoidalActionCategory.Hom.mk hComp)
  have hRight : localizedBaseLiftHom a (r.comp s) ≫ I.map phi = MonoidalActionCategory.Hom.mk k :=
    (_root_.Quotient.sound (rawPostMap_rel q phi)).trans
      (congrArg MonoidalActionCategory.Hom.mk hPost)
  exact hLeft.trans hRight.symm

/-- The reconstructed inner arrow is negative translation of the base lift,
followed by the actual ordinary denominator delta map. -/
theorem relativeReconstructInnerHom_asNegativeLift {a b : iteratedLocalizedRows C X}
    (r : RawHom (iteratedRowProjectionObject a) (iteratedRowProjectionObject b))
    (k : RawHom (relativeCoefficientSource r.stabilizer a) (relativeCoefficientTarget b)) :
    MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r k) =
      (denominatorLeftFunctor k.stabilizer).map (localizedBaseLiftHom a.of.1 r) ≫
        (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map
          (X := (b.of.1.of.1, k.stabilizer ⊗ (r.stabilizer ⊗ a.of.1.of.2)))
          (Y := b.of.1.of) (𝟙 b.of.1.of.1, k.hom.2) := by
  let phi : (b.of.1.of.1, k.stabilizer ⊗ (r.stabilizer ⊗ a.of.1.of.2)) ⟶
      b.of.1.of := (𝟙 b.of.1.of.1, k.hom.2)
  let q := denominatorLeftRaw k.stabilizer (localizedBaseLiftRaw a.of.1 r)
  have hRaw : (⟨r.stabilizer, q.hom ≫ phi⟩ :
      RawHom (denominatorLeftObject k.stabilizer a.of.1) b.of.1) =
      relativeReconstructInnerRaw r k := by
    apply congrArg
      (fun h : r.stabilizer ⊙ₗ (denominatorLeftObject k.stabilizer a.of.1).of ⟶
        b.of.1.of =>
          (⟨r.stabilizer, h⟩ :
            RawHom (denominatorLeftObject k.stabilizer a.of.1) b.of.1))
    apply Prod.ext
    · change r.hom ≫ 𝟙 b.of.1.of.1 = r.hom
      exact Category.comp_id _
    · change ((denominatorInterchangeIso k.stabilizer r.stabilizer a.of.1.of.2).hom ≫
          k.stabilizer ◁ 𝟙 (r.stabilizer ⊗ a.of.1.of.2)) ≫ k.hom.2 =
        (denominatorInterchangeIso k.stabilizer r.stabilizer a.of.1.of.2).hom ≫ k.hom.2
      rw [whiskerLeft_id, Category.comp_id]
  change MonoidalActionCategory.Hom.mk (relativeReconstructInnerRaw r k) =
    (denominatorLeftFunctor k.stabilizer).map
        (MonoidalActionCategory.Hom.mk (localizedBaseLiftRaw a.of.1 r)) ≫
      (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map phi
  rw [denominatorLeftFunctor_map_mk]
  exact ((_root_.Quotient.sound (rawPostMap_rel q phi)).trans
    (congrArg MonoidalActionCategory.Hom.mk hRaw)).symm

/-- The coefficient source Iso is the actual associator at negative R,T,D.
It fixes positive A, with no scalar or coordinate reversal. -/
def relativeSourceAssocIso {a c : iteratedLocalizedRows C X}
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b)
    (s : RawHom b (iteratedRowProjectionObject c)) :
    relativeCoefficientSource (r.comp s).stabilizer a ≅
      relativeCoefficientSource s.stabilizer (iteratedLiftObject a r) :=
  (MonoidalActionCategory.inclusion (Core C) (Core C × Core C)).mapIso
    ((Iso.refl a.of.2).prod (α_ s.stabilizer r.stabilizer a.of.1.of.2))

/-- Actual coefficient precomposition keeps outer U/epsilon and acts only on alpha_R,T,D. -/
def relativeSourceAssocPreRaw {a c : iteratedLocalizedRows C X}
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b)
    (s : RawHom b (iteratedRowProjectionObject c))
    (k : RawHom (relativeCoefficientSource s.stabilizer (iteratedLiftObject a r))
      (relativeCoefficientTarget c)) :
    RawHom (relativeCoefficientSource (r.comp s).stabilizer a)
      (relativeCoefficientTarget c) where
  stabilizer := k.stabilizer
  hom := (k.hom.1, k.stabilizer ◁ (α_ s.stabilizer r.stabilizer a.of.1.of.2).hom ≫ k.hom.2)

/-- The coefficient source Iso acts by exactly the recorded precomposition representative. -/
theorem relativeSourceAssocIso_precompose_mk {a c : iteratedLocalizedRows C X}
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b)
    (s : RawHom b (iteratedRowProjectionObject c))
    (k : RawHom (relativeCoefficientSource s.stabilizer (iteratedLiftObject a r))
      (relativeCoefficientTarget c)) :
    (relativeSourceAssocIso r s).hom ≫ MonoidalActionCategory.Hom.mk k =
      MonoidalActionCategory.Hom.mk (relativeSourceAssocPreRaw r s k) := by
  dsimp only [iteratedRowProjectionObject, forgetDenominatorObject,
    relativeCoefficientSource, relativeCoefficientTarget, denominatorLeftObject,
    iteratedLiftObject] at *
  let epsilon : k.stabilizer ⊗ a.of.2 ⟶ c.of.2 := k.hom.1
  let phi : (relativeCoefficientSource (r.comp s).stabilizer a).of ⟶
      (relativeCoefficientSource s.stabilizer (iteratedLiftObject a r)).of :=
    (𝟙 a.of.2, (α_ s.stabilizer r.stabilizer a.of.1.of.2).hom)
  have hRaw : (⟨k.stabilizer, k.stabilizer ⊴ₗ phi ≫ k.hom⟩ :
      RawHom (relativeCoefficientSource (r.comp s).stabilizer a)
        (relativeCoefficientTarget c)) = relativeSourceAssocPreRaw r s k := by
    apply congrArg
      (fun h : k.stabilizer ⊙ₗ (relativeCoefficientSource (r.comp s).stabilizer a).of ⟶
        (relativeCoefficientTarget c).of =>
          (⟨k.stabilizer, h⟩ :
            RawHom (relativeCoefficientSource (r.comp s).stabilizer a)
              (relativeCoefficientTarget c)))
    apply Prod.ext
    · change (k.stabilizer ◁ 𝟙 a.of.2) ≫ epsilon = epsilon
      rw [whiskerLeft_id, Category.id_comp]
    · rfl
  change MonoidalActionCategory.Hom.mk ((RawHom.ofMap (S := Core C) phi).comp k) =
    MonoidalActionCategory.Hom.mk (relativeSourceAssocPreRaw r s k)
  exact (_root_.Quotient.sound (rawPreMap_rel phi k)).trans
    (congrArg MonoidalActionCategory.Hom.mk hRaw)


/-- The actual translated base lift followed by an inner reconstruction
is the reconstruction over the literal composite base arrow and source associator. -/
theorem relativeReconstructInnerHom_afterBaseLift {a c : iteratedLocalizedRows C X}
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b)
    (s : RawHom b (iteratedRowProjectionObject c))
    (k : RawHom (relativeCoefficientSource s.stabilizer (iteratedLiftObject a r))
      (relativeCoefficientTarget c)) :
    (denominatorLeftFunctor k.stabilizer).map (localizedBaseLiftHom a.of.1 r) ≫
        MonoidalActionCategory.Hom.mk
          (relativeReconstructInnerRaw (a := iteratedLiftObject a r) (b := c) s k) =
      MonoidalActionCategory.Hom.mk
        (relativeReconstructInnerRaw (r.comp s) (relativeSourceAssocPreRaw r s k)) := by
  let rBase : RawHom (forgetDenominatorObject a.of.1) b := r
  let sBase : RawHom
      (forgetDenominatorObject (localizedBaseLiftObject a.of.1 rBase))
      (forgetDenominatorObject c.of.1) := s
  let rsBase : RawHom (forgetDenominatorObject a.of.1)
      (forgetDenominatorObject c.of.1) := r.comp s
  let F := denominatorLeftFunctor (C := C) (X := X) k.stabilizer
  let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
  let f : a.of.1 ⟶ localizedBaseLiftObject a.of.1 rBase := localizedBaseLiftHom a.of.1 rBase
  let g : localizedBaseLiftObject a.of.1 rBase ⟶
      localizedBaseLiftObject (localizedBaseLiftObject a.of.1 rBase) sBase :=
    localizedBaseLiftHom (localizedBaseLiftObject a.of.1 rBase) sBase
  let t : a.of.1 ⟶ localizedBaseLiftObject a.of.1 rsBase :=
    localizedBaseLiftHom a.of.1 rsBase
  let A := F.obj a.of.1
  let B := F.obj (localizedBaseLiftObject a.of.1 rBase)
  let alpha : (localizedBaseLiftObject a.of.1 rsBase).of ⟶
      (localizedBaseLiftObject (localizedBaseLiftObject a.of.1 rBase) sBase).of :=
    (𝟙 c.of.1.of.1, (α_ s.stabilizer r.stabilizer a.of.1.of.2).hom)
  let alphaU : (c.of.1.of.1, k.stabilizer ⊗
        ((s.stabilizer ⊗ r.stabilizer) ⊗ a.of.1.of.2)) ⟶
      (c.of.1.of.1, k.stabilizer ⊗
        (s.stabilizer ⊗ (r.stabilizer ⊗ a.of.1.of.2))) :=
    (𝟙 c.of.1.of.1, k.stabilizer ◁ (α_ s.stabilizer r.stabilizer a.of.1.of.2).hom)
  let delta : (c.of.1.of.1, k.stabilizer ⊗
        (s.stabilizer ⊗ (r.stabilizer ⊗ a.of.1.of.2))) ⟶ c.of.1.of :=
    (𝟙 c.of.1.of.1, k.hom.2)
  let delta' : (c.of.1.of.1, k.stabilizer ⊗
        ((s.stabilizer ⊗ r.stabilizer) ⊗ a.of.1.of.2)) ⟶ c.of.1.of :=
    (𝟙 c.of.1.of.1,
      k.stabilizer ◁ (α_ s.stabilizer r.stabilizer a.of.1.of.2).hom ≫ k.hom.2)
  have hLeft : (MonoidalActionCategory.Hom.mk
      (relativeReconstructInnerRaw (a := iteratedLiftObject a r) (b := c) s k) : B ⟶ c.of.1) =
      (F.map g ≫ I.map delta : B ⟶ c.of.1) :=
    relativeReconstructInnerHom_asNegativeLift (a := iteratedLiftObject a r) (b := c) s k
  have hBase : f ≫ g = t ≫ I.map alpha := localizedBaseLiftHom_composition a.of.1 rBase sBase
  have hTranslate : F.map (I.map alpha) = I.map alphaU :=
    denominatorLeftFunctor_map_inclusion k.stabilizer (𝟙 c.of.1.of.1)
      (α_ s.stabilizer r.stabilizer a.of.1.of.2).hom
  have hPair : alphaU ≫ delta = delta' := by
    apply Prod.ext
    · exact Category.id_comp _
    · rfl
  have hDelta : F.map (I.map alpha) ≫ I.map delta = I.map delta' :=
    (congrArg (fun q => q ≫ I.map delta) hTranslate).trans
      ((I.map_comp alphaU delta).symm.trans (congrArg I.map hPair))
  have hRight : (MonoidalActionCategory.Hom.mk
      (relativeReconstructInnerRaw (r.comp s) (relativeSourceAssocPreRaw r s k)) : A ⟶ c.of.1) =
      (F.map t ≫ I.map delta' : A ⟶ c.of.1) :=
    relativeReconstructInnerHom_asNegativeLift (a := a) (b := c)
      (r.comp s) (relativeSourceAssocPreRaw r s k)
  calc
    (F.map f ≫ MonoidalActionCategory.Hom.mk
        (relativeReconstructInnerRaw (a := iteratedLiftObject a r) (b := c) s k) : A ⟶ c.of.1) =
        (F.map f ≫ (F.map g ≫ I.map delta) : A ⟶ c.of.1) :=
      congrArg (fun q : B ⟶ c.of.1 => F.map f ≫ q) hLeft
    _ = (F.map (f ≫ g) ≫ I.map delta : A ⟶ c.of.1) :=
      (Category.assoc (F.map f) (F.map g) (I.map delta)).symm.trans
        (congrArg
          (fun q : A ⟶ F.obj
            (localizedBaseLiftObject (localizedBaseLiftObject a.of.1 rBase) sBase) =>
              q ≫ I.map delta) (F.map_comp f g).symm)
    _ = (F.map (t ≫ I.map alpha) ≫ I.map delta : A ⟶ c.of.1) :=
      congrArg
        (fun q : a.of.1 ⟶ localizedBaseLiftObject
          (localizedBaseLiftObject a.of.1 rBase) sBase => F.map q ≫ I.map delta) hBase
    _ = (F.map t ≫ (F.map (I.map alpha) ≫ I.map delta) : A ⟶ c.of.1) :=
      (congrArg
        (fun q : A ⟶ F.obj
          (localizedBaseLiftObject (localizedBaseLiftObject a.of.1 rBase) sBase) =>
            q ≫ I.map delta) (F.map_comp t (I.map alpha))).trans
        (Category.assoc (F.map t) (F.map (I.map alpha)) (I.map delta))
    _ = (F.map t ≫ I.map delta' : A ⟶ c.of.1) :=
      congrArg
        (fun q : denominatorLeftObject k.stabilizer
          (localizedBaseLiftObject a.of.1 rsBase) ⟶ c.of.1 => F.map t ≫ q) hDelta
    _ = (MonoidalActionCategory.Hom.mk
        (relativeReconstructInnerRaw (r.comp s) (relativeSourceAssocPreRaw r s k)) : A ⟶ c.of.1) :=
      hRight.symm

/-- On every original coefficient representative, precomposition by the actual N lift
is source-associator transport. No incoming factor or lifting result is assumed. -/
theorem iteratedLiftHom_reconstruction_comp_mk {a c : iteratedLocalizedRows C X}
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b)
    (s : RawHom b (iteratedRowProjectionObject c))
    (k : RawHom (relativeCoefficientSource s.stabilizer (iteratedLiftObject a r))
      (relativeCoefficientTarget c)) :
    iteratedLiftHom a r ≫
        relativeReconstructHom (a := iteratedLiftObject a r) (b := c) s
          (MonoidalActionCategory.Hom.mk k) =
      relativeReconstructHom (r.comp s)
        ((relativeSourceAssocIso r s).hom ≫ MonoidalActionCategory.Hom.mk k) := by
  let epsilon : k.stabilizer ⊗ a.of.2 ⟶ c.of.2 := k.hom.1
  let I := MonoidalActionCategory.inclusion (Core C)
    (SInverse (Core C) (FixedTargetExtension C X) × Core C)
  let f := localizedBaseLiftHom a.of.1 r
  let phi : a.of ⟶ (iteratedLiftObject a r).of := (f, 𝟙 a.of.2)
  let q := relativeReconstructOuterRaw (a := iteratedLiftObject a r) (b := c) s k
  let p : RawHom a c :=
    ⟨k.stabilizer,
      ((denominatorLeftFunctor k.stabilizer).map f ≫
        MonoidalActionCategory.Hom.mk
          (relativeReconstructInnerRaw (a := iteratedLiftObject a r) (b := c) s k), k.hom.1)⟩
  have hPre : (⟨k.stabilizer, k.stabilizer ⊴ₗ phi ≫ q.hom⟩ : RawHom a c) = p := by
    apply congrArg
      (fun h : k.stabilizer ⊙ₗ a.of ⟶ c.of => (⟨k.stabilizer, h⟩ : RawHom a c))
    apply Prod.ext
    · change (k.stabilizer ⊴ₗ f) ≫
          MonoidalActionCategory.Hom.mk
            (relativeReconstructInnerRaw (a := iteratedLiftObject a r) (b := c) s k) =
        (denominatorLeftFunctor k.stabilizer).map f ≫
          MonoidalActionCategory.Hom.mk
            (relativeReconstructInnerRaw (a := iteratedLiftObject a r) (b := c) s k)
      exact congrArg
        (fun h : denominatorLeftObject k.stabilizer a.of.1 ⟶
          denominatorLeftObject k.stabilizer (iteratedLiftObject a r).of.1 =>
            h ≫ MonoidalActionCategory.Hom.mk
              (relativeReconstructInnerRaw (a := iteratedLiftObject a r) (b := c) s k))
        (denominatorLeftAction_map_eq k.stabilizer f)
    · change k.stabilizer ◁ 𝟙 a.of.2 ≫ epsilon = epsilon
      rw [whiskerLeft_id, Category.id_comp]
  have hOuter : I.map phi ≫ MonoidalActionCategory.Hom.mk q = MonoidalActionCategory.Hom.mk p :=
    (_root_.Quotient.sound (rawPreMap_rel phi q)).trans
      (congrArg MonoidalActionCategory.Hom.mk hPre)
  have hRaw : p = relativeReconstructOuterRaw (r.comp s) (relativeSourceAssocPreRaw r s k) := by
    apply congrArg
      (fun h : k.stabilizer ⊙ₗ a.of ⟶ c.of => (⟨k.stabilizer, h⟩ : RawHom a c))
    apply Prod.ext
    · exact relativeReconstructInnerHom_afterBaseLift r s k
    · rfl
  calc
    (iteratedLiftHom a r ≫
        relativeReconstructHom (a := iteratedLiftObject a r) (b := c) s
          (MonoidalActionCategory.Hom.mk k) : a ⟶ c) =
        (I.map phi ≫ MonoidalActionCategory.Hom.mk q : a ⟶ c) :=
      congrArg
        (fun h : a ⟶ iteratedLiftObject a r => h ≫ MonoidalActionCategory.Hom.mk q)
        (iteratedLiftHom_asOrdinary a r).symm
    _ = (MonoidalActionCategory.Hom.mk p : a ⟶ c) := hOuter
    _ = (MonoidalActionCategory.Hom.mk
        (relativeReconstructOuterRaw (r.comp s) (relativeSourceAssocPreRaw r s k)) : a ⟶ c) :=
      congrArg MonoidalActionCategory.Hom.mk hRaw
    _ = (relativeReconstructHom (r.comp s)
        ((relativeSourceAssocIso r s).hom ≫ MonoidalActionCategory.Hom.mk k) : a ⟶ c) := by
      rewrite [relativeSourceAssocIso_precompose_mk]
      exact (relativeReconstructHom_mk (r.comp s) (relativeSourceAssocPreRaw r s k)).symm

/-- The complete coefficient quotient has the same literal lift-precomposition formula. -/
theorem iteratedLiftHom_reconstruction_comp {a c : iteratedLocalizedRows C X}
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b)
    (s : RawHom b (iteratedRowProjectionObject c))
    (f : relativeCoefficientSource s.stabilizer (iteratedLiftObject a r) ⟶
      relativeCoefficientTarget c) :
    iteratedLiftHom a r ≫ relativeReconstructHom (a := iteratedLiftObject a r) (b := c) s f =
      relativeReconstructHom (r.comp s) ((relativeSourceAssocIso r s).hom ≫ f) := by
  refine _root_.Quotient.inductionOn f ?_
  intro k
  exact iteratedLiftHom_reconstruction_comp_mk r s k

end AlgebraicKTheory.FixedTargetExtension.IteratedAction

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- Every actual arrow over r followed by g has a unique factor through the original lift.
Its coefficient is transported by the inverse of alpha_R,T,D; no denominator is reset. -/
theorem iteratedLiftHom_existsUnique_factor {a c : iteratedLocalizedRows C X}
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b)
    (g : b ⟶ iteratedRowProjectionObject c) (psi : a ⟶ c)
    (hpsi : iteratedRowProjectionFunctor.map psi = MonoidalActionCategory.Hom.mk r ≫ g) :
    ∃! chi : iteratedLiftObject a r ⟶ c,
      iteratedRowProjectionFunctor.map chi = g ∧ iteratedLiftHom a r ≫ chi = psi := by
  obtain ⟨s, rfl⟩ := MonoidalActionCategory.Hom.exists_rep g
  have hComposite : iteratedRowProjectionFunctor.map psi =
      MonoidalActionCategory.Hom.mk (r.comp s) :=
    hpsi.trans (MonoidalActionCategory.Hom.mk_comp r s)
  let incoming : relativeArrow (r.comp s) := ⟨psi, hComposite⟩
  let e := relativeHomEquiv (r.comp s)
  let k := e.symm incoming
  let i := relativeSourceAssocIso r s
  let f : relativeCoefficientSource s.stabilizer (iteratedLiftObject a r) ⟶
      relativeCoefficientTarget c := i.inv ≫ k
  let chi : iteratedLiftObject a r ⟶ c :=
    relativeReconstructHom (a := iteratedLiftObject a r) (b := c) s f
  have hInverse : relativeReconstructHom (r.comp s) k = psi :=
    congrArg Subtype.val (e.apply_symm_apply incoming)
  have hFactor : iteratedLiftHom a r ≫ chi = psi := by
    calc
      _ = relativeReconstructHom (r.comp s) (i.hom ≫ (i.inv ≫ k)) :=
        iteratedLiftHom_reconstruction_comp r s f
      _ = relativeReconstructHom (r.comp s) k := by
        rw [Iso.hom_inv_id_assoc]
      _ = psi := hInverse
  refine ⟨chi, ⟨relativeReconstructHom_projection
    (a := iteratedLiftObject a r) (b := c) s f, hFactor⟩, ?_⟩
  intro tau hTau
  let tauRelative : relativeArrow (a := iteratedLiftObject a r) (b := c) s :=
    ⟨tau, hTau.1⟩
  let es := relativeHomEquiv (a := iteratedLiftObject a r) (b := c) s
  let fTau := es.symm tauRelative
  have hTauInverse : relativeReconstructHom
      (a := iteratedLiftObject a r) (b := c) s fTau = tau :=
    congrArg Subtype.val (es.apply_symm_apply tauRelative)
  have hComparison : relativeReconstructHom (r.comp s) (i.hom ≫ fTau) =
      relativeReconstructHom (r.comp s) (i.hom ≫ f) :=
    (iteratedLiftHom_reconstruction_comp r s fTau).symm.trans
      ((congrArg
        (fun q : iteratedLiftObject a r ⟶ c => iteratedLiftHom a r ≫ q) hTauInverse).trans
        (hTau.2.trans (hFactor.symm.trans (iteratedLiftHom_reconstruction_comp r s f))))
  have hCoefficients : i.hom ≫ fTau = i.hom ≫ f :=
    relativeReconstructHom_injective (r.comp s) hComparison
  have hEqual : fTau = f := (cancel_epi i.hom).mp hCoefficients
  exact hTauInverse.symm.trans
    (congrArg
      (fun q : relativeCoefficientSource s.stabilizer (iteratedLiftObject a r) ⟶
        relativeCoefficientTarget c =>
          relativeReconstructHom (a := iteratedLiftObject a r) (b := c) s q) hEqual)

/-- The literal represented lift is strongly cocartesian for the original pi_N.
Every HomLift witness is derived from the actual map equality at fixed endpoints. -/
theorem iteratedLiftHom_isStronglyCocartesian (a : iteratedLocalizedRows C X)
    {b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)}
    (r : RawHom (iteratedRowProjectionObject a) b) :
    (iteratedRowProjectionFunctor (C := C) (X := X)).IsStronglyCocartesian
      (MonoidalActionCategory.Hom.mk r) (iteratedLiftHom a r) := by
  let p : iteratedLocalizedRows C X ⥤
      MonoidalActionCategory (Core C) (FixedTargetExtension C X) := iteratedRowProjectionFunctor
  let d : iteratedLocalizedRows C X := iteratedLiftObject a r
  let phi : a ⟶ d := iteratedLiftHom a r
  let f : p.obj a ⟶ p.obj d := MonoidalActionCategory.Hom.mk r
  have hMap : p.map phi = f := iteratedLiftRaw_projection a r
  have hMappedLift : Functor.IsHomLift p (p.map phi) phi := by
    exact .map phi
  have hLift : Functor.IsHomLift p f phi := hMap ▸ hMappedLift
  refine
    { toIsHomLift := hLift
      universal_property' := ?_ }
  intro c g psi hpsi
  have hIncoming : iteratedRowProjectionFunctor.map psi =
      MonoidalActionCategory.Hom.mk r ≫ g :=
    (@CategoryTheory.IsHomLift.eq_of_isHomLift
      (MonoidalActionCategory (Core C) (FixedTargetExtension C X))
      (iteratedLocalizedRows C X) _ _ p a c (f ≫ g) psi hpsi).symm
  obtain ⟨chi, hChi, hUnique⟩ := iteratedLiftHom_existsUnique_factor r g psi hIncoming
  have hMapChi : p.map chi = g := hChi.1
  have hMappedChi : Functor.IsHomLift p (p.map chi) chi := by
    exact .map chi
  have hLiftChi : Functor.IsHomLift p g chi := hMapChi ▸ hMappedChi
  refine ⟨chi, ⟨hLiftChi, hChi.2⟩, ?_⟩
  intro tau hTau
  have hMapTau : p.map tau = g :=
    (@CategoryTheory.IsHomLift.eq_of_isHomLift
      (MonoidalActionCategory (Core C) (FixedTargetExtension C X))
      (iteratedLocalizedRows C X) _ _ p d c g tau hTau.1).symm
  exact hUnique tau ⟨hMapTau, hTau.2⟩

/-- The original iterated row projection is cofibered for every given exact C and X.
This derives the class from all original base representatives, not from a chosen lift premise. -/
theorem iteratedRowProjectionFunctor_isCofibered :
    (iteratedRowProjectionFunctor (C := C) (X := X)).IsCofibered := by
  constructor
  intro a b f
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  exact ⟨iteratedLiftObject a r, iteratedLiftHom a r,
    iteratedLiftHom_isStronglyCocartesian a r⟩

end AlgebraicKTheory.FixedTargetExtension.IteratedAction

end





noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.GenericCoreResidualTranslation
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- Collapse the positive outer Core coordinate into the original row.
The existing inner denominator remains literal. -/
def collapseObject (a : localizedRows (C := C) X) (A : Core C) :
    localizedRows (C := C) X :=
  ⟨(leftSumObj A a.of.1, a.of.2)⟩

/-- The actual action associators and Core braiding interchange four coordinates:
(T,U,A,E) to (U,A,T,E), with the original quotient unchanged. -/
def collapseRowInterchange (T U A : Core C) (E : FixedTargetExtension C X) :
    leftSumObj (T ⊗ U) (leftSumObj A E) ≅
      leftSumObj (U ⊗ A) (leftSumObj T E) :=
  leftSumAssocIso T U (leftSumObj A E) ≪≫
    pairIso (leftSumMap (𝟙 T) (leftSumAssocIso U A E).inv) ≪≫
    (leftSumAssocIso T (U ⊗ A) E).symm ≪≫
    pairIso (leftSumMap (coreBraid T (U ⊗ A)).hom (𝟙 E)) ≪≫
    leftSumAssocIso (U ⊗ A) T E

omit [HasZeroObject C] [ExactCategory C] in
private theorem nativeBiprodMap_id (A B : C) :
    biprod.map (𝟙 A) (𝟙 B) = 𝟙 (A ⊞ B) := by
  apply biprod.hom_ext <;> simp

omit [HasZeroObject C] [ExactCategory C] in
private theorem nativeBiprodMap_comp {A B A' B' A'' B'' : C}
    (f : A ⟶ A') (g : B ⟶ B') (f' : A' ⟶ A'') (g' : B' ⟶ B'') :
    biprod.map f g ≫ biprod.map f' g' = biprod.map (f ≫ f') (g ≫ g') := by
  apply biprod.hom_ext <;> simp [Category.assoc]

private def nativeCollapseInterchange (T U A Z : C) :
    (T ⊞ U) ⊞ (A ⊞ Z) ≅ (U ⊞ A) ⊞ (T ⊞ Z) :=
  biprod.mapIso (biprod.braiding T U) (Iso.refl (A ⊞ Z)) ≪≫
    SInverseS.biprodInterchangeIso U T A Z

omit [HasZeroObject C] [ExactCategory C] in
private theorem nativeCollapseInterchange_naturality
    {T T' U U' A A' Z Z' : C}
    (f : T ⟶ T') (g : U ⟶ U') (h : A ⟶ A') (k : Z ⟶ Z') :
    biprod.map (biprod.map f g) (biprod.map h k) ≫
        (nativeCollapseInterchange T' U' A' Z').hom =
      (nativeCollapseInterchange T U A Z).hom ≫
        biprod.map (biprod.map g h) (biprod.map f k) := by
  let m := biprod.map (biprod.map f g) (biprod.map h k)
  let s := biprod.map (biprod.braiding T U).hom (𝟙 (A ⊞ Z))
  let s' := biprod.map (biprod.braiding T' U').hom (𝟙 (A' ⊞ Z'))
  let n := biprod.map (biprod.map g f) (biprod.map h k)
  let z := biprod.map (biprod.map g h) (biprod.map f k)
  have hSwap : m ≫ s' = s ≫ n := by
    simpa only [m, s, s', n, nativeBiprodMap_comp, Category.id_comp,
      Category.comp_id] using congrArg
      (fun q : T ⊞ U ⟶ U' ⊞ T' => biprod.map q (biprod.map h k))
      (biprod.braid_natural f g)
  have hMiddle : n ≫ (SInverseS.biprodInterchangeIso U' T' A' Z').hom =
      (SInverseS.biprodInterchangeIso U T A Z).hom ≫ z :=
    SInverseS.biprodInterchangeIso_naturality g f h k
  change m ≫ (s' ≫ (SInverseS.biprodInterchangeIso U' T' A' Z').hom) =
    (s ≫ (SInverseS.biprodInterchangeIso U T A Z).hom) ≫ z
  rw [← Category.assoc, hSwap, Category.assoc, hMiddle, ← Category.assoc]

private theorem collapseRowInterchange_middle (T U A : Core C)
    (E : FixedTargetExtension C X) :
    (collapseRowInterchange T U A E).hom.b.hom =
      (nativeCollapseInterchange T.of U.of A.of E.B).hom := by
  have hAssocInv : (leftSumAssocIso T (U ⊗ A) E).inv.b.hom =
      (biprod.associator T.of (U ⊗ A).of E.B).inv := rfl
  simp only [collapseRowInterchange, Iso.trans_hom, Iso.symm_hom, pairIso,
    AlgebraicKTheory.FixedTargetExtension.comp_b]
  simp only [hAssocInv, leftSumMap_b_hom, leftSumAssocIso_b_hom,
    leftSumAssocIso_inv_b_hom, coreBraid_hom_iso_hom, coreBiprodTensorObj_of,
    nativeCollapseInterchange]
  change (biprod.associator T.of U.of (A.of ⊞ E.B)).hom ≫
      biprod.map (𝟙 T.of) (biprod.associator U.of A.of E.B).inv ≫
      (biprod.associator T.of (U.of ⊞ A.of) E.B).inv ≫
      biprod.map (biprod.braiding T.of (U.of ⊞ A.of)).hom (𝟙 E.B) ≫
      (biprod.associator (U.of ⊞ A.of) T.of E.B).hom =
    biprod.map (biprod.braiding T.of U.of).hom (𝟙 (A.of ⊞ E.B)) ≫
      (SInverseS.biprodInterchangeIso U.of T.of A.of E.B).hom
  apply biprod.hom_ext
  · apply biprod.hom_ext <;>
      simp [biprod.associator, biprod.braiding, SInverseS.biprodInterchangeIso,
        biprod.lift_eq, biprod.desc_eq, biprod.map_eq,
        Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
  · apply biprod.hom_ext <;>
      simp [biprod.associator, biprod.braiding, SInverseS.biprodInterchangeIso,
        biprod.lift_eq, biprod.desc_eq, biprod.map_eq,
        Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

/-- Naturality of the actual row interchange in the inner stabilizer.
This is the four-coordinate biproduct naturality, without a new action premise. -/
theorem collapseRowInterchange_natural_inner {T T' : Core C} (f : T ⟶ T')
    (U A : Core C) (E : FixedTargetExtension C X) :
    leftSumMap (f ⊗ₘ 𝟙 U) (𝟙 (leftSumObj A E)) ≫
        (collapseRowInterchange T' U A E).hom =
      (collapseRowInterchange T U A E).hom ≫
        leftSumMap (𝟙 (U ⊗ A)) (leftSumMap f (𝟙 E)) := by
  have hCoreId (Z : Core C) : (𝟙 Z : Z ⟶ Z).iso.hom = 𝟙 Z.of := rfl
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  simp only [hCoreId, FixedTargetExtension.id_b,
    AlgebraicKTheory.FixedTargetExtension.comp_b, Iso.trans_hom, leftSumMap_b_hom,
    collapseRowInterchange_middle, coreBiprodTensorHom_iso_hom, Iso.refl_hom,
    coreBiprodTensorObj_of]
  change biprod.map (biprod.map f.iso.hom (𝟙 U.of)) (𝟙 (A.of ⊞ E.B)) ≫
      (nativeCollapseInterchange T'.of U.of A.of E.B).hom =
    (nativeCollapseInterchange T.of U.of A.of E.B).hom ≫
      biprod.map (𝟙 (U.of ⊞ A.of)) (biprod.map f.iso.hom (𝟙 E.B))
  simpa only [nativeBiprodMap_id] using
    nativeCollapseInterchange_naturality f.iso.hom (𝟙 U.of) (𝟙 A.of) (𝟙 E.B)

/-- Naturality in the outer stabilizer moves its map to the actual outer epsilon.
The inner stabilizer and original row remain fixed. -/
theorem collapseRowInterchange_natural_outer (T : Core C)
    {U U' : Core C} (f : U ⟶ U') (A : Core C) (E : FixedTargetExtension C X) :
    leftSumMap (𝟙 T ⊗ₘ f) (𝟙 (leftSumObj A E)) ≫
        (collapseRowInterchange T U' A E).hom =
      (collapseRowInterchange T U A E).hom ≫
        leftSumMap (f ⊗ₘ 𝟙 A) (𝟙 (leftSumObj T E)) := by
  have hCoreId (Z : Core C) : (𝟙 Z : Z ⟶ Z).iso.hom = 𝟙 Z.of := rfl
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  simp only [hCoreId, FixedTargetExtension.id_b,
    AlgebraicKTheory.FixedTargetExtension.comp_b,
     Iso.trans_hom, leftSumMap_b_hom, collapseRowInterchange_middle,
    coreBiprodTensorHom_iso_hom, Iso.refl_hom, coreBiprodTensorObj_of]
  change biprod.map (biprod.map (𝟙 T.of) f.iso.hom) (𝟙 (A.of ⊞ E.B)) ≫
      (nativeCollapseInterchange T.of U'.of A.of E.B).hom =
    (nativeCollapseInterchange T.of U.of A.of E.B).hom ≫
      biprod.map (biprod.map f.iso.hom (𝟙 A.of)) (𝟙 (T.of ⊞ E.B))
  simpa only [nativeBiprodMap_id] using
    nativeCollapseInterchange_naturality (𝟙 T.of) f.iso.hom (𝟙 A.of) (𝟙 E.B)

/-- Flatten an actual outer U, inner T/gamma/delta, and outer epsilon.
The combined stabilizer is T tensor U. Neither denominator is reset. -/
def collapseRaw (U : Core C)
    {a b : localizedRows (C := C) X} {A B : Core C}
    (r : RawHom (denominatorLeftObject U a) b) (epsilon : U ⊗ A ⟶ B) :
    RawHom (collapseObject a A) (collapseObject b B) where
  stabilizer := r.stabilizer ⊗ U
  hom :=
    ((collapseRowInterchange r.stabilizer U A a.of.1).hom ≫
      leftSumMap epsilon r.hom.1,
      (α_ r.stabilizer U a.of.2).hom ≫ r.hom.2)

/-- The collapse preserves the actual later/outer ordering of the stabilizers. -/
theorem collapseRaw_stabilizer (U : Core C)
    {a b : localizedRows (C := C) X} {A B : Core C}
    (r : RawHom (denominatorLeftObject U a) b) (epsilon : U ⊗ A ⟶ B) :
    (collapseRaw U r epsilon).stabilizer = r.stabilizer ⊗ U := rfl

/-- The full denominator arrow uses alpha.hom, from (T tensor U) tensor D
through T tensor (U tensor D), followed by the actual inner delta. -/
theorem collapseRaw_denominator (U : Core C)
    {a b : localizedRows (C := C) X} {A B : Core C}
    (r : RawHom (denominatorLeftObject U a) b) (epsilon : U ⊗ A ⟶ B) :
    (collapseRaw U r epsilon).hom.2 =
      (α_ r.stabilizer U a.of.2).hom ≫ r.hom.2 := rfl

/-- The full row arrow uses the recorded outer epsilon and inner gamma. -/
theorem collapseRaw_row (U : Core C)
    {a b : localizedRows (C := C) X} {A B : Core C}
    (r : RawHom (denominatorLeftObject U a) b) (epsilon : U ⊗ A ⟶ B) :
    (collapseRaw U r epsilon).hom.1 =
      (collapseRowInterchange r.stabilizer U A a.of.1).hom ≫
        leftSumMap epsilon r.hom.1 := rfl

omit [ExactCategory C] in
private theorem nativeCollapseInterchange_unit (A Z : C) :
    biprod.map (biprod.snd : (0 : C) ⊞ 0 ⟶ 0) (𝟙 (A ⊞ Z)) ≫
        (biprod.snd : (0 : C) ⊞ (A ⊞ Z) ⟶ A ⊞ Z) =
      (nativeCollapseInterchange (0 : C) 0 A Z).hom ≫
        biprod.map (biprod.snd : (0 : C) ⊞ A ⟶ A)
          (biprod.snd : (0 : C) ⊞ Z ⟶ Z) := by
  have hBraid : (biprod.braiding (0 : C) 0).hom = 𝟙 ((0 : C) ⊞ 0) := by
    apply biprod.hom_ext
    · exact (isZero_zero C).eq_of_tgt _ _
    · exact (isZero_zero C).eq_of_tgt _ _
  simp only [nativeCollapseInterchange, Iso.trans_hom, biprod.mapIso_hom,
    Iso.refl_hom, hBraid, nativeBiprodMap_id, Category.id_comp]
  exact SInverseS.biprodInterchangeIso_zero_hom A Z

omit [ExactCategory C] in
private theorem coreLeftUnitor_hom (A : Core C) :
    (show (0 : C) ⊞ A.of ⟶ A.of from (λ_ A).hom.iso.hom) =
      (biprod.snd : (0 : C) ⊞ A.of ⟶ A.of) :=
  congrArg Iso.hom (coreBiprodLeftUnitor_iso A)

/-- The genuine iterated identity is flattened to the original V identity.
Its two zero stabilizers are removed by the given left unitor, not by equality of objects. -/
theorem collapseRaw_identity_rel (a : localizedRows (C := C) X) (A : Core C) :
    (collapseRaw (𝟙_ (Core C))
      (RawHom.ofMap (S := Core C)
        ((𝟙 a.of.1, (λ_ a.of.2).hom) :
          (denominatorLeftObject (𝟙_ (Core C)) a).of ⟶ a.of))
      (λ_ A).hom).Rel (RawHom.id (collapseObject a A)) := by
  refine ⟨λ_ (𝟙_ (Core C)), ?_⟩
  apply Prod.ext
  · change leftSumMap (λ_ (𝟙_ (Core C))).hom (𝟙 (leftSumObj A a.of.1)) ≫
        (leftSumUnitIso (leftSumObj A a.of.1)).hom =
      (collapseRowInterchange (𝟙_ (Core C)) (𝟙_ (Core C)) A a.of.1).hom ≫
        leftSumMap (λ_ A).hom ((leftSumUnitIso a.of.1).hom ≫ 𝟙 a.of.1)
    rw [Category.comp_id]
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [AlgebraicKTheory.FixedTargetExtension.comp_b,
     Iso.trans_hom, leftSumMap_b_hom, leftSumUnitIso_b_hom,
      collapseRowInterchange_middle, coreLeftUnitor_hom,
      coreBiprodTensorUnit_of, coreBiprodTensorObj_of]
    exact nativeCollapseInterchange_unit A.of a.of.1.B
  · change ((λ_ (𝟙_ (Core C))).hom ▷ a.of.2) ≫ (λ_ a.of.2).hom =
      (α_ (𝟙_ (Core C)) (𝟙_ (Core C)) a.of.2).hom ≫
        ((λ_ ((𝟙_ (Core C)) ⊗ a.of.2)).hom ≫ (λ_ a.of.2).hom)
    have hu : (α_ (𝟙_ (Core C)) (𝟙_ (Core C)) a.of.2).hom ≫
        (λ_ ((𝟙_ (Core C)) ⊗ a.of.2)).hom =
      (λ_ (𝟙_ (Core C))).hom ▷ a.of.2 := by
      rw [leftUnitor_tensor_hom (𝟙_ (Core C)) a.of.2, Iso.hom_inv_id_assoc]
    simpa only [Category.assoc] using
      (congrArg (fun q => q ≫ (λ_ a.of.2).hom) hu).symm

omit [ExactCategory C] in
private theorem nativeCollapseInterchange_drop_unit (T Z : C) :
    (nativeCollapseInterchange T (0 : C) 0 Z).hom ≫
        (biprod.snd : ((0 : C) ⊞ 0) ⊞ (T ⊞ Z) ⟶ T ⊞ Z) =
      biprod.map (biprod.fst : T ⊞ (0 : C) ⟶ T) (𝟙 ((0 : C) ⊞ Z)) ≫
        biprod.map (𝟙 T) (biprod.snd : (0 : C) ⊞ Z ⟶ Z) := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext' <;>
      simp [nativeCollapseInterchange, biprod.braiding,
        SInverseS.biprodInterchangeIso, Category.assoc]
  · apply biprod.hom_ext' <;>
      simp [nativeCollapseInterchange, biprod.braiding,
        SInverseS.biprodInterchangeIso, Category.assoc]

omit [ExactCategory C] in
private theorem coreRightUnitor_hom (A : Core C) :
    (show A.of ⊞ (0 : C) ⟶ A.of from (ρ_ A).hom.iso.hom) =
      (biprod.fst : A.of ⊞ (0 : C) ⟶ A.of) :=
  congrArg Iso.hom (coreBiprodRightUnitor_iso A)

/-- At the ordinary outer unit inclusion, the flattened represented morphism
is the conjugate of the actual inner morphism by the given row zero-unitors.
The original denominator and its whole arrow remain unchanged in the conjugate. -/
theorem collapseRaw_unit_transport {a b : localizedRows (C := C) X} (r : RawHom a b) :
    (collapseRaw (𝟙_ (Core C))
      (⟨r.stabilizer, (r.hom.1, r.stabilizer ◁ (λ_ a.of.2).hom ≫ r.hom.2)⟩ :
        RawHom (denominatorLeftObject (𝟙_ (Core C)) a) b)
      (λ_ (𝟙_ (Core C))).hom).Rel
      (⟨r.stabilizer,
        (leftSumMap (𝟙 r.stabilizer) (leftSumUnitIso a.of.1).hom ≫ r.hom.1 ≫
          (leftSumUnitIso b.of.1).inv, r.hom.2)⟩ :
        RawHom (collapseObject a (𝟙_ (Core C))) (collapseObject b (𝟙_ (Core C)))) := by
  have hCoreId (Z : Core C) : (𝟙 Z : Z ⟶ Z).iso.hom = 𝟙 Z.of := rfl
  refine ⟨ρ_ r.stabilizer, ?_⟩
  apply Prod.ext
  · change leftSumMap (ρ_ r.stabilizer).hom (𝟙 (leftSumObj (𝟙_ (Core C)) a.of.1)) ≫
        (leftSumMap (𝟙 r.stabilizer) (leftSumUnitIso a.of.1).hom ≫ r.hom.1 ≫
          (leftSumUnitIso b.of.1).inv) =
      (collapseRowInterchange r.stabilizer (𝟙_ (Core C)) (𝟙_ (Core C)) a.of.1).hom ≫
        leftSumMap (λ_ (𝟙_ (Core C))).hom r.hom.1
    apply (cancel_mono (leftSumUnitIso b.of.1).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [hCoreId, FixedTargetExtension.id_b,
      AlgebraicKTheory.FixedTargetExtension.comp_b,
     Iso.trans_hom, leftSumMap_b_hom, leftSumUnitIso_b_hom,
      collapseRowInterchange_middle, coreRightUnitor_hom, coreLeftUnitor_hom,
      Iso.refl_hom, coreBiprodTensorUnit_of, coreBiprodTensorObj_of]
    dsimp only [leftSumObj]
    let gammaB : r.stabilizer.of ⊞ a.of.1.B ⟶ b.of.1.B := r.hom.1.b.hom
    change biprod.map (biprod.fst : r.stabilizer.of ⊞ (0 : C) ⟶ r.stabilizer.of)
        (𝟙 ((0 : C) ⊞ a.of.1.B)) ≫
        biprod.map (𝟙 r.stabilizer.of) (biprod.snd : (0 : C) ⊞ a.of.1.B ⟶ a.of.1.B) ≫
        gammaB =
      (nativeCollapseInterchange r.stabilizer.of (0 : C) (0 : C) a.of.1.B).hom ≫
        biprod.map (biprod.snd : (0 : C) ⊞ (0 : C) ⟶ (0 : C)) gammaB ≫
        (biprod.snd : (0 : C) ⊞ b.of.1.B ⟶ b.of.1.B)
    simpa only [Category.assoc, biprod.map_snd] using
      (congrArg (fun q => q ≫ gammaB)
        (nativeCollapseInterchange_drop_unit r.stabilizer.of a.of.1.B)).symm
  · change ((ρ_ r.stabilizer).hom ▷ a.of.2) ≫ r.hom.2 =
      (α_ r.stabilizer (𝟙_ (Core C)) a.of.2).hom ≫
        (r.stabilizer ◁ (λ_ a.of.2).hom ≫ r.hom.2)
    simpa only [Category.assoc] using
      (congrArg (fun q => q ≫ r.hom.2) (triangle r.stabilizer a.of.2)).symm

/-- Changing the inner stabilizer changes the combined stabilizer by e tensor Id_U.
The actual row and denominator relations are preserved at their fixed endpoints. -/
theorem collapseRaw_rel_inner (U : Core C)
    {a b : localizedRows (C := C) X} {A B : Core C}
    {r s : RawHom (denominatorLeftObject U a) b} (epsilon : U ⊗ A ⟶ B)
    (h : r.Rel s) : (collapseRaw U r epsilon).Rel (collapseRaw U s epsilon) := by
  obtain ⟨e, he⟩ := h
  let gammaR : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 := r.hom.1
  let gammaS : leftSumObj s.stabilizer a.of.1 ⟶ b.of.1 := s.hom.1
  let deltaR : r.stabilizer ⊗ (U ⊗ a.of.2) ⟶ b.of.2 := r.hom.2
  let deltaS : s.stabilizer ⊗ (U ⊗ a.of.2) ⟶ b.of.2 := s.hom.2
  have hr : leftSumMap e.hom (𝟙 a.of.1) ≫ gammaS = gammaR :=
    congrArg (fun k : r.stabilizer ⊙ₗ (denominatorLeftObject U a).of ⟶ b.of =>
      k.1) he
  have hd : (e.hom ▷ (U ⊗ a.of.2)) ≫ deltaS = deltaR :=
    congrArg (fun k : r.stabilizer ⊙ₗ (denominatorLeftObject U a).of ⟶ b.of =>
      k.2) he
  refine ⟨tensorIso e (Iso.refl U), ?_⟩
  apply Prod.ext
  · change leftSumMap (e.hom ⊗ₘ 𝟙 U) (𝟙 (leftSumObj A a.of.1)) ≫
        ((collapseRowInterchange s.stabilizer U A a.of.1).hom ≫
          leftSumMap epsilon gammaS) =
      (collapseRowInterchange r.stabilizer U A a.of.1).hom ≫
        leftSumMap epsilon gammaR
    calc
      _ = (collapseRowInterchange r.stabilizer U A a.of.1).hom ≫
          leftSumMap (𝟙 (U ⊗ A)) (leftSumMap e.hom (𝟙 a.of.1)) ≫
            leftSumMap epsilon gammaS := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ leftSumMap epsilon gammaS)
          (collapseRowInterchange_natural_inner e.hom U A a.of.1)
      _ = _ := by rw [← leftSumMap_comp, Category.id_comp, hr]
  · change ((e.hom ⊗ₘ 𝟙 U) ▷ a.of.2) ≫
        ((α_ s.stabilizer U a.of.2).hom ≫ deltaS) =
      (α_ r.stabilizer U a.of.2).hom ≫ deltaR
    have hn : ((e.hom ⊗ₘ 𝟙 U) ▷ a.of.2) ≫ (α_ s.stabilizer U a.of.2).hom =
        (α_ r.stabilizer U a.of.2).hom ≫ (e.hom ▷ (U ⊗ a.of.2)) := by
      simpa only [tensorHom_id] using associator_naturality_left e.hom U a.of.2
    calc
      _ = (α_ r.stabilizer U a.of.2).hom ≫
          (e.hom ▷ (U ⊗ a.of.2)) ≫ deltaS := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ deltaS) hn
      _ = _ := by rw [hd]

/-- Flatten the actual inner quotient morphism, with U and epsilon fixed.
This is a map on the original quotient, before the outer quotient is descended. -/
def collapseHom (U : Core C)
    {a b : localizedRows (C := C) X} {A B : Core C}
    (f : denominatorLeftObject U a ⟶ b) (epsilon : U ⊗ A ⟶ B) :
    collapseObject a A ⟶ collapseObject b B :=
  Quotient.map (fun r => collapseRaw U r epsilon)
    (by intro r s h; exact collapseRaw_rel_inner U epsilon h) f

/-- The flattened quotient map retains each represented inner raw arrow. -/
theorem collapseHom_mk (U : Core C)
    {a b : localizedRows (C := C) X} {A B : Core C}
    (r : RawHom (denominatorLeftObject U a) b) (epsilon : U ⊗ A ⟶ B) :
    collapseHom U (MonoidalActionCategory.Hom.mk r) epsilon =
      MonoidalActionCategory.Hom.mk (collapseRaw U r epsilon) := rfl

/-- An ordinary scalar map in the outer denominator action has this exact
inner representative after precomposition. Its row and inner T are unchanged. -/
def collapsePreScalarRaw {U U' : Core C} (f : U ⟶ U')
    {a b : localizedRows (C := C) X} (r : RawHom (denominatorLeftObject U' a) b) :
    RawHom (denominatorLeftObject U a) b where
  stabilizer := r.stabilizer
  hom := (r.hom.1, r.stabilizer ◁ (f ▷ a.of.2) ≫ r.hom.2)

/-- Both actual quotient coordinates respect an outer stabilizer Iso.
The source denominator is carried through the original scalar map, not replaced. -/
theorem collapseRaw_rel_outer {U U' : Core C} (e : U ≅ U')
    {a b : localizedRows (C := C) X} {A B : Core C}
    (r : RawHom (denominatorLeftObject U' a) b)
    (epsilon : U ⊗ A ⟶ B) (epsilon' : U' ⊗ A ⟶ B)
    (hEpsilon : (e.hom ▷ A) ≫ epsilon' = epsilon) :
    (collapseRaw U (collapsePreScalarRaw e.hom r) epsilon).Rel
      (collapseRaw U' r epsilon') := by
  let gamma : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 := r.hom.1
  let delta : r.stabilizer ⊗ (U' ⊗ a.of.2) ⟶ b.of.2 := r.hom.2
  refine ⟨tensorIso (Iso.refl r.stabilizer) e, ?_⟩
  apply Prod.ext
  · change leftSumMap (𝟙 r.stabilizer ⊗ₘ e.hom) (𝟙 (leftSumObj A a.of.1)) ≫
        ((collapseRowInterchange r.stabilizer U' A a.of.1).hom ≫
          leftSumMap epsilon' gamma) =
      (collapseRowInterchange r.stabilizer U A a.of.1).hom ≫
        leftSumMap epsilon gamma
    calc
      _ = (collapseRowInterchange r.stabilizer U A a.of.1).hom ≫
          leftSumMap (e.hom ⊗ₘ 𝟙 A) (𝟙 (leftSumObj r.stabilizer a.of.1)) ≫
            leftSumMap epsilon' gamma := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ leftSumMap epsilon' gamma)
          (collapseRowInterchange_natural_outer r.stabilizer e.hom A a.of.1)
      _ = _ := by
        rw [← leftSumMap_comp, Category.id_comp, tensorHom_id, hEpsilon]
  · change ((𝟙 r.stabilizer ⊗ₘ e.hom) ▷ a.of.2) ≫
        ((α_ r.stabilizer U' a.of.2).hom ≫ delta) =
      (α_ r.stabilizer U a.of.2).hom ≫
        (r.stabilizer ◁ (e.hom ▷ a.of.2) ≫ delta)
    have hn : ((𝟙 r.stabilizer ⊗ₘ e.hom) ▷ a.of.2) ≫
        (α_ r.stabilizer U' a.of.2).hom =
      (α_ r.stabilizer U a.of.2).hom ≫ r.stabilizer ◁ (e.hom ▷ a.of.2) := by
      simpa only [id_tensorHom] using
        associator_naturality_middle r.stabilizer e.hom a.of.2
    simpa only [Category.assoc] using congrArg (fun q => q ≫ delta) hn

private theorem collapsePreScalarRaw_represent {U U' : Core C} (f : U ⟶ U')
    {a b : localizedRows (C := C) X} (r : RawHom (denominatorLeftObject U' a) b) :
    denominatorScalarComponent f a ≫ MonoidalActionCategory.Hom.mk r =
      MonoidalActionCategory.Hom.mk (collapsePreScalarRaw f r) := by
  let gamma : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 := r.hom.1
  let phi : (denominatorLeftObject U a).of ⟶ (denominatorLeftObject U' a).of :=
    (𝟙 a.of.1, f ▷ a.of.2)
  have hh : (collapsePreScalarRaw f r).hom = r.stabilizer ⊴ₗ phi ≫ r.hom := by
    apply Prod.ext
    · change gamma = leftSumMap (𝟙 r.stabilizer) (𝟙 a.of.1) ≫ gamma
      rw [leftSumMap_id, Category.id_comp]
    · rfl
  change MonoidalActionCategory.Hom.mk
      ((RawHom.ofMap (S := Core C) phi).comp r) =
    MonoidalActionCategory.Hom.mk (collapsePreScalarRaw f r)
  apply _root_.Quotient.sound
  refine ⟨ρ_ r.stabilizer, ?_⟩
  change (ρ_ r.stabilizer).hom ⊵ₗ (denominatorLeftObject U a).of ≫
      (collapsePreScalarRaw f r).hom =
    (αₗ r.stabilizer (𝟙_ (Core C)) (denominatorLeftObject U a).of).hom ≫
      r.stabilizer ⊴ₗ ((λₗ[Core C] (denominatorLeftObject U a).of).hom ≫ phi) ≫ r.hom
  simp only [hh, MonoidalLeftAction.rightUnitor_actionHom,
    MonoidalLeftAction.actionHomRight_comp, Category.assoc]

/-- Quotient-level compatibility with the genuine scalar component of the outer action.
This carries the outer stabilizer relation through the actual V precomposition. -/
theorem collapseHom_scalar_transport {U U' : Core C} (e : U ≅ U')
    {a b : localizedRows (C := C) X} {A B : Core C}
    (f : denominatorLeftObject U' a ⟶ b)
    (epsilon : U ⊗ A ⟶ B) (epsilon' : U' ⊗ A ⟶ B)
    (hEpsilon : (e.hom ▷ A) ≫ epsilon' = epsilon) :
    collapseHom U (denominatorScalarComponent e.hom a ≫ f) epsilon =
      collapseHom U' f epsilon' := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  rw [collapsePreScalarRaw_represent]
  change MonoidalActionCategory.Hom.mk
      (collapseRaw U (collapsePreScalarRaw e.hom r) epsilon) =
    MonoidalActionCategory.Hom.mk (collapseRaw U' r epsilon')
  exact _root_.Quotient.sound (collapseRaw_rel_outer e r epsilon epsilon' hEpsilon)

/-- At the ordinary outer unit inclusion, collapse uses exactly the original
row zero-unitor Iso, keeping the inner denominator unchanged. -/
def collapseUnitObjectIso (a : localizedRows (C := C) X) :
    collapseObject a (𝟙_ (Core C)) ≅ a :=
  (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).mapIso
    ((leftSumUnitIso a.of.1).prod (Iso.refl a.of.2))

private theorem rawPreOrdinary_represent
    {a b c : localizedRows (C := C) X} (f : a.of ⟶ b.of) (r : RawHom b c) :
    (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map f ≫
        MonoidalActionCategory.Hom.mk r =
      MonoidalActionCategory.Hom.mk (⟨r.stabilizer, r.stabilizer ⊴ₗ f ≫ r.hom⟩ : RawHom a c) := by
  change MonoidalActionCategory.Hom.mk ((RawHom.ofMap (S := Core C) f).comp r) = _
  apply _root_.Quotient.sound
  refine ⟨ρ_ r.stabilizer, ?_⟩
  simp only [RawHom.comp, RawHom.ofMap, MonoidalLeftAction.rightUnitor_actionHom,
    MonoidalLeftAction.actionHomRight_comp, Category.assoc]

private theorem rawPostOrdinary_represent
    {a b c : localizedRows (C := C) X} (r : RawHom a b) (f : b.of ⟶ c.of) :
    MonoidalActionCategory.Hom.mk r ≫
        (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map f =
      MonoidalActionCategory.Hom.mk (⟨r.stabilizer, r.hom ≫ f⟩ : RawHom a c) := by
  change MonoidalActionCategory.Hom.mk (r.comp (RawHom.ofMap (S := Core C) f)) = _
  apply _root_.Quotient.sound
  refine ⟨λ_ r.stabilizer, ?_⟩
  simp only [RawHom.comp, RawHom.ofMap,
    MonoidalLeftAction.leftUnitor_actionHom, Category.assoc]
  rw [MonoidalLeftAction.actionUnitIso_hom_naturality_assoc]

/-- The actual collapsed map on the ordinary outer-unit inclusion.
Its input is the original inner morphism transported through the proved denominator unitor. -/
def collapseOuterUnitHom {a b : localizedRows (C := C) X} (f : a ⟶ b) :
    collapseObject a (𝟙_ (Core C)) ⟶ collapseObject b (𝟙_ (Core C)) :=
  collapseHom (𝟙_ (Core C)) ((denominatorUnitComponent a).hom ≫ f)
    (λ_ (𝟙_ (Core C))).hom

/-- The actual outer-unit collapsed map is exactly zero-unitor conjugation,
proved on every original quotient representative and not supplied as a functor witness. -/
theorem collapseOuterUnitHom_eq {a b : localizedRows (C := C) X} (f : a ⟶ b) :
    collapseOuterUnitHom f =
      (collapseUnitObjectIso a).hom ≫ f ≫ (collapseUnitObjectIso b).inv := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
  let rH : I.obj a.of ⟶ I.obj b.of := MonoidalActionCategory.Hom.mk r
  let phi : (collapseObject a (𝟙_ (Core C))).of ⟶ a.of :=
    ((leftSumUnitIso a.of.1).hom, 𝟙 a.of.2)
  let psi : b.of ⟶ (collapseObject b (𝟙_ (Core C))).of :=
    ((leftSumUnitIso b.of.1).inv, 𝟙 b.of.2)
  let d : (denominatorLeftObject (𝟙_ (Core C)) a).of ⟶ a.of :=
    (𝟙 a.of.1, (λ_ a.of.2).hom)
  let ru : RawHom (denominatorLeftObject (𝟙_ (Core C)) a) b :=
    ⟨r.stabilizer, (r.hom.1, r.stabilizer ◁ (λ_ a.of.2).hom ≫ r.hom.2)⟩
  let k : RawHom (collapseObject a (𝟙_ (Core C))) (collapseObject b (𝟙_ (Core C))) :=
    ⟨r.stabilizer,
      (leftSumMap (𝟙 r.stabilizer) (leftSumUnitIso a.of.1).hom ≫ r.hom.1 ≫
        (leftSumUnitIso b.of.1).inv, r.hom.2)⟩
  have hdu : (⟨r.stabilizer, r.stabilizer ⊴ₗ d ≫ r.hom⟩ :
      RawHom (denominatorLeftObject (𝟙_ (Core C)) a) b) = ru := by
    apply congrArg (fun h => (⟨r.stabilizer, h⟩ :
      RawHom (denominatorLeftObject (𝟙_ (Core C)) a) b))
    apply Prod.ext
    · change leftSumMap (𝟙 r.stabilizer) (𝟙 a.of.1) ≫ r.hom.1 = r.hom.1
      rw [leftSumMap_id, Category.id_comp]
    · rfl
  have hconj : (⟨r.stabilizer, (r.stabilizer ⊴ₗ phi ≫ r.hom) ≫ psi⟩ :
      RawHom (collapseObject a (𝟙_ (Core C))) (collapseObject b (𝟙_ (Core C)))) = k := by
    apply congrArg (fun h => (⟨r.stabilizer, h⟩ :
      RawHom (collapseObject a (𝟙_ (Core C))) (collapseObject b (𝟙_ (Core C)))))
    apply Prod.ext
    · change (leftSumMap (𝟙 r.stabilizer) (leftSumUnitIso a.of.1).hom ≫ r.hom.1) ≫
          (leftSumUnitIso b.of.1).inv = _
      exact Category.assoc _ _ _
    · change (r.stabilizer ◁ 𝟙 a.of.2 ≫ r.hom.2) ≫ 𝟙 b.of.2 = r.hom.2
      rw [whiskerLeft_id, Category.id_comp, Category.comp_id]
  have hleft : collapseOuterUnitHom (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk
        (collapseRaw (𝟙_ (Core C)) ru (λ_ (𝟙_ (Core C))).hom) := by
    let dH : I.obj (denominatorLeftObject (𝟙_ (Core C)) a).of ⟶ I.obj a.of := I.map d
    have hpre : dH ≫ rH =
        (MonoidalActionCategory.Hom.mk ru :
          I.obj (denominatorLeftObject (𝟙_ (Core C)) a).of ⟶ I.obj b.of) :=
      (rawPreOrdinary_represent
        (a := I.obj (denominatorLeftObject (𝟙_ (Core C)) a).of)
        (b := I.obj a.of) (c := I.obj b.of) d r).trans
          (congrArg
            (fun q : RawHom (I.obj (denominatorLeftObject (𝟙_ (Core C)) a).of)
                (I.obj b.of) => MonoidalActionCategory.Hom.mk q) hdu)
    change collapseHom (𝟙_ (Core C)) (dH ≫ rH) (λ_ (𝟙_ (Core C))).hom = _
    exact (congrArg
      (fun q : I.obj (denominatorLeftObject (𝟙_ (Core C)) a).of ⟶ I.obj b.of =>
        collapseHom (a := a) (b := b) (A := 𝟙_ (Core C)) (B := 𝟙_ (Core C))
          (𝟙_ (Core C)) q (λ_ (𝟙_ (Core C))).hom) hpre).trans
            (collapseHom_mk (a := a) (b := b) (A := 𝟙_ (Core C)) (B := 𝟙_ (Core C))
              (𝟙_ (Core C)) ru (λ_ (𝟙_ (Core C))).hom)
  have hright : (collapseUnitObjectIso a).hom ≫ MonoidalActionCategory.Hom.mk r ≫
      (collapseUnitObjectIso b).inv = MonoidalActionCategory.Hom.mk k := by
    let phiH : I.obj (collapseObject a (𝟙_ (Core C))).of ⟶ I.obj a.of := I.map phi
    let psiH : I.obj b.of ⟶ I.obj (collapseObject b (𝟙_ (Core C))).of := I.map psi
    let rp : RawHom (I.obj (collapseObject a (𝟙_ (Core C))).of) (I.obj b.of) :=
      ⟨r.stabilizer, r.stabilizer ⊴ₗ phi ≫ r.hom⟩
    have hpre : phiH ≫ rH =
        (MonoidalActionCategory.Hom.mk rp :
          I.obj (collapseObject a (𝟙_ (Core C))).of ⟶ I.obj b.of) :=
      rawPreOrdinary_represent (a := I.obj (collapseObject a (𝟙_ (Core C))).of)
        (b := I.obj a.of) (c := I.obj b.of) phi r
    have hpost : (MonoidalActionCategory.Hom.mk rp :
        I.obj (collapseObject a (𝟙_ (Core C))).of ⟶ I.obj b.of) ≫ psiH =
        (MonoidalActionCategory.Hom.mk k :
          I.obj (collapseObject a (𝟙_ (Core C))).of ⟶
            I.obj (collapseObject b (𝟙_ (Core C))).of) :=
      (rawPostOrdinary_represent (a := I.obj (collapseObject a (𝟙_ (Core C))).of)
        (b := I.obj b.of) (c := I.obj (collapseObject b (𝟙_ (Core C))).of) rp psi).trans
          (congrArg
            (fun q : RawHom (I.obj (collapseObject a (𝟙_ (Core C))).of)
                (I.obj (collapseObject b (𝟙_ (Core C))).of) =>
              MonoidalActionCategory.Hom.mk q) hconj)
    change phiH ≫ rH ≫ psiH = _
    exact (Category.assoc phiH rH psiH).symm.trans
      ((congrArg
        (fun q : I.obj (collapseObject a (𝟙_ (Core C))).of ⟶ I.obj b.of => q ≫ psiH)
          hpre).trans hpost)
  exact hleft.trans
    ((_root_.Quotient.sound (collapseRaw_unit_transport r)).trans hright.symm)

/-- The genuine restriction of collapse to the ordinary outer unit is a functor. -/
def collapseOuterUnitFunctor : localizedRows (C := C) X ⥤ localizedRows (C := C) X where
  obj a := collapseObject a (𝟙_ (Core C))
  map f := collapseOuterUnitHom f
  map_id a := by
    rw [collapseOuterUnitHom_eq, Category.id_comp]
    exact (collapseUnitObjectIso a).hom_inv_id
  map_comp f g := by
    rw [collapseOuterUnitHom_eq, collapseOuterUnitHom_eq, collapseOuterUnitHom_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The complete natural zero-unitor comparison on the ordinary outer-unit restriction.
It identifies that actual restriction with Id_V; no eta or comparison weakness is asserted. -/
def collapseOuterUnitNatIso : collapseOuterUnitFunctor (C := C) (X := X) ≅
    𝟭 (localizedRows (C := C) X) :=
  NatIso.ofComponents collapseUnitObjectIso (by
    intro a b f
    change collapseOuterUnitHom f ≫ (collapseUnitObjectIso b).hom =
      (collapseUnitObjectIso a).hom ≫ f
    rw [collapseOuterUnitHom_eq]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-! The following block is ordered after the genuine denominatorLeftAction provider.
Its instance is the declared left-denominator action, not a free action or result witness.
The completed category retains the original positive outer Core coordinate. -/

attribute [local instance] denominatorLeftAction

/-- The original completed iterated action, with literal ((E,D),A) objects. -/
abbrev iteratedLocalizedRows :=
  SInverse (Core C) (localizedRows (C := C) X)

/-- Collapse keeps D and adds the positive outer A to the original row E. -/
def collapseIteratedObject (a : iteratedLocalizedRows (C := C) (X := X)) :
    localizedRows (C := C) X := collapseObject a.of.1 a.of.2

/-- Flatten an actual outer raw arrow using the previously descended inner quotient map. -/
def collapseIteratedRaw
    {a b : iteratedLocalizedRows (C := C) (X := X)} (r : RawHom a b) :
    collapseIteratedObject a ⟶ collapseIteratedObject b :=
  collapseHom r.stabilizer r.hom.1 r.hom.2

/-- The actual denominator action scalar component carries the whole outer Raw.Rel
through collapse. Both positive and negative stabilizer coordinates are retained. -/
theorem collapseIteratedRaw_rel
    {a b : iteratedLocalizedRows (C := C) (X := X)} {r s : RawHom a b}
    (h : r.Rel s) : collapseIteratedRaw r = collapseIteratedRaw s := by
  obtain ⟨e, he⟩ := h
  have hi : denominatorScalarComponent e.hom a.of.1 ≫ s.hom.1 = r.hom.1 :=
    congrArg (fun f : r.stabilizer ⊙ₗ a.of ⟶ b.of => f.1) he
  have hd : (e.hom ▷ a.of.2) ≫ s.hom.2 = r.hom.2 :=
    congrArg (fun f : r.stabilizer ⊙ₗ a.of ⟶ b.of => f.2) he
  change collapseHom r.stabilizer r.hom.1 r.hom.2 =
    collapseHom s.stabilizer s.hom.1 s.hom.2
  rw [← hi]
  exact collapseHom_scalar_transport e s.hom.1 r.hom.2 s.hom.2 hd

/-- The canonical map of completed quotient morphisms underlying Gamma.
Composition is a separate derived law; no functor or weakness witness is supplied here. -/
def collapseIteratedHom
    {a b : iteratedLocalizedRows (C := C) (X := X)} (f : a ⟶ b) :
    collapseIteratedObject a ⟶ collapseIteratedObject b :=
  Quotient.lift collapseIteratedRaw (by intro r s h; exact collapseIteratedRaw_rel h) f

/-- Each actual completed outer representative is flattened by its original U/inner map/epsilon. -/
theorem collapseIteratedHom_mk
    {a b : iteratedLocalizedRows (C := C) (X := X)} (r : RawHom a b) :
    collapseIteratedHom (MonoidalActionCategory.Hom.mk r) =
      collapseHom r.stabilizer r.hom.1 r.hom.2 := rfl

/-- The actual completed quotient identity is preserved. -/
theorem collapseIteratedHom_id (a : iteratedLocalizedRows (C := C) (X := X)) :
    collapseIteratedHom (𝟙 a) = 𝟙 (collapseIteratedObject a) := by
  change MonoidalActionCategory.Hom.mk
      (collapseRaw (𝟙_ (Core C))
        (RawHom.ofMap (S := Core C)
          ((𝟙 a.of.1.of.1, (λ_ a.of.1.of.2).hom) :
            (denominatorLeftObject (𝟙_ (Core C)) a.of.1).of ⟶ a.of.1.of))
        (λ_ a.of.2).hom) =
    MonoidalActionCategory.Hom.mk (RawHom.id (collapseObject a.of.1 a.of.2))
  exact _root_.Quotient.sound (collapseRaw_identity_rel a.of.1 a.of.2)

/-- The actual completed positive inclusion uses precisely the proved outer-unit map. -/
theorem collapseIteratedHom_inclusion {a b : localizedRows (C := C) X} (f : a ⟶ b) :
    collapseIteratedHom ((SInverse.inclusion (Core C) (localizedRows (C := C) X)).map f) =
      collapseOuterUnitHom f := by
  change collapseHom (𝟙_ (Core C)) ((denominatorUnitComponent a).hom ≫ f)
      ((λ_ (𝟙_ (Core C))).hom ≫ 𝟙 (𝟙_ (Core C))) = _
  rewrite [Category.comp_id]
  rfl

/-- A fixed outer V translates the first inner arrow, after the actual outer alpha.
Its row stays literal; only the denominator is precomposed by alpha and the given swap. -/
def collapseComposedInnerRaw (U V : Core C)
    {a b c : localizedRows (C := C) X}
    (r : RawHom (denominatorLeftObject U a) b)
    (s : RawHom (denominatorLeftObject V b) c) :
    RawHom (denominatorLeftObject (V ⊗ U) a) c where
  stabilizer := s.stabilizer ⊗ r.stabilizer
  hom :=
    ((leftSumAssocIso s.stabilizer r.stabilizer a.of.1).hom ≫
      leftSumMap (𝟙 s.stabilizer) r.hom.1 ≫ s.hom.1,
      (α_ s.stabilizer r.stabilizer ((V ⊗ U) ⊗ a.of.2)).hom ≫
        s.stabilizer ◁
          (r.stabilizer ◁ (α_ V U a.of.2).hom ≫
            (denominatorInterchangeIso V r.stabilizer (U ⊗ a.of.2)).hom ≫
              V ◁ r.hom.2) ≫ s.hom.2)

/-- The original outer composition coordinate keeps alpha.hom, then V acts on epsilon. -/
def collapseComposedEpsilon (U V : Core C) {A B P : Core C}
    (epsilon : U ⊗ A ⟶ B) (theta : V ⊗ B ⟶ P) : (V ⊗ U) ⊗ A ⟶ P :=
  (α_ V U A).hom ≫ V ◁ epsilon ≫ theta

/-- The two total stabilizers are compared by the genuine middle-four Core Iso.
This sends ((R,T),(V,U)) to ((R,V),(T,U)), preserving the original composition order. -/
def collapseCompositionStabilizerIso (R T V U : Core C) :
    (R ⊗ T) ⊗ (V ⊗ U) ≅ (R ⊗ V) ⊗ (T ⊗ U) :=
  Core.isoMk (SInverseS.biprodInterchangeIso R.of T.of V.of U.of)

omit [ExactCategory C] in
private theorem coreWhiskerLeft_hom (T : Core C) {A B : Core C} (f : A ⟶ B) :
    (T ◁ f).iso.hom = biprod.map (𝟙 T.of) f.iso.hom := by
  rewrite [← id_tensorHom, coreBiprodTensorHom_iso_hom]
  rfl

omit [ExactCategory C] in
private theorem coreWhiskerRight_hom {T U : Core C} (f : T ⟶ U) (A : Core C) :
    (f ▷ A).iso.hom = biprod.map f.iso.hom (𝟙 A.of) := by
  rewrite [← tensorHom_id, coreBiprodTensorHom_iso_hom]
  rfl

omit [ExactCategory C] in
private theorem coreAssociator_hom (T U A : Core C) :
    (α_ T U A).hom.iso.hom = (biprod.associator T.of U.of A.of).hom :=
  congrArg Iso.hom (coreBiprodAssociator_iso T U A)

omit [HasZeroObject C] [ExactCategory C] in
private theorem nativeCollapseComposition (R T V U A B P E F G : C)
    (epsilon : U ⊞ A ⟶ B) (theta : V ⊞ B ⟶ P)
    (f : T ⊞ E ⟶ F) (g : R ⊞ F ⟶ G) :
    biprod.map (SInverseS.biprodInterchangeIso R T V U).hom (𝟙 (A ⊞ E)) ≫
        (biprod.associator (R ⊞ V) (T ⊞ U) (A ⊞ E)).hom ≫
        biprod.map (𝟙 (R ⊞ V))
          ((nativeCollapseInterchange T U A E).hom ≫ biprod.map epsilon f) ≫
        (nativeCollapseInterchange R V B F).hom ≫ biprod.map theta g =
      (nativeCollapseInterchange (R ⊞ T) (V ⊞ U) A E).hom ≫
        biprod.map
          ((biprod.associator V U A).hom ≫ biprod.map (𝟙 V) epsilon ≫ theta)
          ((biprod.associator R T E).hom ≫ biprod.map (𝟙 R) f ≫ g) := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    · apply biprod.hom_ext' <;>
        simp [nativeCollapseInterchange, SInverseS.biprodInterchangeIso,
          biprod.associator, biprod.braiding, biprod.lift_eq, biprod.desc_eq,
          biprod.map_eq, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    · apply biprod.hom_ext' <;>
        simp [nativeCollapseInterchange, SInverseS.biprodInterchangeIso,
          biprod.associator, biprod.braiding, biprod.lift_eq, biprod.desc_eq,
          biprod.map_eq, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
  · apply biprod.hom_ext' <;>
      simp [nativeCollapseInterchange, SInverseS.biprodInterchangeIso,
        biprod.associator, biprod.braiding, biprod.lift_eq, biprod.desc_eq,
          biprod.map_eq, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

omit [HasZeroObject C] [ExactCategory C] in
private theorem nativeCollapseDenComposition (R T V U D D' D'' : C)
    (f : T ⊞ (U ⊞ D) ⟶ D') (g : R ⊞ (V ⊞ D') ⟶ D'') :
    biprod.map (SInverseS.biprodInterchangeIso R T V U).hom (𝟙 D) ≫
        (biprod.associator (R ⊞ V) (T ⊞ U) D).hom ≫
        biprod.map (𝟙 (R ⊞ V)) ((biprod.associator T U D).hom ≫ f) ≫
        (biprod.associator R V D').hom ≫ g =
      (biprod.associator (R ⊞ T) (V ⊞ U) D).hom ≫
        (biprod.associator R T ((V ⊞ U) ⊞ D)).hom ≫
        biprod.map (𝟙 R)
          (biprod.map (𝟙 T) (biprod.associator V U D).hom ≫
            (SInverseS.swapStabilizerIso V T (U ⊞ D)).hom ≫ biprod.map (𝟙 V) f) ≫ g := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    · apply biprod.hom_ext' <;>
        simp [SInverseS.biprodInterchangeIso, SInverseS.swapStabilizerIso,
          biprod.associator, biprod.braiding, biprod.lift_eq, biprod.desc_eq,
          biprod.map_eq, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    · apply biprod.hom_ext' <;>
        simp [SInverseS.biprodInterchangeIso, SInverseS.swapStabilizerIso,
          biprod.associator, biprod.braiding, biprod.lift_eq, biprod.desc_eq,
          biprod.map_eq, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
  · simp [SInverseS.biprodInterchangeIso, SInverseS.swapStabilizerIso,
      biprod.associator, biprod.braiding, biprod.lift_eq, biprod.desc_eq,
          biprod.map_eq, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

private theorem collapseRaw_middle (U : Core C)
    {a b : localizedRows (C := C) X} {A B : Core C}
    (r : RawHom (denominatorLeftObject U a) b) (epsilon : U ⊗ A ⟶ B) :
    (collapseRaw U r epsilon).hom.1.b.hom =
      (nativeCollapseInterchange r.stabilizer.of U.of A.of a.of.1.B).hom ≫
        biprod.map epsilon.iso.hom r.hom.1.b.hom := by
  change ((collapseRowInterchange r.stabilizer U A a.of.1).hom.b.hom ≫
    (leftSumMap epsilon r.hom.1).b.hom) = _
  rw [collapseRowInterchange_middle, leftSumMap_b_hom]
  rfl

private theorem collapseRaw_den_hom (U : Core C)
    {a b : localizedRows (C := C) X} {A B : Core C}
    (r : RawHom (denominatorLeftObject U a) b) (epsilon : U ⊗ A ⟶ B) :
    (collapseRaw U r epsilon).hom.2.iso.hom =
      (biprod.associator r.stabilizer.of U.of a.of.2.of).hom ≫ r.hom.2.iso.hom := by
  change (α_ r.stabilizer U a.of.2).hom.iso.hom ≫ r.hom.2.iso.hom = _
  rw [coreAssociator_hom]

private theorem rawComp_middle {a b c : localizedRows (C := C) X}
    (r : RawHom a b) (s : RawHom b c) :
    (r.comp s).hom.1.b.hom =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.B).hom ≫
        biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom ≫ s.hom.1.b.hom := by
  change (leftSumAssocIso s.stabilizer r.stabilizer a.of.1).hom.b.hom ≫
    (leftSumMap (𝟙 s.stabilizer) r.hom.1).b.hom ≫ s.hom.1.b.hom = _
  rw [leftSumAssocIso_b_hom, leftSumMap_b_hom]
  rfl

private theorem rawComp_den_hom {a b c : localizedRows (C := C) X}
    (r : RawHom a b) (s : RawHom b c) :
    (r.comp s).hom.2.iso.hom =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.2.of).hom ≫
        biprod.map (𝟙 s.stabilizer.of) r.hom.2.iso.hom ≫ s.hom.2.iso.hom := by
  change (α_ s.stabilizer r.stabilizer a.of.2).hom.iso.hom ≫
    (s.stabilizer ◁ r.hom.2).iso.hom ≫ s.hom.2.iso.hom = _
  rw [coreAssociator_hom, coreWhiskerLeft_hom]
  rfl

private theorem collapseComposedInner_middle (U V : Core C)
    {a b c : localizedRows (C := C) X}
    (r : RawHom (denominatorLeftObject U a) b)
    (s : RawHom (denominatorLeftObject V b) c) :
    (collapseComposedInnerRaw U V r s).hom.1.b.hom =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.B).hom ≫
        biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom ≫ s.hom.1.b.hom := by
  let gammaR : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 := r.hom.1
  let gammaS : leftSumObj s.stabilizer b.of.1 ⟶ c.of.1 := s.hom.1
  change (leftSumAssocIso s.stabilizer r.stabilizer a.of.1).hom.b.hom ≫
    (leftSumMap (𝟙 s.stabilizer) gammaR).b.hom ≫ gammaS.b.hom = _
  rw [leftSumAssocIso_b_hom, leftSumMap_b_hom]
  rfl

private theorem collapseComposedInner_den_hom (U V : Core C)
    {a b c : localizedRows (C := C) X}
    (r : RawHom (denominatorLeftObject U a) b)
    (s : RawHom (denominatorLeftObject V b) c) :
    (collapseComposedInnerRaw U V r s).hom.2.iso.hom =
      (biprod.associator s.stabilizer.of r.stabilizer.of
        ((V.of ⊞ U.of) ⊞ a.of.2.of)).hom ≫
        biprod.map (𝟙 s.stabilizer.of)
          (biprod.map (𝟙 r.stabilizer.of) (biprod.associator V.of U.of a.of.2.of).hom ≫
            (SInverseS.swapStabilizerIso V.of r.stabilizer.of (U.of ⊞ a.of.2.of)).hom ≫
              biprod.map (𝟙 V.of) r.hom.2.iso.hom) ≫ s.hom.2.iso.hom := by
  let deltaR : r.stabilizer ⊗ (U ⊗ a.of.2) ⟶ b.of.2 := r.hom.2
  let deltaS : s.stabilizer ⊗ (V ⊗ b.of.2) ⟶ c.of.2 := s.hom.2
  let inner : r.stabilizer ⊗ ((V ⊗ U) ⊗ a.of.2) ⟶ V ⊗ b.of.2 :=
    r.stabilizer ◁ (α_ V U a.of.2).hom ≫
      (denominatorInterchangeIso V r.stabilizer (U ⊗ a.of.2)).hom ≫ V ◁ deltaR
  change (α_ s.stabilizer r.stabilizer ((V ⊗ U) ⊗ a.of.2)).hom.iso.hom ≫
    (s.stabilizer ◁ inner).iso.hom ≫ deltaS.iso.hom = _
  rw [coreAssociator_hom, coreWhiskerLeft_hom]
  dsimp only [inner]
  simp only [coreCategory_comp_iso, Iso.trans_hom, coreAssociator_hom,
    coreWhiskerLeft_hom, denominatorInterchangeIso_hom, coreBiprodTensorObj_of]
  rfl

omit [ExactCategory C] in
private theorem collapseComposedEpsilon_hom (U V : Core C) {A B P : Core C}
    (epsilon : U ⊗ A ⟶ B) (theta : V ⊗ B ⟶ P) :
    (collapseComposedEpsilon U V epsilon theta).iso.hom =
      (biprod.associator V.of U.of A.of).hom ≫
        biprod.map (𝟙 V.of) epsilon.iso.hom ≫ theta.iso.hom := by
  simp only [collapseComposedEpsilon, coreCategory_comp_iso, Iso.trans_hom,
    coreAssociator_hom, coreWhiskerLeft_hom]
  rfl

/-- Full represented composition compatibility for Gamma. The first/second denominators,
positive coordinates, later/earlier stabilizers and alpha.hom are all the original maps. -/
theorem collapseRaw_composition_rel (U V : Core C)
    {a b c : localizedRows (C := C) X} {A B P : Core C}
    (r : RawHom (denominatorLeftObject U a) b)
    (s : RawHom (denominatorLeftObject V b) c)
    (epsilon : U ⊗ A ⟶ B) (theta : V ⊗ B ⟶ P) :
    (collapseRaw (V ⊗ U) (collapseComposedInnerRaw U V r s)
      (collapseComposedEpsilon U V epsilon theta)).Rel
      ((collapseRaw U r epsilon).comp (collapseRaw V s theta)) := by
  let aa : localizedRows (C := C) X := collapseObject a A
  let bb : localizedRows (C := C) X := collapseObject b B
  let cc : localizedRows (C := C) X := collapseObject c P
  let rr : RawHom aa bb := collapseRaw U (a := a) (b := b) (A := A) (B := B) r epsilon
  let ss : RawHom bb cc := collapseRaw V (a := b) (b := c) (A := B) (B := P) s theta
  let tt : RawHom aa cc := collapseRaw (V ⊗ U) (a := a) (b := c) (A := A) (B := P)
    (collapseComposedInnerRaw U V (a := a) (b := b) (c := c) r s)
    (collapseComposedEpsilon U V epsilon theta)
  let chi := collapseCompositionStabilizerIso s.stabilizer r.stabilizer V U
  have hChi : chi.hom.iso.hom =
      (SInverseS.biprodInterchangeIso s.stabilizer.of r.stabilizer.of V.of U.of).hom := by
    simp only [chi, collapseCompositionStabilizerIso, Core.isoMk_hom_iso]
  refine ⟨chi, ?_⟩
  apply Prod.ext
  · apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    have hR : rr.hom.1.b.hom =
        (nativeCollapseInterchange r.stabilizer.of U.of A.of a.of.1.B).hom ≫
          biprod.map epsilon.iso.hom r.hom.1.b.hom :=
      collapseRaw_middle U (a := a) (b := b) (A := A) (B := B) r epsilon
    have hS : ss.hom.1.b.hom =
        (nativeCollapseInterchange s.stabilizer.of V.of B.of b.of.1.B).hom ≫
          biprod.map theta.iso.hom s.hom.1.b.hom :=
      collapseRaw_middle V (a := b) (b := c) (A := B) (B := P) s theta
    have hComp : (rr.comp ss).hom.1.b.hom =
        (biprod.associator (s.stabilizer.of ⊞ V.of) (r.stabilizer.of ⊞ U.of)
          (A.of ⊞ a.of.1.B)).hom ≫
          biprod.map (𝟙 (s.stabilizer.of ⊞ V.of))
            ((nativeCollapseInterchange r.stabilizer.of U.of A.of a.of.1.B).hom ≫
              biprod.map epsilon.iso.hom r.hom.1.b.hom) ≫
          (nativeCollapseInterchange s.stabilizer.of V.of B.of b.of.1.B).hom ≫
            biprod.map theta.iso.hom s.hom.1.b.hom := by
      have h := rawComp_middle (a := aa) (b := bb) (c := cc) rr ss
      change (rr.comp ss).hom.1.b.hom =
        (biprod.associator (s.stabilizer.of ⊞ V.of) (r.stabilizer.of ⊞ U.of)
          (A.of ⊞ a.of.1.B)).hom ≫
          biprod.map (𝟙 (s.stabilizer.of ⊞ V.of)) rr.hom.1.b.hom ≫ ss.hom.1.b.hom at h
      exact h.trans (by rw [hR, hS]; rfl)
    have hTarget : tt.hom.1.b.hom =
        (nativeCollapseInterchange (s.stabilizer.of ⊞ r.stabilizer.of)
          (V.of ⊞ U.of) A.of a.of.1.B).hom ≫
          biprod.map
            ((biprod.associator V.of U.of A.of).hom ≫
              biprod.map (𝟙 V.of) epsilon.iso.hom ≫ theta.iso.hom)
            ((biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.B).hom ≫
              biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom ≫ s.hom.1.b.hom) := by
      have h := collapseRaw_middle (V ⊗ U) (a := a) (b := c) (A := A) (B := P)
        (collapseComposedInnerRaw U V (a := a) (b := b) (c := c) r s)
        (collapseComposedEpsilon U V epsilon theta)
      change tt.hom.1.b.hom =
        (nativeCollapseInterchange (s.stabilizer.of ⊞ r.stabilizer.of)
          (V.of ⊞ U.of) A.of a.of.1.B).hom ≫
          biprod.map (collapseComposedEpsilon U V epsilon theta).iso.hom
            (collapseComposedInnerRaw U V (a := a) (b := b) (c := c) r s).hom.1.b.hom at h
      exact h.trans (by rw [collapseComposedEpsilon_hom U V epsilon theta,
        collapseComposedInner_middle U V (a := a) (b := b) (c := c) r s])
    change biprod.map chi.hom.iso.hom (𝟙 (A.of ⊞ a.of.1.B)) ≫
      (rr.comp ss).hom.1.b.hom = tt.hom.1.b.hom
    rw [hChi, hComp, hTarget]
    exact nativeCollapseComposition s.stabilizer.of r.stabilizer.of V.of U.of
      A.of B.of P.of a.of.1.B b.of.1.B c.of.1.B epsilon.iso.hom theta.iso.hom
        r.hom.1.b.hom s.hom.1.b.hom
  · apply Core.hom_ext
    have hR : rr.hom.2.iso.hom =
        (biprod.associator r.stabilizer.of U.of a.of.2.of).hom ≫ r.hom.2.iso.hom :=
      collapseRaw_den_hom U (a := a) (b := b) (A := A) (B := B) r epsilon
    have hS : ss.hom.2.iso.hom =
        (biprod.associator s.stabilizer.of V.of b.of.2.of).hom ≫ s.hom.2.iso.hom :=
      collapseRaw_den_hom V (a := b) (b := c) (A := B) (B := P) s theta
    have hComp : (rr.comp ss).hom.2.iso.hom =
        (biprod.associator (s.stabilizer.of ⊞ V.of) (r.stabilizer.of ⊞ U.of) a.of.2.of).hom ≫
          biprod.map (𝟙 (s.stabilizer.of ⊞ V.of))
            ((biprod.associator r.stabilizer.of U.of a.of.2.of).hom ≫ r.hom.2.iso.hom) ≫
          (biprod.associator s.stabilizer.of V.of b.of.2.of).hom ≫ s.hom.2.iso.hom := by
      have h := rawComp_den_hom (a := aa) (b := bb) (c := cc) rr ss
      change (rr.comp ss).hom.2.iso.hom =
        (biprod.associator (s.stabilizer.of ⊞ V.of) (r.stabilizer.of ⊞ U.of) a.of.2.of).hom ≫
          biprod.map (𝟙 (s.stabilizer.of ⊞ V.of)) rr.hom.2.iso.hom ≫ ss.hom.2.iso.hom at h
      exact h.trans (by rw [hR, hS]; rfl)
    have hTarget : tt.hom.2.iso.hom =
        (biprod.associator (s.stabilizer.of ⊞ r.stabilizer.of) (V.of ⊞ U.of) a.of.2.of).hom ≫
          (biprod.associator s.stabilizer.of r.stabilizer.of
            ((V.of ⊞ U.of) ⊞ a.of.2.of)).hom ≫
          biprod.map (𝟙 s.stabilizer.of)
            (biprod.map (𝟙 r.stabilizer.of) (biprod.associator V.of U.of a.of.2.of).hom ≫
              (SInverseS.swapStabilizerIso V.of r.stabilizer.of (U.of ⊞ a.of.2.of)).hom ≫
                biprod.map (𝟙 V.of) r.hom.2.iso.hom) ≫ s.hom.2.iso.hom := by
      have h := collapseRaw_den_hom (V ⊗ U) (a := a) (b := c) (A := A) (B := P)
        (collapseComposedInnerRaw U V (a := a) (b := b) (c := c) r s)
        (collapseComposedEpsilon U V epsilon theta)
      change tt.hom.2.iso.hom =
        (biprod.associator (s.stabilizer.of ⊞ r.stabilizer.of) (V.of ⊞ U.of) a.of.2.of).hom ≫
          (collapseComposedInnerRaw U V (a := a) (b := b) (c := c) r s).hom.2.iso.hom at h
      exact h.trans (by rw [collapseComposedInner_den_hom U V (a := a) (b := b) (c := c) r s])
    have hChiDen : (chi.hom ▷ a.of.2).iso.hom =
        biprod.map
          (SInverseS.biprodInterchangeIso s.stabilizer.of r.stabilizer.of V.of U.of).hom
            (𝟙 a.of.2.of) := by
      exact (coreWhiskerRight_hom chi.hom a.of.2).trans
        (congrArg (fun f => biprod.map f (𝟙 a.of.2.of)) hChi)
    change (chi.hom ▷ a.of.2).iso.hom ≫
      (rr.comp ss).hom.2.iso.hom = tt.hom.2.iso.hom
    rw [hChiDen, hComp, hTarget]
    exact nativeCollapseDenComposition s.stabilizer.of r.stabilizer.of V.of U.of
      a.of.2.of b.of.2.of c.of.2.of r.hom.2.iso.hom s.hom.2.iso.hom

private theorem collapseComposedInner_represent (U V : Core C)
    {a b c : localizedRows (C := C) X}
    (r : RawHom (denominatorLeftObject U a) b)
    (s : RawHom (denominatorLeftObject V b) c) :
    (denominatorAssocComponent V U a).hom ≫
        (denominatorLeftFunctor V).map (MonoidalActionCategory.Hom.mk r) ≫
        MonoidalActionCategory.Hom.mk s =
      MonoidalActionCategory.Hom.mk (collapseComposedInnerRaw U V r s) := by
  let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
  let gammaR : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 := r.hom.1
  let gammaS : leftSumObj s.stabilizer b.of.1 ⟶ c.of.1 := s.hom.1
  let phi : (denominatorLeftObject (V ⊗ U) a).of ⟶
      (denominatorLeftObject V (denominatorLeftObject U a)).of :=
    (𝟙 a.of.1, (α_ V U a.of.2).hom)
  let h : RawHom (denominatorLeftObject (V ⊗ U) a) (denominatorLeftObject V b) :=
    ⟨r.stabilizer, r.stabilizer ⊴ₗ phi ≫ (denominatorLeftRaw V r).hom⟩
  have hh : h.comp s = collapseComposedInnerRaw U V r s := by
    apply congrArg (fun k => (⟨s.stabilizer ⊗ r.stabilizer, k⟩ :
      RawHom (denominatorLeftObject (V ⊗ U) a) c))
    apply Prod.ext
    · change (leftSumAssocIso s.stabilizer r.stabilizer a.of.1).hom ≫
          leftSumMap (𝟙 s.stabilizer)
            (leftSumMap (𝟙 r.stabilizer) (𝟙 a.of.1) ≫ gammaR) ≫ gammaS =
        (leftSumAssocIso s.stabilizer r.stabilizer a.of.1).hom ≫
          leftSumMap (𝟙 s.stabilizer) gammaR ≫ gammaS
      have hId : leftSumMap (𝟙 r.stabilizer) (𝟙 a.of.1) ≫ gammaR = gammaR :=
        (congrArg
          (fun q : leftSumObj r.stabilizer a.of.1 ⟶ leftSumObj r.stabilizer a.of.1 =>
            q ≫ gammaR)
          (AlgebraicKTheory.FixedTargetExtension.leftSumMap_id r.stabilizer a.of.1)).trans
            (Category.id_comp gammaR)
      exact congrArg
        (fun q : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 =>
          (leftSumAssocIso s.stabilizer r.stabilizer a.of.1).hom ≫
            leftSumMap (𝟙 s.stabilizer) q ≫ gammaS) hId
    · change (α_ s.stabilizer r.stabilizer ((V ⊗ U) ⊗ a.of.2)).hom ≫
          s.stabilizer ◁
            (r.stabilizer ◁ (α_ V U a.of.2).hom ≫
              (denominatorInterchangeIso V r.stabilizer (U ⊗ a.of.2)).hom ≫
                V ◁ r.hom.2) ≫ s.hom.2 = _
      rfl
  let A := I.obj (denominatorLeftObject (V ⊗ U) a).of
  let B := I.obj (denominatorLeftObject V (denominatorLeftObject U a)).of
  let D := I.obj (denominatorLeftObject V b).of
  let Cc := I.obj c.of
  let phiH : A ⟶ B := I.map phi
  let rH : B ⟶ D := (denominatorLeftFunctor V).map (MonoidalActionCategory.Hom.mk r)
  let sH : D ⟶ Cc := MonoidalActionCategory.Hom.mk s
  have hmap : rH = (MonoidalActionCategory.Hom.mk (denominatorLeftRaw V r) : B ⟶ D) :=
    denominatorLeftFunctor_map_mk V r
  have hpre : phiH ≫
      (MonoidalActionCategory.Hom.mk (denominatorLeftRaw V r) : B ⟶ D) =
      (MonoidalActionCategory.Hom.mk h : A ⟶ D) :=
    rawPreOrdinary_represent (a := A) (b := B) (c := D) phi (denominatorLeftRaw V r)
  have hcompose : (MonoidalActionCategory.Hom.mk h : A ⟶ D) ≫ sH =
      (MonoidalActionCategory.Hom.mk (collapseComposedInnerRaw U V r s) : A ⟶ Cc) :=
    (MonoidalActionCategory.Hom.mk_comp h s).trans
      (congrArg (fun q : RawHom A Cc => MonoidalActionCategory.Hom.mk q) hh)
  change phiH ≫ rH ≫ sH = _
  exact (Category.assoc phiH rH sH).symm.trans
    ((congrArg (fun q : A ⟶ D => q ≫ sH)
      ((congrArg (fun q : B ⟶ D => phiH ≫ q) hmap).trans hpre)).trans hcompose)

/-- The quotient-level composition law for the original flattened inner arrows.
The associator and translated arrow are the genuine denominator action data. -/
theorem collapseHom_composition (U V : Core C)
    {a b c : localizedRows (C := C) X} {A B P : Core C}
    (f : denominatorLeftObject U a ⟶ b) (g : denominatorLeftObject V b ⟶ c)
    (epsilon : U ⊗ A ⟶ B) (theta : V ⊗ B ⟶ P) :
    collapseHom (V ⊗ U)
        ((denominatorAssocComponent V U a).hom ≫ (denominatorLeftFunctor V).map f ≫ g)
        (collapseComposedEpsilon U V epsilon theta) =
      collapseHom U f epsilon ≫ collapseHom V g theta := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  obtain ⟨s, rfl⟩ := MonoidalActionCategory.Hom.exists_rep g
  let cr : RawHom (collapseObject a A) (collapseObject b B) :=
    collapseRaw (a := a) (b := b) (A := A) (B := B) U r epsilon
  let cs : RawHom (collapseObject b B) (collapseObject c P) :=
    collapseRaw (a := b) (b := c) (A := B) (B := P) V s theta
  let cc : RawHom (collapseObject a A) (collapseObject c P) :=
    collapseRaw (a := a) (b := c) (A := A) (B := P) (V ⊗ U)
      (collapseComposedInnerRaw U V r s) (collapseComposedEpsilon U V epsilon theta)
  have hinner := collapseComposedInner_represent U V r s
  have hcollapse : collapseHom (a := a) (b := c) (A := A) (B := P) (V ⊗ U)
      ((denominatorAssocComponent V U a).hom ≫
        (denominatorLeftFunctor V).map (MonoidalActionCategory.Hom.mk r) ≫
          MonoidalActionCategory.Hom.mk s) (collapseComposedEpsilon U V epsilon theta) =
      collapseHom (a := a) (b := c) (A := A) (B := P) (V ⊗ U)
        (MonoidalActionCategory.Hom.mk (collapseComposedInnerRaw U V r s))
          (collapseComposedEpsilon U V epsilon theta) :=
    congrArg
      (fun q : denominatorLeftObject (V ⊗ U) a ⟶ c =>
        collapseHom (a := a) (b := c) (A := A) (B := P) (V ⊗ U) q
          (collapseComposedEpsilon U V epsilon theta)) hinner
  have hcc : collapseHom (a := a) (b := c) (A := A) (B := P) (V ⊗ U)
      (MonoidalActionCategory.Hom.mk (collapseComposedInnerRaw U V r s))
        (collapseComposedEpsilon U V epsilon theta) =
      (MonoidalActionCategory.Hom.mk cc : collapseObject a A ⟶ collapseObject c P) :=
    collapseHom_mk (a := a) (b := c) (A := A) (B := P) (V ⊗ U)
      (collapseComposedInnerRaw U V r s) (collapseComposedEpsilon U V epsilon theta)
  have hrel : (MonoidalActionCategory.Hom.mk cc :
      collapseObject a A ⟶ collapseObject c P) =
      (MonoidalActionCategory.Hom.mk (cr.comp cs) :
        collapseObject a A ⟶ collapseObject c P) :=
    _root_.Quotient.sound
      (collapseRaw_composition_rel (a := a) (b := b) (c := c) (A := A) (B := B) (P := P)
        U V r s epsilon theta)
  have hU : (collapseHom (a := a) (b := b) (A := A) (B := B) U
      (MonoidalActionCategory.Hom.mk r) epsilon : collapseObject a A ⟶ collapseObject b B) =
      (MonoidalActionCategory.Hom.mk cr : collapseObject a A ⟶ collapseObject b B) :=
    collapseHom_mk (a := a) (b := b) (A := A) (B := B) U r epsilon
  have hV : (collapseHom (a := b) (b := c) (A := B) (B := P) V
      (MonoidalActionCategory.Hom.mk s) theta : collapseObject b B ⟶ collapseObject c P) =
      (MonoidalActionCategory.Hom.mk cs : collapseObject b B ⟶ collapseObject c P) :=
    collapseHom_mk (a := b) (b := c) (A := B) (B := P) V s theta
  have hcompose : (MonoidalActionCategory.Hom.mk (cr.comp cs) :
      collapseObject a A ⟶ collapseObject c P) =
      collapseHom (a := a) (b := b) (A := A) (B := B) U
        (MonoidalActionCategory.Hom.mk r) epsilon ≫
          collapseHom (a := b) (b := c) (A := B) (B := P) V
            (MonoidalActionCategory.Hom.mk s) theta :=
    (MonoidalActionCategory.Hom.mk_comp cr cs).symm.trans
      (congrArg₂
        (fun (q : collapseObject a A ⟶ collapseObject b B)
            (t : collapseObject b B ⟶ collapseObject c P) => q ≫ t) hU.symm hV.symm)
  exact hcollapse.trans (hcc.trans (hrel.trans hcompose))

/-- The actual completed quotient map preserves every composition,
by the alpha.hom/translated-inner-map formula of the genuine denominator action. -/
theorem collapseIteratedHom_comp
    {a b c : iteratedLocalizedRows (C := C) (X := X)} (f : a ⟶ b) (g : b ⟶ c) :
    collapseIteratedHom (f ≫ g) = collapseIteratedHom f ≫ collapseIteratedHom g := by
  refine _root_.Quotient.inductionOn₂ f g ?_
  intro r s
  change collapseHom (s.stabilizer ⊗ r.stabilizer)
      ((denominatorAssocComponent s.stabilizer r.stabilizer a.of.1).hom ≫
        (denominatorLeftFunctor s.stabilizer).map r.hom.1 ≫ s.hom.1)
      ((α_ s.stabilizer r.stabilizer a.of.2).hom ≫ s.stabilizer ◁ r.hom.2 ≫ s.hom.2) =
    collapseHom r.stabilizer r.hom.1 r.hom.2 ≫
      collapseHom s.stabilizer s.hom.1 s.hom.2
  simpa only [collapseComposedEpsilon, Category.assoc] using
    collapseHom_composition r.stabilizer s.stabilizer r.hom.1 s.hom.1 r.hom.2 s.hom.2

/-- Gamma is the canonical collapse functor from the completed iterated category.
Its object, two quotient stages, unit and composition are all the derived maps above. -/
def collapseFunctor : iteratedLocalizedRows (C := C) (X := X) ⥤
    localizedRows (C := C) X where
  obj := collapseIteratedObject
  map := collapseIteratedHom
  map_id := collapseIteratedHom_id
  map_comp := collapseIteratedHom_comp

/-- The original positive inclusion followed by Gamma is naturally Id_V.
The component is the actual row zero-unitor at each unchanged inner denominator. -/
def collapseInclusionNatIso :
    SInverse.inclusion (Core C) (localizedRows (C := C) X) ⋙ collapseFunctor ≅
      𝟭 (localizedRows (C := C) X) :=
  NatIso.ofComponents collapseUnitObjectIso (by
    intro a b f
    have hunit : collapseOuterUnitHom f ≫ (collapseUnitObjectIso b).hom =
        (collapseUnitObjectIso a).hom ≫ f :=
      (collapseOuterUnitNatIso (C := C) (X := X)).hom.naturality f
    have hmap := collapseIteratedHom_inclusion f
    change collapseIteratedHom
        ((SInverse.inclusion (Core C) (localizedRows (C := C) X)).map f) ≫
        (collapseUnitObjectIso b).hom = (collapseUnitObjectIso a).hom ≫ f
    exact (congrArg
      (fun q : collapseObject a (𝟙_ (Core C)) ⟶ collapseObject b (𝟙_ (Core C)) =>
        q ≫ (collapseUnitObjectIso b).hom) hmap).trans hunit)

/-- The completed fibre model keeps the original positive-first (A,D) coordinates.
It inserts the chosen original row E and changes neither coordinate of K. -/
def completedFiberObject (E : FixedTargetExtension C X)
    (a : SInverse (Core C) (Core C)) : iteratedLocalizedRows (C := C) (X := X) :=
  ⟨((⟨(E, a.of.2)⟩ : localizedRows (C := C) X), a.of.1)⟩

/-- The completed fibre raw map has outer U/epsilon and ordinary inner delta.
The inner row remains Id_E; epsilon is the FIRST coordinate of the original K raw arrow. -/
def completedFiberRaw (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    RawHom (completedFiberObject E a) (completedFiberObject E b) where
  stabilizer := r.stabilizer
  hom :=
    ((MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map
      (X := (E, r.stabilizer ⊗ a.of.2)) (Y := (E, b.of.2)) (𝟙 E, r.hom.2),
      r.hom.1)

private theorem completedFiberRaw_rel (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} {r s : RawHom a b} (h : r.Rel s) :
    (completedFiberRaw E r).Rel (completedFiberRaw E s) := by
  obtain ⟨e, he⟩ := h
  have hp : (e.hom ▷ a.of.1) ≫ s.hom.1 = r.hom.1 :=
    congrArg (fun f : r.stabilizer ⊙ₗ a.of ⟶ b.of => f.1) he
  have hd : (e.hom ▷ a.of.2) ≫ s.hom.2 = r.hom.2 :=
    congrArg (fun f : r.stabilizer ⊙ₗ a.of ⟶ b.of => f.2) he
  refine ⟨e, ?_⟩
  apply Prod.ext
  · let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
    change I.map ((𝟙 E, e.hom ▷ a.of.2) :
        (E, r.stabilizer ⊗ a.of.2) ⟶ (E, s.stabilizer ⊗ a.of.2)) ≫
        I.map ((𝟙 E, s.hom.2) : (E, s.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2)) =
      I.map ((𝟙 E, r.hom.2) : (E, r.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2))
    rw [← Functor.map_comp]
    apply congrArg (fun f : (E, r.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2) => I.map f)
    apply Prod.ext
    · exact Category.id_comp _
    · exact hd
  · exact hp

private theorem completedFiberRaw_id (E : FixedTargetExtension C X)
    (a : SInverse (Core C) (Core C)) :
    completedFiberRaw E (RawHom.id a) = RawHom.id (completedFiberObject E a) := rfl

private theorem completedFiberRaw_comp (E : FixedTargetExtension C X)
    {a b c : SInverse (Core C) (Core C)} (r : RawHom a b) (s : RawHom b c) :
    completedFiberRaw E (r.comp s) = (completedFiberRaw E r).comp (completedFiberRaw E s) := by
  apply congrArg (fun h => (⟨s.stabilizer ⊗ r.stabilizer, h⟩ :
    RawHom (completedFiberObject E a) (completedFiberObject E c)))
  apply Prod.ext
  · let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
    let deltaR : r.stabilizer ⊗ a.of.2 ⟶ b.of.2 := r.hom.2
    let deltaS : s.stabilizer ⊗ b.of.2 ⟶ c.of.2 := s.hom.2
    let q0 : (E, (s.stabilizer ⊗ r.stabilizer) ⊗ a.of.2) ⟶
        (E, s.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)) :=
      (𝟙 E, (α_ s.stabilizer r.stabilizer a.of.2).hom)
    let q1 : (E, s.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)) ⟶
        (E, s.stabilizer ⊗ b.of.2) := (𝟙 E, s.stabilizer ◁ deltaR)
    let q2 : (E, s.stabilizer ⊗ b.of.2) ⟶ (E, c.of.2) := (𝟙 E, deltaS)
    let q : (E, (s.stabilizer ⊗ r.stabilizer) ⊗ a.of.2) ⟶ (E, c.of.2) :=
      (𝟙 E, (α_ s.stabilizer r.stabilizer a.of.2).hom ≫ s.stabilizer ◁ deltaR ≫ deltaS)
    let d : (E, r.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2) := (𝟙 E, deltaR)
    let t : I.obj (E, s.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)) ⟶
        I.obj (E, s.stabilizer ⊗ b.of.2) :=
      (denominatorLeftFunctor s.stabilizer).map (I.map d)
    have htranslate : t = I.map q1 :=
      denominatorLeftFunctor_map_inclusion s.stabilizer (𝟙 E) deltaR
    have hq : q0 ≫ q1 ≫ q2 = q := by
      apply Prod.ext
      · dsimp only [q0, q1, q2, q]
        change 𝟙 E ≫ 𝟙 E ≫ 𝟙 E = 𝟙 E
        exact (Category.id_comp (𝟙 E ≫ 𝟙 E)).trans (Category.id_comp (𝟙 E))
      · rfl
    have hmap : I.map q = I.map q0 ≫ I.map q1 ≫ I.map q2 :=
      (congrArg
        (fun k : (E, (s.stabilizer ⊗ r.stabilizer) ⊗ a.of.2) ⟶ (E, c.of.2) =>
          I.map k) hq.symm).trans
            ((I.map_comp q0 (q1 ≫ q2)).trans
              (congrArg
                (fun k : I.obj (E, s.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)) ⟶
                    I.obj (E, c.of.2) => I.map q0 ≫ k) (I.map_comp q1 q2)))
    change I.map q = I.map q0 ≫ t ≫ I.map q2
    exact hmap.trans
      (congrArg
        (fun k : I.obj (E, s.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)) ⟶
            I.obj (E, s.stabilizer ⊗ b.of.2) => I.map q0 ≫ k ≫ I.map q2)
        htranslate.symm)
  · rfl

/-- J_E is the literal completed fibre inclusion, with positive A and denominator D.
Its object and raw morphisms are derived above from the original K=SInverseS presentation. -/
def completedFiberFunctor (E : FixedTargetExtension C X) :
    SInverse (Core C) (Core C) ⥤ iteratedLocalizedRows (C := C) (X := X) where
  obj := completedFiberObject E
  map f := Quotient.map (completedFiberRaw E)
    (by intro r s h; exact completedFiberRaw_rel E h) f
  map_id a := by
    exact congrArg MonoidalActionCategory.Hom.mk (completedFiberRaw_id E a)
  map_comp f g := by
    refine _root_.Quotient.inductionOn₂ f g ?_
    intro r s
    exact congrArg MonoidalActionCategory.Hom.mk (completedFiberRaw_comp E r s)

/-- The full original K representative maps to outer U and inner ordinary delta. -/
theorem completedFiberFunctor_map_mk (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (completedFiberFunctor E).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (completedFiberRaw E r) := rfl

/-- Gamma followed on J_E has the actual positive row A□E and the original denominator D. -/
theorem collapse_completedFiber_object (E : FixedTargetExtension C X)
    (a : SInverse (Core C) (Core C)) :
    (collapseFunctor.obj ((completedFiberFunctor E).obj a)).of =
      (leftSumObj a.of.1 E, a.of.2) := rfl

/-- The full Gamma-J representative retains U, epsilon and delta.
Its extra inner unit is explicitly kept until the left-unitor relation is applied. -/
theorem collapse_completedFiber_map_mk (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (collapseFunctor.map ((completedFiberFunctor E).map (MonoidalActionCategory.Hom.mk r))) =
      MonoidalActionCategory.Hom.mk
        (collapseRaw r.stabilizer
          (RawHom.ofMap (S := Core C)
            ((𝟙 E, r.hom.2) : (E, r.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2)))
          r.hom.1) := rfl

/-! ## Collapse on the unit row and the split-row functor

The collapse of the unit row is identified with the split row by the right unitor on its kernel.
This comparison gives a natural isomorphism to the original split-row functor and retains the
positive object and denominator in their original order. -/

/-- Collapse adds A to the literal 0→X→X row. This given row Iso removes only
its kernel A⊞0 by the right unitor, keeping the actual middle A⊞X and quotient X. -/
def collapseUnitSplitRowIso (A : Core C) :
    leftSumObj A (AlgebraicKTheory.AuxiliaryExtension.unitRow X) ≅
      SplitInclusion.splitRow X A :=
  pairIso
    { a := (ρ_ A).hom.iso
      b := Iso.refl (A.of ⊞ X)
      comm_i := by
        change biprod.map (𝟙 A.of) (0 : (0 : C) ⟶ X) ≫ 𝟙 (A.of ⊞ X) =
          (ρ_ A).hom.iso.hom ≫ (biprod.inl : A.of ⟶ A.of ⊞ X)
        have hUnitor : (show A.of ⊞ (0 : C) ⟶ A.of from (ρ_ A).hom.iso.hom) =
            (biprod.fst : A.of ⊞ (0 : C) ⟶ A.of) := coreRightUnitor_hom A
        have hNative : biprod.map (𝟙 A.of) (0 : (0 : C) ⟶ X) =
            (biprod.fst : A.of ⊞ (0 : C) ⟶ A.of) ≫ biprod.inl := by
          apply biprod.hom_ext'
          · simp
          · exact (isZero_zero C).eq_of_src _ _
        exact (Category.comp_id _).trans
          (hNative.trans (congrArg
            (fun q : A.of ⊞ (0 : C) ⟶ A.of => q ≫ biprod.inl) hUnitor).symm)
      comm_p := by
        change 𝟙 (A.of ⊞ X) ≫ (biprod.snd : A.of ⊞ X ⟶ X) =
          (biprod.snd : A.of ⊞ X ⟶ X) ≫ 𝟙 X
        rw [Category.id_comp, Category.comp_id] }

/-- The same comparison preserves the entire original middle arrow by Id_(A⊞X). -/
theorem collapseUnitSplitRowIso_middle (A : Core C) :
    (collapseUnitSplitRowIso (C := C) (X := X) A).hom.b.hom = 𝟙 (A.of ⊞ X) := rfl

/-- The Gamma-J object comparison has the actual split row and SAME denominator D.
There is no interchange of the positive-first A,D coordinates. -/
def collapseFiberEtaComponent (a : SInverse (Core C) (Core C)) :
    (completedFiberFunctor (AlgebraicKTheory.AuxiliaryExtension.unitRow X) ⋙
      collapseFunctor).obj a ≅ (SplitInclusion.splitLocalizedFunctor X).obj a :=
  (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).mapIso
    ((collapseUnitSplitRowIso (C := C) (X := X) a.of.1).prod (Iso.refl a.of.2))

omit [ExactCategory C] in
private theorem nativeCollapseEta (U A B Z : C) (epsilon : U ⊞ A ⟶ B) :
    biprod.map (biprod.snd : (0 : C) ⊞ U ⟶ U) (𝟙 (A ⊞ Z)) ≫
        (biprod.associator U A Z).inv ≫ biprod.map epsilon (𝟙 Z) =
      (nativeCollapseInterchange (0 : C) U A Z).hom ≫
        biprod.map epsilon (biprod.snd : (0 : C) ⊞ Z ⟶ Z) := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    · exact (isZero_zero C).eq_of_src _ _
    · simp [nativeCollapseInterchange, SInverseS.biprodInterchangeIso,
        biprod.associator, biprod.braiding, biprod.lift_eq, biprod.desc_eq,
        biprod.map_eq, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
  · apply biprod.hom_ext' <;>
      simp [nativeCollapseInterchange, SInverseS.biprodInterchangeIso,
        biprod.associator, biprod.braiding, biprod.lift_eq, biprod.desc_eq,
        biprod.map_eq, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

private theorem collapseFiberEta_raw_rel
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    let E := AlgebraicKTheory.AuxiliaryExtension.unitRow X
    let va : localizedRows (C := C) X := ⟨(E, a.of.2)⟩
    let vb : localizedRows (C := C) X := ⟨(E, b.of.2)⟩
    let ga := collapseObject va a.of.1
    let gb := collapseObject vb b.of.1
    let sa := SplitInclusion.splitLocalizedObject X a
    let sb := SplitInclusion.splitLocalizedObject X b
    let phiA : ga.of ⟶ sa.of :=
      ((collapseUnitSplitRowIso (C := C) (X := X) a.of.1).hom, 𝟙 a.of.2)
    let phiB : gb.of ⟶ sb.of :=
      ((collapseUnitSplitRowIso (C := C) (X := X) b.of.1).hom, 𝟙 b.of.2)
    let inner : RawHom (denominatorLeftObject r.stabilizer va) vb :=
      RawHom.ofMap (S := Core C)
        ((𝟙 E, r.hom.2) : (E, r.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2))
    let k : RawHom ga gb := collapseRaw (a := va) (b := vb)
      (A := a.of.1) (B := b.of.1) r.stabilizer inner r.hom.1
    (⟨k.stabilizer, k.hom ≫ phiB⟩ : RawHom ga sb).Rel
      (⟨r.stabilizer,
        CategoryTheory.MonoidalCategory.MonoidalLeftActionStruct.actionHomRight
          r.stabilizer (d := ga.of) (d' := sa.of) phiA ≫
            (SplitInclusion.splitLocalizedRaw X r).hom⟩ : RawHom ga sb) := by
  let E := AlgebraicKTheory.AuxiliaryExtension.unitRow X
  have hCoreId (Z : Core C) : (𝟙 Z : Z ⟶ Z).iso.hom = 𝟙 Z.of := rfl
  refine ⟨λ_ r.stabilizer, ?_⟩
  apply Prod.ext
  · change leftSumMap (λ_ r.stabilizer).hom (𝟙 (leftSumObj a.of.1 E)) ≫
        (leftSumMap (𝟙 r.stabilizer) (collapseUnitSplitRowIso (C := C) (X := X) a.of.1).hom ≫
          SplitInclusion.splitNumeratorMap X r.hom.1) =
      ((collapseRowInterchange (𝟙_ (Core C)) r.stabilizer a.of.1 E).hom ≫
        leftSumMap r.hom.1 ((leftSumUnitIso E).hom ≫ 𝟙 E)) ≫
        (collapseUnitSplitRowIso (C := C) (X := X) b.of.1).hom
    rewrite [Category.comp_id]
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [AlgebraicKTheory.FixedTargetExtension.comp_b, Iso.trans_hom,
      leftSumMap_b_hom, collapseRowInterchange_middle,
      collapseUnitSplitRowIso_middle, SplitInclusion.splitNumeratorMap_b,
      leftSumUnitIso_b_hom, coreLeftUnitor_hom, coreBiprodTensorUnit_of, Category.assoc]
    have hRowId : (𝟙 (leftSumObj a.of.1 E) : _ ⟶ _).b.hom =
        𝟙 (a.of.1.of ⊞ X) := rfl
    have hEtaMiddle :
        (leftSumMap (𝟙 r.stabilizer)
          (collapseUnitSplitRowIso (C := C) (X := X) a.of.1).hom).b.hom =
          𝟙 (r.stabilizer.of ⊞ (a.of.1.of ⊞ X)) := by
      have hMap := leftSumMap_b_hom (𝟙 r.stabilizer)
        (collapseUnitSplitRowIso (C := C) (X := X) a.of.1).hom
      have hA := collapseUnitSplitRowIso_middle (C := C) (X := X) a.of.1
      exact hMap.trans
        ((congrArg₂
          (fun (f : r.stabilizer.of ⟶ r.stabilizer.of)
              (g : a.of.1.of ⊞ X ⟶ a.of.1.of ⊞ X) => biprod.map f g)
          (hCoreId r.stabilizer) hA).trans
            (nativeBiprodMap_id r.stabilizer.of (a.of.1.of ⊞ X)))
    have hSplit :
        ((leftSumMap (𝟙 r.stabilizer)
            (collapseUnitSplitRowIso (C := C) (X := X) a.of.1).hom).b ≪≫
          SplitInclusion.splitMiddleIso X r.hom.1).hom =
            (biprod.associator r.stabilizer.of a.of.1.of X).inv ≫
              biprod.map r.hom.1.iso.hom (𝟙 X) := by
      change (leftSumMap (𝟙 r.stabilizer)
          (collapseUnitSplitRowIso (C := C) (X := X) a.of.1).hom).b.hom ≫
            (SplitInclusion.splitMiddleIso X r.hom.1).hom = _
      exact (congrArg
        (fun f : r.stabilizer.of ⊞ (a.of.1.of ⊞ X) ⟶
            r.stabilizer.of ⊞ (a.of.1.of ⊞ X) =>
          f ≫ (SplitInclusion.splitMiddleIso X r.hom.1).hom) hEtaMiddle).trans
            ((Category.id_comp _).trans (SplitInclusion.splitMiddleIso_hom X r.hom.1))
    change biprod.map (biprod.snd : (0 : C) ⊞ r.stabilizer.of ⟶ r.stabilizer.of)
        (𝟙 (leftSumObj a.of.1 E) : _ ⟶ _).b.hom ≫
        ((leftSumMap (𝟙 r.stabilizer)
            (collapseUnitSplitRowIso (C := C) (X := X) a.of.1).hom).b ≪≫
          SplitInclusion.splitMiddleIso X r.hom.1).hom =
      (nativeCollapseInterchange (0 : C) r.stabilizer.of a.of.1.of X).hom ≫
        biprod.map r.hom.1.iso.hom (biprod.snd : (0 : C) ⊞ X ⟶ X) ≫
          𝟙 (b.of.1.of ⊞ X)
    have hLeft := congrArg₂
      (fun (f : ((0 : C) ⊞ r.stabilizer.of) ⊞ (a.of.1.of ⊞ X) ⟶
            r.stabilizer.of ⊞ (a.of.1.of ⊞ X))
          (g : r.stabilizer.of ⊞ (a.of.1.of ⊞ X) ⟶ b.of.1.of ⊞ X) => f ≫ g)
      (congrArg
        (fun g : a.of.1.of ⊞ X ⟶ a.of.1.of ⊞ X =>
          biprod.map (biprod.snd : (0 : C) ⊞ r.stabilizer.of ⟶ r.stabilizer.of) g)
        hRowId) hSplit
    have hNative := nativeCollapseEta r.stabilizer.of a.of.1.of b.of.1.of X r.hom.1.iso.hom
    have hPost := congrArg
      (fun q : (r.stabilizer.of ⊞ a.of.1.of) ⊞ ((0 : C) ⊞ X) ⟶ b.of.1.of ⊞ X =>
        (nativeCollapseInterchange (0 : C) r.stabilizer.of a.of.1.of X).hom ≫ q)
      (Category.comp_id (biprod.map r.hom.1.iso.hom
        (biprod.snd : (0 : C) ⊞ X ⟶ X))).symm
    exact hLeft.trans (hNative.trans hPost)
  · change ((λ_ r.stabilizer).hom ▷ a.of.2) ≫
        (r.stabilizer ◁ 𝟙 a.of.2 ≫ r.hom.2) =
      ((α_ (𝟙_ (Core C)) r.stabilizer a.of.2).hom ≫
        ((λ_ (r.stabilizer ⊗ a.of.2)).hom ≫ r.hom.2)) ≫ 𝟙 b.of.2
    rw [whiskerLeft_id, Category.id_comp, Category.comp_id]
    have hu : (α_ (𝟙_ (Core C)) r.stabilizer a.of.2).hom ≫
        (λ_ (r.stabilizer ⊗ a.of.2)).hom = (λ_ r.stabilizer).hom ▷ a.of.2 := by
      rw [leftUnitor_tensor_hom r.stabilizer a.of.2, Iso.hom_inv_id_assoc]
    simpa only [Category.assoc] using
      (congrArg (fun f => f ≫ r.hom.2) hu).symm


/-- The original fibre inclusion J at the literal unit row satisfies Gamma J ≅ eta.
Every original epsilon/delta representative is compared using the actual lambda_U;
there is no eta weakness, splitting choice or action-invertibility premise. -/
def collapseFiberEtaNatIso :
    completedFiberFunctor (AlgebraicKTheory.AuxiliaryExtension.unitRow X) ⋙
        collapseFunctor ≅ SplitInclusion.splitLocalizedFunctor X :=
  let E := AlgebraicKTheory.AuxiliaryExtension.unitRow X
  let F : SInverse (Core C) (Core C) ⥤ localizedRows (C := C) X :=
    completedFiberFunctor E ⋙ collapseFunctor
  let G : SInverse (Core C) (Core C) ⥤ localizedRows (C := C) X :=
    SplitInclusion.splitLocalizedFunctor X
  NatIso.ofComponents (F := F) (G := G)
    (fun (a : SInverse (Core C) (Core C)) => collapseFiberEtaComponent (C := C) (X := X) a)
    (by
      intro a b f
      obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
      let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
      let va : localizedRows (C := C) X := ⟨(E, a.of.2)⟩
      let vb : localizedRows (C := C) X := ⟨(E, b.of.2)⟩
      let ga := collapseObject va a.of.1
      let gb := collapseObject vb b.of.1
      let sa := SplitInclusion.splitLocalizedObject X a
      let sb := SplitInclusion.splitLocalizedObject X b
      let phiA : ga.of ⟶ sa.of :=
        ((collapseUnitSplitRowIso (C := C) (X := X) a.of.1).hom, 𝟙 a.of.2)
      let phiB : gb.of ⟶ sb.of :=
        ((collapseUnitSplitRowIso (C := C) (X := X) b.of.1).hom, 𝟙 b.of.2)
      let inner : RawHom (denominatorLeftObject r.stabilizer va) vb :=
        RawHom.ofMap (S := Core C)
          ((𝟙 E, r.hom.2) : (E, r.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2))
      let k : RawHom ga gb := collapseRaw (a := va) (b := vb)
        (A := a.of.1) (B := b.of.1) r.stabilizer inner r.hom.1
      let s : RawHom sa sb := SplitInclusion.splitLocalizedRaw X r
      have hF : F.map (MonoidalActionCategory.Hom.mk r) = MonoidalActionCategory.Hom.mk k :=
        collapse_completedFiber_map_mk E r
      have hG : G.map (MonoidalActionCategory.Hom.mk r) = MonoidalActionCategory.Hom.mk s :=
        SplitInclusion.splitLocalizedFunctor_map_mk X r
      have hA : (collapseFiberEtaComponent (C := C) (X := X) a).hom = I.map phiA := rfl
      have hB : (collapseFiberEtaComponent (C := C) (X := X) b).hom = I.map phiB := rfl
      have hPost : MonoidalActionCategory.Hom.mk k ≫ I.map phiB =
          MonoidalActionCategory.Hom.mk (⟨k.stabilizer, k.hom ≫ phiB⟩ : RawHom ga sb) :=
        rawPostOrdinary_represent (a := ga) (b := gb) (c := sb) k phiB
      have hPre : I.map phiA ≫ MonoidalActionCategory.Hom.mk s =
          MonoidalActionCategory.Hom.mk
            (⟨s.stabilizer, s.stabilizer ⊴ₗ phiA ≫ s.hom⟩ : RawHom ga sb) :=
        rawPreOrdinary_represent (a := ga) (b := sa) (c := sb) phiA s
      have hLeft := congrArg₂ (fun (q : ga ⟶ gb) (h : gb ⟶ sb) => q ≫ h) hF hB
      have hRight := congrArg₂ (fun (h : ga ⟶ sa) (q : sa ⟶ sb) => h ≫ q) hA hG
      exact hLeft.trans
        (hPost.trans ((_root_.Quotient.sound (collapseFiberEta_raw_rel r)).trans
          (hPre.symm.trans hRight.symm))))

end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- The completed inclusion has the literal original row E as pi_N object image. -/
theorem completedFiber_projection_obj (E : FixedTargetExtension C X)
    (a : SInverse (Core C) (Core C)) :
    iteratedRowProjectionFunctor.obj ((completedFiberFunctor E).obj a) =
      (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) := rfl

/-- Both original K coordinates are retained, but pi_N discards them on the fibre.
The ordinary inner row Id_E gives exactly the base identity for each quotient arrow. -/
theorem completedFiber_projection_map (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    iteratedRowProjectionFunctor.map ((completedFiberFunctor E).map f) =
      (𝟙 (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X))) := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  let ja := completedFiberObject E a
  let jb := completedFiberObject E b
  have hMap := iteratedRowProjectionFunctor_map_mk
    (a := ja) (b := jb) (completedFiberRaw E r)
  change iteratedRowProjectionFunctor.map (X := ja) (Y := jb)
      (MonoidalActionCategory.Hom.mk (completedFiberRaw E r)) = _
  apply hMap.trans
  change forgetDenominatorFunctor.map
      ((MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map
        (X := (E, r.stabilizer ⊗ a.of.2)) (Y := (E, b.of.2)) (𝟙 E, r.hom.2)) = _
  exact (forgetDenominatorFunctor_map_inclusion (𝟙 E) r.hom.2).trans
    ((MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X)).map_id E)

/-- The complete ordinary natural comparison of pi_N J_E with the actual constant row. -/
def completedFiberProjectionIso (E : FixedTargetExtension C X) :
    completedFiberFunctor E ⋙ iteratedRowProjectionFunctor ≅
      (Functor.const (SInverse (Core C) (Core C))).obj
        (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change iteratedRowProjectionFunctor.map ((completedFiberFunctor E).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ 𝟙 _
    rw [completedFiber_projection_map]
    simp only [completedFiber_projection_obj, Category.comp_id])

/-- The identity-component comparison gives the exact constant-functor equality,
without a supplied projection or fibre witness. -/
theorem completedFiberProjection_eq_const (E : FixedTargetExtension C X) :
    completedFiberFunctor E ⋙ iteratedRowProjectionFunctor =
      (Functor.const (SInverse (Core C) (Core C))).obj
        (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :=
  Functor.ext_of_iso (completedFiberProjectionIso E) (fun _ => rfl)

/-- J_E as an actual functor into the original strict pi_N fibre.
This is the stock induced functor using the derived full constant equality. -/
def completedFiberStrictFunctor (E : FixedTargetExtension C X) :
    SInverse (Core C) (Core C) ⥤
      Functor.Fiber (iteratedRowProjectionFunctor (C := C) (X := X))
        (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :=
  Functor.Fiber.inducedFunctor (completedFiberProjection_eq_const E)

/-- The strict-fibre functor includes back as the exact completed J_E. -/
theorem completedFiberStrictFunctor_inclusion (E : FixedTargetExtension C X) :
    completedFiberStrictFunctor E ⋙ Functor.Fiber.fiberInclusion = completedFiberFunctor E :=
  Functor.Fiber.inducedFunctor_comp (completedFiberProjection_eq_const E)

end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end

/-!
The actual completed pair category is the strict fibre of the literal pi_N.
This fragment follows the derived relative-Hom source, Gamma's original J_E,
and the stock strict-fibre embedding. It does not assume a fibre equivalence,
a row splitting, an eta equivalence or any weak/homotopy equivalence.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- The original base identity is represented by its actual action unitor. -/
def completedFiberUnitBase (E : FixedTargetExtension C X) :
    RawHom (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) ⟨E⟩ :=
  RawHom.id ⟨E⟩

/-- The relative coefficient at the unit base is identified with the original K object
by lambda_D, preserving the positive coordinate A literally. -/
def completedFiberUnitCoefficientIso (E : FixedTargetExtension C X)
    (a : SInverse (Core C) (Core C)) :
    relativeCoefficientSource (completedFiberUnitBase E).stabilizer
        ((completedFiberFunctor E).obj a) ≅ a :=
  (MonoidalActionCategory.inclusion (Core C) (Core C × Core C)).mapIso
    ((Iso.refl a.of.1).prod (λ_ a.of.2))

/-- The unit-source coefficient representative retains U/epsilon and precomposes delta
only by U acting on the actual lambda_D. -/
def completedFiberUnitPreRaw (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    RawHom
      (relativeCoefficientSource (completedFiberUnitBase E).stabilizer
        ((completedFiberFunctor E).obj a)) b where
  stabilizer := r.stabilizer
  hom := (r.hom.1, r.stabilizer ◁ (λ_ a.of.2).hom ≫ r.hom.2)

omit [ExactCategory C] in
private theorem interchange_unit_hom (U D : Core C) :
    (denominatorInterchangeIso U (𝟙_ (Core C)) D).hom ≫ U ◁ (λ_ D).hom =
      (λ_ (U ⊗ D)).hom := by
  apply Core.hom_ext
  have h := swap_zero_unit_hom U.of D.of
  simpa only [coreCategory_comp_iso, Iso.trans_hom, denominatorInterchangeIso_hom,
    core_left_hom, core_left_unitor_hom, coreBiprodTensorUnit_of,
    coreBiprodTensorObj_of] using h

/-- The actual ordinary coefficient source Iso has this whole original raw representative. -/
theorem completedFiberUnitCoefficientIso_precompose_mk (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (completedFiberUnitCoefficientIso E a).hom ≫ MonoidalActionCategory.Hom.mk r =
      MonoidalActionCategory.Hom.mk (completedFiberUnitPreRaw E r) := by
  let unitMap :
      (relativeCoefficientSource (completedFiberUnitBase E).stabilizer
        ((completedFiberFunctor E).obj a)).of ⟶ a.of :=
    (𝟙 a.of.1, (λ_ a.of.2).hom)
  have hRaw : (⟨r.stabilizer, r.stabilizer ⊴ₗ unitMap ≫ r.hom⟩ :
      RawHom
        (relativeCoefficientSource (completedFiberUnitBase E).stabilizer
          ((completedFiberFunctor E).obj a)) b) = completedFiberUnitPreRaw E r := by
    apply congrArg
      (fun h : r.stabilizer ⊙ₗ
        (relativeCoefficientSource (completedFiberUnitBase E).stabilizer
          ((completedFiberFunctor E).obj a)).of ⟶ b.of =>
          (⟨r.stabilizer, h⟩ : RawHom
            (relativeCoefficientSource (completedFiberUnitBase E).stabilizer
              ((completedFiberFunctor E).obj a)) b))
    apply Prod.ext
    · change r.stabilizer ◁ 𝟙 a.of.1 ≫ r.hom.1 = r.hom.1
      rw [whiskerLeft_id, Category.id_comp]
    · rfl
  change MonoidalActionCategory.Hom.mk ((RawHom.ofMap (S := Core C) unitMap).comp r) =
    MonoidalActionCategory.Hom.mk (completedFiberUnitPreRaw E r)
  exact (_root_.Quotient.sound (rawPreMap_rel unitMap r)).trans
    (congrArg MonoidalActionCategory.Hom.mk hRaw)

/-- At the original unit base, the reconstructed inner arrow is exactly the ordinary
Id_E/delta inclusion. Both source unitors are accounted for by their actual maps. -/
theorem completedFiberUnit_inner (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    relativeReconstructInnerRaw
        (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
        (completedFiberUnitBase E) (completedFiberUnitPreRaw E r) =
      (RawHom.ofMap (S := Core C)
        ((𝟙 E, r.hom.2) : (E, r.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2))) := by
  apply congrArg
    (fun h : (𝟙_ (Core C)) ⊙ₗ (E, r.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2) =>
      (⟨𝟙_ (Core C), h⟩ :
        RawHom (denominatorLeftObject r.stabilizer ((completedFiberFunctor E).obj a).of.1)
          ((completedFiberFunctor E).obj b).of.1))
  apply Prod.ext
  · change (leftSumUnitIso E).hom = (leftSumUnitIso E).hom ≫ 𝟙 E
    exact (Category.comp_id _).symm
  · change (denominatorInterchangeIso r.stabilizer (𝟙_ (Core C)) a.of.2).hom ≫
        (r.stabilizer ◁ (λ_ a.of.2).hom ≫ r.hom.2) =
      (λ_ (r.stabilizer ⊗ a.of.2)).hom ≫ r.hom.2
    exact (Category.assoc
      (denominatorInterchangeIso r.stabilizer (𝟙_ (Core C)) a.of.2).hom
      (r.stabilizer ◁ (λ_ a.of.2).hom) r.hom.2).symm.trans
      (congrArg
        (fun q : (𝟙_ (Core C)) ⊗ (r.stabilizer ⊗ a.of.2) ⟶
          r.stabilizer ⊗ a.of.2 => q ≫ r.hom.2)
        (interchange_unit_hom r.stabilizer a.of.2))

/-- The original J_E map is reconstruction at the unit base after lambda_D transport.
This compares every original epsilon/delta quotient morphism, not only objects. -/
theorem completedFiberMap_asReconstruction (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (completedFiberFunctor E).map f =
      relativeReconstructHom
        (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
        (completedFiberUnitBase E)
        ((completedFiberUnitCoefficientIso E a).hom ≫ f) := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  have hRaw :
      relativeReconstructOuterRaw
        (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
        (completedFiberUnitBase E) (completedFiberUnitPreRaw E r) =
      completedFiberRaw E r := by
    apply congrArg
      (fun h : r.stabilizer ⊙ₗ ((completedFiberFunctor E).obj a).of ⟶
        ((completedFiberFunctor E).obj b).of =>
          (⟨r.stabilizer, h⟩ : RawHom
            ((completedFiberFunctor E).obj a) ((completedFiberFunctor E).obj b)))
    apply Prod.ext
    · change MonoidalActionCategory.Hom.mk
        (relativeReconstructInnerRaw
          (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
          (completedFiberUnitBase E) (completedFiberUnitPreRaw E r)) =
      MonoidalActionCategory.Hom.mk
        (RawHom.ofMap (S := Core C)
          ((𝟙 E, r.hom.2) : (E, r.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2)))
      exact congrArg MonoidalActionCategory.Hom.mk (completedFiberUnit_inner E r)
    · rfl
  have hMap := completedFiberFunctor_map_mk E r
  have hPre := completedFiberUnitCoefficientIso_precompose_mk E r
  have hReconstruct := relativeReconstructHom_mk
    (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
    (completedFiberUnitBase E) (completedFiberUnitPreRaw E r)
  have hTransport := congrArg
    (fun q : relativeCoefficientSource (completedFiberUnitBase E).stabilizer
        ((completedFiberFunctor E).obj a) ⟶ b =>
      relativeReconstructHom
        (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
        (completedFiberUnitBase E) q) hPre.symm
  exact hMap.trans ((congrArg MonoidalActionCategory.Hom.mk hRaw).symm.trans
    (hReconstruct.symm.trans hTransport))

/-- The original strict-fibre inclusion is injective on every Hom set.
Only the genuine coefficient source Iso is cancelled; no global epi assertion is made. -/
theorem completedFiberStrict_map_injective (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} {f g : a ⟶ b}
    (h : (completedFiberStrictFunctor E).map f = (completedFiberStrictFunctor E).map g) :
    f = g := by
  have hN : (completedFiberFunctor E).map f = (completedFiberFunctor E).map g :=
    congrArg
      (fun phi : (completedFiberStrictFunctor E).obj a ⟶
        (completedFiberStrictFunctor E).obj b => phi.val) h
  rw [completedFiberMap_asReconstruction, completedFiberMap_asReconstruction] at hN
  have hCoefficients : (completedFiberUnitCoefficientIso E a).hom ≫ f =
      (completedFiberUnitCoefficientIso E a).hom ≫ g :=
    (show Function.Injective
        (relativeReconstructHom
          (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
          (completedFiberUnitBase E)) from
      relativeReconstructHom_injective
        (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
        (completedFiberUnitBase E)) hN
  exact (cancel_epi (completedFiberUnitCoefficientIso E a).hom).mp hCoefficients

/-- Every original strict-fibre morphism maps to the actual unit base identity. -/
theorem completedFiberStrictHom_projection (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)}
    (phi : (completedFiberStrictFunctor E).obj a ⟶ (completedFiberStrictFunctor E).obj b) :
    iteratedRowProjectionFunctor.map phi.val =
      MonoidalActionCategory.Hom.mk (completedFiberUnitBase E) := by
  let p := iteratedRowProjectionFunctor (C := C) (X := X)
  have hMap : p.map phi.val =
      (𝟙 (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X))) :=
    (@CategoryTheory.IsHomLift.eq_of_isHomLift
      (MonoidalActionCategory (Core C) (FixedTargetExtension C X))
      (iteratedLocalizedRows (C := C) (X := X)) _ _ p
      ((completedFiberFunctor E).obj a) ((completedFiberFunctor E).obj b)
      (𝟙 (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)))
      phi.val phi.property).symm
  exact hMap

/-- The strict-fibre preimage is the actual relative coefficient followed by lambda_D.inv.
Its lifted-identity condition is the ordinary projection theorem proved above. -/
def completedFiberStrictPreimage (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)}
    (phi : (completedFiberStrictFunctor E).obj a ⟶ (completedFiberStrictFunctor E).obj b) :
    a ⟶ b :=
  (completedFiberUnitCoefficientIso E a).inv ≫
    (relativeHomEquiv
      (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
      (completedFiberUnitBase E)).symm
      ⟨phi.val, by exact completedFiberStrictHom_projection E phi⟩

/-- The actual preimage maps back to the original strict-fibre morphism. -/
theorem completedFiberStrict_map_preimage (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)}
    (phi : (completedFiberStrictFunctor E).obj a ⟶ (completedFiberStrictFunctor E).obj b) :
    (completedFiberStrictFunctor E).map (completedFiberStrictPreimage E phi) = phi := by
  apply Functor.Fiber.hom_ext
  change (completedFiberFunctor E).map (completedFiberStrictPreimage E phi) = phi.val
  rw [completedFiberMap_asReconstruction]
  change relativeReconstructHom
      (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
      (completedFiberUnitBase E)
      ((completedFiberUnitCoefficientIso E a).hom ≫
        ((completedFiberUnitCoefficientIso E a).inv ≫
          (relativeHomEquiv
            (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
            (completedFiberUnitBase E)).symm
            ⟨phi.val, completedFiberStrictHom_projection E phi⟩)) = phi.val
  rw [Iso.hom_inv_id_assoc]
  exact congrArg Subtype.val
    ((relativeHomEquiv
      (a := (completedFiberFunctor E).obj a) (b := (completedFiberFunctor E).obj b)
      (completedFiberUnitBase E)).apply_symm_apply
      ⟨phi.val, completedFiberStrictHom_projection E phi⟩)

/-- The other inverse law follows from the derived injectivity and map-preimage identity. -/
theorem completedFiberStrict_preimage_map (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    completedFiberStrictPreimage E ((completedFiberStrictFunctor E).map f) = f := by
  apply completedFiberStrict_map_injective E
  exact completedFiberStrict_map_preimage E ((completedFiberStrictFunctor E).map f)

/-- Fully faithfulness of the original completed inclusion is derived from both inverse laws. -/
def completedFiberStrictFullyFaithful (E : FixedTargetExtension C X) :
    (completedFiberStrictFunctor E).FullyFaithful where
  preimage phi := completedFiberStrictPreimage E phi
  map_preimage phi := by exact completedFiberStrict_map_preimage E phi
  preimage_map f := by exact completedFiberStrict_preimage_map E f

/-- Every strict-fibre object has its original positive A and denominator D as a preimage.
Only the fibre's given row equality is used; no row isomorphism or splitting is supplied. -/
theorem completedFiberStrict_essSurj (E : FixedTargetExtension C X) :
    (completedFiberStrictFunctor E).EssSurj := by
  constructor
  intro b
  let k : SInverse (Core C) (Core C) := ⟨(b.val.of.2, b.val.of.1.of.2)⟩
  have hRow : b.val.of.1.of.1 = E :=
    congrArg
      (fun q : MonoidalActionCategory (Core C) (FixedTargetExtension C X) => q.of) b.property
  have hObj : ((completedFiberStrictFunctor E).obj k).val = b.val :=
    congrArg
      (fun row : FixedTargetExtension C X =>
        (⟨((⟨(row, b.val.of.1.of.2)⟩ : localizedRows (C := C) X), b.val.of.2)⟩ :
          iteratedLocalizedRows (C := C) (X := X))) hRow.symm
  have hFiber : (completedFiberStrictFunctor E).obj k = b := Subtype.ext hObj
  exact ⟨k, ⟨eqToIso hFiber⟩⟩

/-- The original strict-fibre inclusion is an equivalence, with all three conditions derived. -/
theorem completedFiberStrict_isEquivalence (E : FixedTargetExtension C X) :
    (completedFiberStrictFunctor E).IsEquivalence :=
  { full := (completedFiberStrictFullyFaithful E).full
    faithful := (completedFiberStrictFullyFaithful E).faithful
    essSurj := completedFiberStrict_essSurj E }

/-- The same original K is equivalent to the literal strict pi_N fibre at E.
Its forward functor is exactly J_E with the stock strict-fibre factorization. -/
def completedFiberEquivalence (E : FixedTargetExtension C X) :
    SInverse (Core C) (Core C) ≌
      Functor.Fiber (iteratedRowProjectionFunctor (C := C) (X := X))
        (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) := by
  letI : (completedFiberStrictFunctor E).IsEquivalence := completedFiberStrict_isEquivalence E
  exact (completedFiberStrictFunctor E).asEquivalence

/-- The forward equivalence map is the original strict-fibre inclusion, not a new model. -/
theorem completedFiberEquivalence_functor (E : FixedTargetExtension C X) :
    (completedFiberEquivalence E).functor = completedFiberStrictFunctor E := rfl

end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end


/-!
Actual identity-composite homotopies for the original Gamma/I/J/kappa diagram.
This fragment follows current Gamma, the literal up-universe nerve map, and
the original SplitRowInclusion kernel projection. It supplies the full
simplicial section/kernel homotopies used
by the conditional split-comparison lemma. It assumes no J or eta weakness.
-/



noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- The actual original kernel composite of Gamma J is naturally Id_K.
Gamma J is first compared to literal eta, then the original eta-kappa Iso is applied. -/
def collapseFiberKernelNatIso :
    completedFiberFunctor (AlgebraicKTheory.AuxiliaryExtension.unitRow X) ⋙ collapseFunctor ⋙
        localizedKernelFunctor X ≅ 𝟭 (SInverse (Core C) (Core C)) :=
  Functor.isoWhiskerRight collapseFiberEtaNatIso (localizedKernelFunctor X) ≪≫
    SplitInclusion.splitLocalizedKernelIso X

/-- Gamma I supplies the actual section homotopy on the WHOLE ordinary V nerve. -/
def collapseInclusionNerveHomotopy :
    SSet.Homotopy
      (nerveMap (SInverse.inclusion (Core C) (localizedRows (C := C) X)) ≫
        nerveMap (collapseFunctor (C := C) (X := X)))
      (𝟙 (nerve (localizedRows (C := C) X) : SSet.{max u v})) := by
  rw [nerveMap_comp, ← nerveMap_id]
  exact NatTrans.nerveHomotopy collapseInclusionNatIso.hom

/-- The original kappa Gamma J identity has its full native-nerve homotopy.
J uses the literal up map, Gamma the ordinary map, and kappa the original down map.
Positive-first A,D and literal givenX are retained; no homotopy-group result is assumed. -/
def collapseFiberKernelNerveHomotopy :
    SSet.Homotopy
      (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberFunctor
        (AlgebraicKTheory.AuxiliaryExtension.unitRow X)) ≫
        nerveMap (collapseFunctor (C := C) (X := X)) ≫
          nerveMapCommonHom.{u, max u v, 0} (localizedKernelFunctor X))
      (𝟙 (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})) := by
  rw [nerveMap_nerveMapCommonHom_comp, nerveMapCommonHomUp_comp, ← nerveMap_id]
  exact NatTrans.nerveHomotopy collapseFiberKernelNatIso.hom

end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end


/-!
The actual J_E equivalence is weak on its original up-universe nerve map.
This is its map INTO the strict fibre, not the whole total-category J_E map.
The inclusion of that fibre in the total category still requires the genuine
geometric theorem and the original base conull result.
-/



noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- The original completed-fibre functor is weak as a map into its actual strict fibre. -/
theorem completedFiberStrictNerveMap_mem_realizationWeakEquivalences
    (E : FixedTargetExtension C X) :
    SSet.realizationWeakEquivalences (nerveMapCommonHomUp.{u, max u v, 0}
      (completedFiberStrictFunctor E)) := by
  exact @nerveMapCommonHomUp_mem_realizationWeakEquivalences_of_isEquivalence.{u, max u v, 0}
    (SInverse (Core C) (Core C)) _
    (Functor.Fiber (iteratedRowProjectionFunctor (C := C) (X := X))
      (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X))) _
    (completedFiberStrictFunctor E) (completedFiberStrict_isEquivalence E)

end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end





/-! ## literal completed K negative7 -/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.GenericCoreTranslation CategoryTheory.GenericCoreResidualTranslation
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.CompletedFiberNegativeTranslation

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The actual completed-fibre transport prepends T only to the original denominator. -/
theorem leftNegative_object (T : Core C) (a : SInverse (Core C) (Core C)) :
    ((legacyNegativeFunctor T).obj a).of = (a.of.1, T ⊗ a.of.2) := rfl

/-- The literal legacy representative keeps its original outer stabilizer. -/
theorem leftNegative_stabilizer (T : Core C) {a b : SInverse (Core C) (Core C)}
    (r : RawHom a b) : (legacyNegativeRaw T r).stabilizer = r.stabilizer := rfl

/-- The actual positive epsilon is unchanged. -/
theorem leftNegative_positive (T : Core C) {a b : SInverse (Core C) (Core C)}
    (r : RawHom a b) : (legacyNegativeRaw T r).hom.1 = r.hom.1 := rfl

/-- The whole original denominator arrow follows the native swap and T-whiskering. -/
theorem leftNegative_denominator_hom (T : Core C)
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (legacyNegativeRaw T r).hom.2.iso.hom =
      (SInverseS.swapStabilizerIso T.of r.stabilizer.of a.of.2.of).hom ≫
        biprod.map (𝟙 T.of) r.hom.2.iso.hom := rfl

/-- The actual denominator-braiding comparison realizes to a full continuous homotopy,
from the original right-negative map to the literal completed-fibre left-negative map. -/
def rightToLeftNegativeRealizedHomotopy (T : Core C) :
    ContinuousMap.Homotopy (negativeRealizedMap T)
      ((SSet.toTop.map (nerveMap (legacyNegativeFunctor T))).hom) :=
  SSet.realizeHomotopy (genericNerve (C := C)) (genericNerve (C := C))
    (negativeNerveMap T) (nerveMap (legacyNegativeFunctor T))
    (NatTrans.nerveHomotopy (rightToLegacyNegativeIso T).hom)

/-- The literal left-negative realized map has the original positive map as inverse.
Both inverse homotopies are derived from the actual comparison and proved right-negative HE. -/
def leftNegativeRealizedEquiv (T : Core C) :
    ContinuousMap.HomotopyEquiv (genericSpace (C := C)) (genericSpace (C := C)) where
  toFun := (SSet.toTop.map (nerveMap (legacyNegativeFunctor T))).hom
  invFun := positiveRealizedMap T
  left_inv := by
    let H := rightToLeftNegativeRealizedHomotopy T
    exact ⟨((ContinuousMap.Homotopy.refl (positiveRealizedMap T)).comp H.symm).trans
      (negativeRealizedEquiv T).left_inv.some⟩
  right_inv := by
    let H := rightToLeftNegativeRealizedHomotopy T
    exact ⟨(H.symm.compContinuousMap (positiveRealizedMap T)).trans
      (negativeRealizedEquiv T).right_inv.some⟩

/-- The actual completed-fibre left-negative functor is a realization weak equivalence.
No eta or pi_N transition conclusion is an input; the underlying map is the literal one above. -/
theorem leftNegative_mem_realizationWeakEquivalences (T : Core C) :
    SSet.realizationWeakEquivalences (nerveMap (legacyNegativeFunctor T)) := by
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (nerveMap (legacyNegativeFunctor T)))
  exact TopCat.mem_of_eq_toFun (leftNegativeRealizedEquiv T) rfl

end AlgebraicKTheory.CompletedFiberNegativeTranslation

end


/-! ## canonical lift naturality5 -/

/-!
The canonical cocartesian fibre transport uses the literal negative-left K functor.
This fragment follows the cofibered projection, original J_E and its strict-fibre
equivalence. The comparison components are original lifts over the base arrow;
they are natural transformations, not ambient isomorphisms or WE witnesses.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.GenericCoreTranslation CategoryTheory.GenericCoreResidualTranslation
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

omit [ExactCategory C] [HasZeroObject C] in
private theorem native_swap_twice (U T D : C) :
    (SInverseS.swapStabilizerIso U T D).hom ≫
      (SInverseS.swapStabilizerIso T U D).hom = 𝟙 (T ⊞ (U ⊞ D)) := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext' <;> simp

omit [ExactCategory C] in
private theorem interchange_swap_twice (U T D : Core C) :
    (denominatorInterchangeIso U T D).hom ≫
      (denominatorInterchangeIso T U D).hom = 𝟙 (T ⊗ (U ⊗ D)) := by
  apply Core.hom_ext
  have h := native_swap_twice U.of T.of D.of
  simpa only [coreCategory_comp_iso, Iso.trans_hom, denominatorInterchangeIso_hom,
    coreBiprodTensorObj_of, coreCategory_id_iso, Iso.refl_hom] using h

omit [ExactCategory C] in
/-- The completed negative transport keeps epsilon and moves the actual denominator
through the opposite interchange before T acts on delta. -/
theorem completedNegativeRaw_denominator (T : Core C)
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (legacyNegativeRaw T r).hom.2 =
      (denominatorInterchangeIso T r.stabilizer a.of.2).hom ≫ T ◁ r.hom.2 := by
  let delta : r.stabilizer ⊗ (T ⊗ a.of.2) ⟶ T ⊗ b.of.2 := (legacyNegativeRaw T r).hom.2
  have hActual : delta.iso.hom =
      (SInverseS.swapStabilizerIso T.of r.stabilizer.of a.of.2.of).hom ≫
        biprod.map (𝟙 T.of) r.hom.2.iso.hom :=
    AlgebraicKTheory.CompletedFiberNegativeTranslation.leftNegative_denominator_hom T r
  have hInterchange := denominatorInterchangeIso_hom T r.stabilizer a.of.2
  have hWhisker := core_left_hom T r.hom.2
  have hRight :
      ((denominatorInterchangeIso T r.stabilizer a.of.2).hom ≫ T ◁ r.hom.2).iso.hom =
        (SInverseS.swapStabilizerIso T.of r.stabilizer.of a.of.2.of).hom ≫
          biprod.map (𝟙 T.of) r.hom.2.iso.hom := by
    change (denominatorInterchangeIso T r.stabilizer a.of.2).hom.iso.hom ≫
        (T ◁ r.hom.2).iso.hom = _
    exact (congrArg
      (fun q : r.stabilizer.of ⊞ (T.of ⊞ a.of.2.of) ⟶
          T.of ⊞ (r.stabilizer.of ⊞ a.of.2.of) => q ≫ (T ◁ r.hom.2).iso.hom)
      hInterchange).trans
        (congrArg
          (fun q : T.of ⊞ (r.stabilizer.of ⊞ a.of.2.of) ⟶ T.of ⊞ b.of.2.of =>
            (SInverseS.swapStabilizerIso T.of r.stabilizer.of a.of.2.of).hom ≫ q)
          hWhisker)
  apply Core.hom_ext
  exact hActual.trans hRight.symm

/-- The actual inner square slides a K denominator map through the original base lift.
Its row remains the same given gamma; only the two explicit interchanges cancel. -/
theorem completedFiber_inner_lift_square {E F : FixedTargetExtension C X}
    (r : RawHom (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) ⟨F⟩)
    {a b : SInverse (Core C) (Core C)} (k : RawHom a b) :
    (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map
        (X := (E, k.stabilizer ⊗ a.of.2)) (Y := (E, b.of.2)) (𝟙 E, k.hom.2) ≫
        localizedBaseLiftHom ((completedFiberFunctor E).obj b).of.1 r =
      (denominatorLeftFunctor k.stabilizer).map
          (localizedBaseLiftHom ((completedFiberFunctor E).obj a).of.1 r) ≫
        (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map
          (X := (F, k.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)))
          (Y := (F, r.stabilizer ⊗ b.of.2)) (𝟙 F, (legacyNegativeRaw r.stabilizer k).hom.2) :=
    by
  let I := MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)
  let deltaE : (E, k.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2) := (𝟙 E, k.hom.2)
  let deltaF : (F, k.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)) ⟶
      (F, r.stabilizer ⊗ b.of.2) :=
    (𝟙 F, (legacyNegativeRaw r.stabilizer k).hom.2)
  let q := localizedBaseLiftRaw ((completedFiberFunctor E).obj b).of.1 r
  let s := denominatorLeftRaw k.stabilizer
    (localizedBaseLiftRaw ((completedFiberFunctor E).obj a).of.1 r)
  let target : localizedRows (C := C) X := ⟨(F, r.stabilizer ⊗ b.of.2)⟩
  let common : RawHom (denominatorLeftObject k.stabilizer
      ((completedFiberFunctor E).obj a).of.1) target :=
    ⟨r.stabilizer, (r.hom, r.stabilizer ◁ k.hom.2)⟩
  have hLeftRaw : (⟨r.stabilizer, r.stabilizer ⊴ₗ deltaE ≫ q.hom⟩ :
      RawHom (denominatorLeftObject k.stabilizer
        ((completedFiberFunctor E).obj a).of.1) target) = common := by
    apply congrArg
      (fun h : r.stabilizer ⊙ₗ (E, k.stabilizer ⊗ a.of.2) ⟶ target.of =>
        (⟨r.stabilizer, h⟩ :
          RawHom (denominatorLeftObject k.stabilizer
            ((completedFiberFunctor E).obj a).of.1) target))
    apply Prod.ext
    · change leftSumMap (𝟙 r.stabilizer) (𝟙 E) ≫ r.hom = r.hom
      rw [leftSumMap_id, Category.id_comp]
    · change r.stabilizer ◁ k.hom.2 ≫ 𝟙 (r.stabilizer ⊗ b.of.2) =
        r.stabilizer ◁ k.hom.2
      exact Category.comp_id _
  have hRightRaw : (⟨r.stabilizer, s.hom ≫ deltaF⟩ :
      RawHom (denominatorLeftObject k.stabilizer
        ((completedFiberFunctor E).obj a).of.1) target) = common := by
    apply congrArg
      (fun h : r.stabilizer ⊙ₗ (E, k.stabilizer ⊗ a.of.2) ⟶ target.of =>
        (⟨r.stabilizer, h⟩ :
          RawHom (denominatorLeftObject k.stabilizer
            ((completedFiberFunctor E).obj a).of.1) target))
    apply Prod.ext
    · change r.hom ≫ 𝟙 F = r.hom
      exact Category.comp_id _
    · change ((denominatorInterchangeIso k.stabilizer r.stabilizer a.of.2).hom ≫
          k.stabilizer ◁ 𝟙 (r.stabilizer ⊗ a.of.2)) ≫
          (legacyNegativeRaw r.stabilizer k).hom.2 = r.stabilizer ◁ k.hom.2
      let d : r.stabilizer ⊗ (k.stabilizer ⊗ a.of.2) ⟶ r.stabilizer ⊗ b.of.2 :=
        r.stabilizer ◁ k.hom.2
      have hDelta : (legacyNegativeRaw r.stabilizer k).hom.2 =
          (denominatorInterchangeIso r.stabilizer k.stabilizer a.of.2).hom ≫ d :=
        completedNegativeRaw_denominator r.stabilizer k
      have hSwap := interchange_swap_twice k.stabilizer r.stabilizer a.of.2
      have hCancel : (denominatorInterchangeIso k.stabilizer r.stabilizer a.of.2).hom ≫
          ((denominatorInterchangeIso r.stabilizer k.stabilizer a.of.2).hom ≫ d) = d :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg
            (fun q : r.stabilizer ⊗ (k.stabilizer ⊗ a.of.2) ⟶
                r.stabilizer ⊗ (k.stabilizer ⊗ a.of.2) => q ≫ d) hSwap).trans
              (Category.id_comp d))
      have hUnit : (denominatorInterchangeIso k.stabilizer r.stabilizer a.of.2).hom ≫
          k.stabilizer ◁ 𝟙 (r.stabilizer ⊗ a.of.2) =
            (denominatorInterchangeIso k.stabilizer r.stabilizer a.of.2).hom :=
        (congrArg
          (fun q : k.stabilizer ⊗ (r.stabilizer ⊗ a.of.2) ⟶
              k.stabilizer ⊗ (r.stabilizer ⊗ a.of.2) =>
            (denominatorInterchangeIso k.stabilizer r.stabilizer a.of.2).hom ≫ q)
          (whiskerLeft_id k.stabilizer (r.stabilizer ⊗ a.of.2))).trans (Category.comp_id _)
      exact (congrArg
        (fun q : r.stabilizer ⊗ (k.stabilizer ⊗ a.of.2) ⟶
            k.stabilizer ⊗ (r.stabilizer ⊗ a.of.2) =>
          q ≫ (legacyNegativeRaw r.stabilizer k).hom.2) hUnit).trans
            ((congrArg
              (fun q : k.stabilizer ⊗ (r.stabilizer ⊗ a.of.2) ⟶
                  r.stabilizer ⊗ b.of.2 =>
                (denominatorInterchangeIso k.stabilizer r.stabilizer a.of.2).hom ≫ q)
              hDelta).trans hCancel)
  have hLeft : I.map deltaE ≫
      localizedBaseLiftHom ((completedFiberFunctor E).obj b).of.1 r =
      MonoidalActionCategory.Hom.mk common :=
    (_root_.Quotient.sound (rawPreMap_rel deltaE q)).trans
      (congrArg MonoidalActionCategory.Hom.mk hLeftRaw)
  have hRight : (denominatorLeftFunctor k.stabilizer).map
        (localizedBaseLiftHom ((completedFiberFunctor E).obj a).of.1 r) ≫ I.map deltaF =
      MonoidalActionCategory.Hom.mk common := by
    change (denominatorLeftFunctor k.stabilizer).map
        (MonoidalActionCategory.Hom.mk
          (localizedBaseLiftRaw ((completedFiberFunctor E).obj a).of.1 r)) ≫ I.map deltaF = _
    rw [denominatorLeftFunctor_map_mk]
    exact (_root_.Quotient.sound (rawPostMap_rel s deltaF)).trans
      (congrArg MonoidalActionCategory.Hom.mk hRightRaw)
  exact hLeft.trans hRight.symm

/-- The original canonical lifts are natural on every completed K quotient morphism.
Their entire row gamma and denominator delta are retained in the square. -/
theorem completedFiber_lift_naturality {E F : FixedTargetExtension C X}
    (r : RawHom (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) ⟨F⟩)
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (completedFiberFunctor E).map f ≫ iteratedLiftHom ((completedFiberFunctor E).obj b) r =
      iteratedLiftHom ((completedFiberFunctor E).obj a) r ≫
        (completedFiberFunctor F).map ((legacyNegativeFunctor r.stabilizer).map f) := by
  obtain ⟨k, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  let I := MonoidalActionCategory.inclusion (Core C)
    (localizedRows (C := C) X × Core C)
  let ja := completedFiberObject E a
  let jb := completedFiberObject E b
  let ta := completedFiberObject F (legacyNegativeObj r.stabilizer a)
  let tb := completedFiberObject F (legacyNegativeObj r.stabilizer b)
  let phiA : ja.of ⟶ ta.of :=
    (localizedBaseLiftHom ja.of.1 r, 𝟙 a.of.1)
  let phiB : jb.of ⟶ tb.of :=
    (localizedBaseLiftHom jb.of.1 r, 𝟙 b.of.1)
  let q := completedFiberRaw E k
  let s := completedFiberRaw F (legacyNegativeRaw r.stabilizer k)
  let left : RawHom ja tb := ⟨k.stabilizer, q.hom ≫ phiB⟩
  let right : RawHom ja tb := ⟨k.stabilizer, k.stabilizer ⊴ₗ phiA ≫ s.hom⟩
  have hRaw : left = right := by
    apply congrArg
      (fun h : k.stabilizer ⊙ₗ ja.of ⟶ tb.of => (⟨k.stabilizer, h⟩ : RawHom ja tb))
    apply Prod.ext
    · change
        (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map
            ((𝟙 E, k.hom.2) : (E, k.stabilizer ⊗ a.of.2) ⟶ (E, b.of.2)) ≫
          localizedBaseLiftHom jb.of.1 r =
        (k.stabilizer ⊴ₗ localizedBaseLiftHom ja.of.1 r) ≫
          (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X × Core C)).map
            ((𝟙 F, (legacyNegativeRaw r.stabilizer k).hom.2) :
              (F, k.stabilizer ⊗ (r.stabilizer ⊗ a.of.2)) ⟶
                (F, r.stabilizer ⊗ b.of.2))
      rw [denominatorLeftAction_map_eq]
      exact completedFiber_inner_lift_square r k
    · have hEpsilon : (legacyNegativeRaw r.stabilizer k).hom.1 = k.hom.1 :=
        AlgebraicKTheory.CompletedFiberNegativeTranslation.leftNegative_positive r.stabilizer k
      change k.hom.1 ≫ 𝟙 b.of.1 =
        (k.stabilizer ◁ 𝟙 a.of.1) ≫ (legacyNegativeRaw r.stabilizer k).hom.1
      have hRight : (k.stabilizer ◁ 𝟙 a.of.1) ≫
          (legacyNegativeRaw r.stabilizer k).hom.1 = k.hom.1 :=
        (congrArg
          (fun q : k.stabilizer ⊗ a.of.1 ⟶ k.stabilizer ⊗ a.of.1 =>
            q ≫ (legacyNegativeRaw r.stabilizer k).hom.1)
          (whiskerLeft_id k.stabilizer a.of.1)).trans
            ((Category.id_comp _).trans hEpsilon)
      exact (Category.comp_id _).trans hRight.symm
  have hLeft : MonoidalActionCategory.Hom.mk q ≫ I.map phiB =
      MonoidalActionCategory.Hom.mk left :=
    _root_.Quotient.sound (rawPostMap_rel q phiB)
  have hRight : I.map phiA ≫ MonoidalActionCategory.Hom.mk s =
      MonoidalActionCategory.Hom.mk right :=
    _root_.Quotient.sound (rawPreMap_rel phiA s)
  have hJE := completedFiberFunctor_map_mk (a := a) (b := b) E k
  have hNegative := legacyNegativeFunctor_map_mk r.stabilizer k
  have hJF := completedFiberFunctor_map_mk
    (a := legacyNegativeObj r.stabilizer a) (b := legacyNegativeObj r.stabilizer b) F
    (legacyNegativeRaw r.stabilizer k)
  have hMapRight : (completedFiberFunctor F).map
      ((legacyNegativeFunctor r.stabilizer).map (MonoidalActionCategory.Hom.mk k)) =
        MonoidalActionCategory.Hom.mk s :=
    (congrArg
      (fun q : legacyNegativeObj r.stabilizer a ⟶ legacyNegativeObj r.stabilizer b =>
        (completedFiberFunctor F).map
          (X := legacyNegativeObj r.stabilizer a) (Y := legacyNegativeObj r.stabilizer b) q)
      hNegative).trans hJF
  let rA : RawHom (iteratedRowProjectionObject ja)
      (⟨F⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) := r
  let rB : RawHom (iteratedRowProjectionObject jb)
      (⟨F⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) := r
  have hLiftA := (iteratedLiftHom_asOrdinary ja rA).symm
  have hLiftB := (iteratedLiftHom_asOrdinary jb rB).symm
  exact (congrArg (fun q : ja ⟶ jb => q ≫ iteratedLiftHom jb r) hJE).trans
    ((congrArg (fun h : jb ⟶ tb => MonoidalActionCategory.Hom.mk q ≫ h) hLiftB).trans
      (hLeft.trans ((congrArg MonoidalActionCategory.Hom.mk hRaw).trans
        (hRight.symm.trans
          ((congrArg (fun q : ja ⟶ ta => q ≫ MonoidalActionCategory.Hom.mk s)
            hLiftA.symm).trans
              (congrArg (fun q : ta ⟶ tb => iteratedLiftHom ja r ≫ q) hMapRight.symm))))))

/-- The actual fibre comparison is a natural transformation lying over the given base arrow.
It is not a natural Iso: its components are the original cocartesian lifts. -/
def completedFiberLiftNatTrans {E F : FixedTargetExtension C X}
    (r : RawHom (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) ⟨F⟩) :
    completedFiberFunctor E ⟶ legacyNegativeFunctor r.stabilizer ⋙ completedFiberFunctor F where
  app a := iteratedLiftHom ((completedFiberFunctor E).obj a) r
  naturality {a b} f := by exact completedFiber_lift_naturality r f

/-- Each original comparison component is strongly cocartesian over the same literal base map. -/
theorem completedFiberLiftNatTrans_isStronglyCocartesian {E F : FixedTargetExtension C X}
    (r : RawHom (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) ⟨F⟩)
    (a : SInverse (Core C) (Core C)) :
    (iteratedRowProjectionFunctor (C := C) (X := X)).IsStronglyCocartesian
      (MonoidalActionCategory.Hom.mk r) ((completedFiberLiftNatTrans r).app a) := by
  exact iteratedLiftHom_isStronglyCocartesian ((completedFiberFunctor E).obj a) r

end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end


/-! ## actual comma comparison7 -/

/-!
The original completed fibre maps into the original right comma category.
The actual canonical lift over g gives a natural comparison from post_g Psi_E
to Psi_F followed by the literal negative-left translation. Its components
are comma arrows, not isomorphisms or supplied transition weak equivalences.

This fragment follows the exact cofibered/fibre context and lift naturality.
It requires the existing public CofiberedCommaAdjunction provider; no owning
artifact, imported new module or native verification is claimed.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.GenericCoreTranslation CategoryTheory.GenericCoreResidualTranslation
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- Psi_E uses the original completed K inclusion and the actual strict-fibre comma map. -/
def completedFiberCommaFunctor (E : FixedTargetExtension C X) :
    SInverse (Core C) (Core C) ⥤
      CostructuredArrow (iteratedRowProjectionFunctor (C := C) (X := X))
        (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) := by
  let p := iteratedRowProjectionFunctor (C := C) (X := X)
  letI : p.IsCofibered := iteratedRowProjectionFunctor_isCofibered
  exact completedFiberStrictFunctor E ⋙
    Functor.IsCofibered.fiberToCostructuredArrow (p := p)
      (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X))

/-- The underlying comma object is the same original J_E object. -/
theorem completedFiberCommaFunctor_left (E : FixedTargetExtension C X)
    (a : SInverse (Core C) (Core C)) :
    ((completedFiberCommaFunctor E).obj a).left = (completedFiberFunctor E).obj a := rfl

/-- The structural comma arrow is the actual identity at E; its proof cast is a loop equality. -/
theorem completedFiberCommaFunctor_hom (E : FixedTargetExtension C X)
    (a : SInverse (Core C) (Core C)) :
    ((completedFiberCommaFunctor E).obj a).hom =
      𝟙 (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) := by
  change eqToHom ((completedFiberStrictFunctor E).obj a).property = _
  exact eqToHom_refl _ _

/-- The complete source projection of Psi_E is the original total-category J_E. -/
theorem completedFiberCommaFunctor_projection (E : FixedTargetExtension C X) :
    completedFiberCommaFunctor E ⋙
      CostructuredArrow.proj (iteratedRowProjectionFunctor (C := C) (X := X))
        (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) =
      completedFiberFunctor E := rfl

private theorem completedFiberCommaFunctor_map_left (E : FixedTargetExtension C X)
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    ((completedFiberCommaFunctor E).map f).left = (completedFiberFunctor E).map f := rfl

/-- Each original canonical lift is an actual arrow of the right comma category.
Its base equation is the literal projection identity of the original lift. -/
def completedFiberCommaComparisonComponent {E F : FixedTargetExtension C X}
    (r : RawHom (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) ⟨F⟩)
    (a : SInverse (Core C) (Core C)) :
    ((completedFiberCommaFunctor E ⋙ CostructuredArrow.map
        (MonoidalActionCategory.Hom.mk r)).obj a) ⟶
      ((legacyNegativeFunctor r.stabilizer ⋙ completedFiberCommaFunctor F).obj a) :=
  let p := iteratedRowProjectionFunctor (C := C) (X := X)
  let eRow : MonoidalActionCategory (Core C) (FixedTargetExtension C X) := ⟨E⟩
  let fRow : MonoidalActionCategory (Core C) (FixedTargetExtension C X) := ⟨F⟩
  let g : eRow ⟶ fRow := MonoidalActionCategory.Hom.mk r
  let ja := completedFiberObject E a
  let ta := completedFiberObject F (legacyNegativeObj r.stabilizer a)
  let rNative : RawHom (iteratedRowProjectionObject ja) fRow := r
  let cSource : CostructuredArrow p fRow :=
    (CostructuredArrow.map g).obj ((completedFiberCommaFunctor E).obj a)
  let cTarget : CostructuredArrow p fRow :=
    (completedFiberCommaFunctor F).obj (legacyNegativeObj r.stabilizer a)
  let phi : cSource.left ⟶ cTarget.left := iteratedLiftHom ja rNative
  let hComm : p.map phi ≫ cTarget.hom = cSource.hom := by
    let pPhi : eRow ⟶ fRow := p.map (X := ja) (Y := ta) phi
    have hProjection : pPhi = g := iteratedLiftRaw_projection ja rNative
    have hSource : ((completedFiberCommaFunctor E).obj a).hom = 𝟙 eRow :=
      completedFiberCommaFunctor_hom E a
    have hTarget : cTarget.hom = 𝟙 fRow :=
      completedFiberCommaFunctor_hom F (legacyNegativeObj r.stabilizer a)
    have hLeft : g = (𝟙 eRow) ≫ g := (Category.id_comp g).symm
    have hSourcePost : g = ((completedFiberCommaFunctor E).obj a).hom ≫ g :=
      hLeft.trans (congrArg
        (fun q : eRow ⟶ eRow => q ≫ g) hSource.symm)
    have hTargetPost : pPhi ≫ cTarget.hom = pPhi :=
      (congrArg (fun q : fRow ⟶ fRow => pPhi ≫ q) hTarget).trans
        (Category.comp_id pPhi)
    change pPhi ≫ cTarget.hom = ((completedFiberCommaFunctor E).obj a).hom ≫ g
    exact hTargetPost.trans (hProjection.trans hSourcePost)
  CostructuredArrow.homMk (f := cSource) (f' := cTarget) phi hComm

/-- The comparison preserves the full original lift as its underlying morphism. -/
theorem completedFiberCommaComparisonComponent_left {E F : FixedTargetExtension C X}
    (r : RawHom (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) ⟨F⟩)
    (a : SInverse (Core C) (Core C)) :
    (completedFiberCommaComparisonComponent r a).left =
      iteratedLiftHom ((completedFiberFunctor E).obj a) r := rfl

/-- The canonical right-comma comparison is natural on every original epsilon/delta map.
No chosen transition result or category equivalence is an input. -/
def completedFiberCommaComparison {E F : FixedTargetExtension C X}
    (r : RawHom (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) ⟨F⟩) :
    completedFiberCommaFunctor E ⋙ CostructuredArrow.map (MonoidalActionCategory.Hom.mk r) ⟶
      legacyNegativeFunctor r.stabilizer ⋙ completedFiberCommaFunctor F where
  app := completedFiberCommaComparisonComponent r
  naturality {a b} f := by
    apply CostructuredArrow.hom_ext
    change ((completedFiberCommaFunctor E).map f).left ≫
        (completedFiberCommaComparisonComponent r b).left =
      (completedFiberCommaComparisonComponent r a).left ≫
        ((completedFiberCommaFunctor F).map ((legacyNegativeFunctor r.stabilizer).map f)).left
    have hE := completedFiberCommaFunctor_map_left E f
    have hF := completedFiberCommaFunctor_map_left F ((legacyNegativeFunctor r.stabilizer).map f)
    have hA := completedFiberCommaComparisonComponent_left r a
    have hB := completedFiberCommaComparisonComponent_left r b
    have hLeft := congrArg₂
      (fun (q : (completedFiberFunctor E).obj a ⟶ (completedFiberFunctor E).obj b)
          (h : (completedFiberFunctor E).obj b ⟶
            (completedFiberFunctor F).obj ((legacyNegativeFunctor r.stabilizer).obj b)) => q ≫ h)
      hE hB
    have hRight := congrArg₂
      (fun (h : (completedFiberFunctor E).obj a ⟶
            (completedFiberFunctor F).obj ((legacyNegativeFunctor r.stabilizer).obj a))
          (q : (completedFiberFunctor F).obj ((legacyNegativeFunctor r.stabilizer).obj a) ⟶
            (completedFiberFunctor F).obj ((legacyNegativeFunctor r.stabilizer).obj b)) => h ≫ q)
      hA hF
    exact hLeft.trans ((completedFiber_lift_naturality r f).trans hRight.symm)


end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end


/-! ## derived comma transitions3 -/

/-!
The original completed K comparison is weak into each literal right comma.
The actual lift natural transformation compares post_g Psi_E with the
original negative-left translation followed by Psi_F. Realize its full up
nerve cylinder, then cancel the derived Psi_E map to obtain the ordinary
comma transition. No transition, Psi, ambient J or eta weakness is supplied.

This fragment follows the exact cofibered/fibre/up-cylinder context, the
actual adjunction realization, the canonical lift comparison and the
already-derived literal completed-K negative translation.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.GenericCoreTranslation CategoryTheory.GenericCoreResidualTranslation
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- The original completed K functor into the right comma is weak by the
derived strict-fibre equivalence and the actual cofibered comma adjunction. -/
theorem completedFiberCommaNerveMap_mem_realizationWeakEquivalences
    (E : FixedTargetExtension C X) :
    SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E)) := by
  let p := iteratedRowProjectionFunctor (C := C) (X := X)
  let d : MonoidalActionCategory (Core C) (FixedTargetExtension C X) := ⟨E⟩
  have hCof : p.IsCofibered :=
    iteratedRowProjectionFunctor_isCofibered (C := C) (X := X)
  let i := @Functor.IsCofibered.fiberToCostructuredArrow
    (MonoidalActionCategory (Core C) (FixedTargetExtension C X))
    (iteratedLocalizedRows (C := C) (X := X)) _ _ p d
  have hI : SSet.realizationWeakEquivalences (nerveMap i) :=
    @Functor.IsCofibered.fiberToCostructuredArrow_mem_realizationWeakEquivalences
      (iteratedLocalizedRows (C := C) (X := X)) _
      (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) _ p hCof d
  have hJ : SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberStrictFunctor E)) :=
    completedFiberStrictNerveMap_mem_realizationWeakEquivalences E
  have hComposite := SSet.realizationWeakEquivalences.comp_mem
    (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberStrictFunctor E)) (nerveMap i) hJ hI
  have hPsi : completedFiberStrictFunctor E ⋙ i = completedFiberCommaFunctor E := rfl
  have hMap := nerveMapCommonHomUp_nerveMap_comp (completedFiberStrictFunctor E) i
  rw [hPsi] at hMap
  exact hMap ▸ hComposite

/-- A represented original base arrow induces a weak ordinary comma map.
Its actual lift comparison is used through the complete up nerve homotopy. -/
theorem completedFiberCommaPostcomposition_mk_mem_realizationWeakEquivalences
    {E F : FixedTargetExtension C X}
    (r : RawHom
      (⟨E⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)) ⟨F⟩) :
    SSet.realizationWeakEquivalences
      (nerveMap (CostructuredArrow.map
        (S := iteratedRowProjectionFunctor (C := C) (X := X))
        (MonoidalActionCategory.Hom.mk r))) := by
  let post := CostructuredArrow.map
    (S := iteratedRowProjectionFunctor (C := C) (X := X))
    (MonoidalActionCategory.Hom.mk r)
  have hNegative : SSet.realizationWeakEquivalences
      (nerveMap (legacyNegativeFunctor r.stabilizer)) :=
    AlgebraicKTheory.CompletedFiberNegativeTranslation.leftNegative_mem_realizationWeakEquivalences
      r.stabilizer
  have hPsiF : SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor F)) :=
    completedFiberCommaNerveMap_mem_realizationWeakEquivalences F
  have hRightComposite := SSet.realizationWeakEquivalences.comp_mem
    (nerveMap (legacyNegativeFunctor r.stabilizer))
    (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor F)) hNegative hPsiF
  have hRightMap := nerveMap_nerveMapCommonHomUp_comp
    (legacyNegativeFunctor r.stabilizer) (completedFiberCommaFunctor F)
  have hRight : SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (legacyNegativeFunctor r.stabilizer ⋙
        completedFiberCommaFunctor F)) :=
    hRightMap ▸ hRightComposite
  have hSimplicial : SSet.Homotopy
      (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E ⋙ post))
      (nerveMapCommonHomUp.{u, max u v, 0}
        (legacyNegativeFunctor r.stabilizer ⋙ completedFiberCommaFunctor F)) :=
    NatTrans.nerveHomotopyCommonHomUp.{u, max u v, 0} (completedFiberCommaComparison r)
  let K : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  let Q : SSet.{max u v} := nerve
    (CostructuredArrow (iteratedRowProjectionFunctor (C := C) (X := X))
      (⟨F⟩ : MonoidalActionCategory (Core C) (FixedTargetExtension C X)))
  let hContinuous := SSet.realizeHomotopy K Q
    (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E ⋙ post))
    (nerveMapCommonHomUp.{u, max u v, 0}
      (legacyNegativeFunctor r.stabilizer ⋙ completedFiberCommaFunctor F)) hSimplicial
  have hLeft : SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E ⋙ post)) := by
    change TopCat.weakHomotopyEquivalences
      (SSet.toTop.map
        (nerveMapCommonHomUp.{u, max u v, 0}
          (legacyNegativeFunctor r.stabilizer ⋙ completedFiberCommaFunctor F))) at hRight
    change TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E ⋙ post)))
    exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy hContinuous).mpr hRight
  have hPsiE : SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E)) :=
    completedFiberCommaNerveMap_mem_realizationWeakEquivalences E
  have hLeftMap := nerveMapCommonHomUp_nerveMap_comp (completedFiberCommaFunctor E) post
  have hLeftComposite : SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E) ≫ nerveMap post) :=
    hLeftMap.symm ▸ hLeft
  exact SSet.realizationWeakEquivalences.of_precomp
    (nerveMapCommonHomUp.{u, max u v, 0} (completedFiberCommaFunctor E)) (nerveMap post) hPsiE
      hLeftComposite

/-- Every literal original base morphism induces a weak right-comma transition.
The representative is obtained from the original quotient, not supplied. -/
theorem iteratedRowProjection_rightCommaTransition_mem_weakHomotopyEquivalences
    {a b : MonoidalActionCategory (Core C) (FixedTargetExtension C X)} (g : a ⟶ b) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (nerveMap (CostructuredArrow.map
        (S := iteratedRowProjectionFunctor (C := C) (X := X)) g))) := by
  change SSet.realizationWeakEquivalences
    (nerveMap (CostructuredArrow.map
      (S := iteratedRowProjectionFunctor (C := C) (X := X)) g))
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep g
  exact completedFiberCommaPostcomposition_mk_mem_realizationWeakEquivalences
    (E := a.of) (F := b.of) r

end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end
