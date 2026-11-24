/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiExpandedDegenerationModels
public import MathlibExt.AlgebraicGeometry.StackChowGroups
public import MathlibExt.AlgebraicGeometry.StableMapNumericalClasses

/-!
# Actual central stable-map families and their moduli realization

The target is an etale-local standard expanded degeneration with one
global base map. The curve, markings, predeformability and contraction
are native scheme data. The central numerical class is computed after the
canonical pullback factorization to the specified original W0.

The moduli realization retains a native fibre-groupoid equivalence and
all Cartesian target/source maps, naturality, unit and composition laws.
It supplies geometry; source cotangent/POT/cone/virtual constructions
are separate output requests normalized on these same maps.

Source: Jun Li arXiv:math/0110113v1, introduction pp1--4, Section1.1,
Proposition1.18 and Sections2--3; arXiv:math/0009097v1, Section2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiExpandedCentralModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open ExpandedTargetChainGeometry ExpandedTargetGluingModels MarkedCurveStabilization
open LiExpandedDegenerationModels StackCycleGeometry StackCycleRelations

variable {k : Type} [Field k] {P Q : RelativePair (k := k)} {W0 : SingularTarget P Q}
  (W : OneParameter P Q W0) (S : LiExpandedDegenerationModels.StandardSystem W)
  (n g : ℕ) (T : Over (Spec (.of k)))

def centralBase : T ⟶ W.curve := toUnit T ≫ W.zero

structure Family where
  target : LiExpandedDegenerationModels.ExpandedFamily W S T (centralBase W T)
  curve : MarkedFamily T.left n g
  map : curve.X ⟶ target.scheme.left
  over : map ≫ target.projection.left = curve.π
  predeformable : RelativeExpandedMapFamilies.IsPredeformable curve.π target.projection.left map over

def centralContraction (F : Family W S n g T) : F.target.scheme ⟶ W0.scheme :=
  pullback.lift F.target.contraction (F.target.projection ≫ toUnit T)
    (by simpa [centralBase, Category.assoc] using F.target.over) ≫ W.central.inv

def contractedFamily (F : Family W S n g T) :
    GeneralStableMapFamilies.Family W0.scheme.hom n g T.left T.hom where
  curve := F.curve
  map := F.map ≫ (centralContraction W S n g T F).left
  over := by
    rw [Category.assoc, Over.w (centralContraction W S n g T F),
      ← Over.w F.target.projection, ← Category.assoc, F.over]

structure FamilyIso (F H : Family W S n g T) where
  target : LiExpandedDegenerationModels.ExpandedIso W S F.target H.target
  source : F.curve.X ≅ H.curve.X
  over : source.hom ≫ H.curve.π = F.curve.π
  marking : ∀ i, F.curve.marking i ≫ source.hom = H.curve.marking i
  map : source.hom ≫ H.map = F.map ≫ target.iso.hom.left

@[ext] theorem FamilyIso.ext {F H : Family W S n g T} (f h : FamilyIso W S n g T F H)
    (target : f.target = h.target) (source : f.source = h.source) : f = h := by
  cases f; cases h; cases target; cases source; rfl

instance familyGroupoid : Groupoid (Family W S n g T) where
  Hom F H := FamilyIso W S n g T F H
  id F := ⟨⟨Iso.refl _, by simp, by simp⟩, Iso.refl _, by simp,
    by intro i; simp, by simp⟩
  comp f h :=
    ⟨⟨f.target.iso ≪≫ h.target.iso, by simp [Category.assoc, h.target.over, f.target.over],
        by simp [Category.assoc, h.target.contraction, f.target.contraction]⟩,
      f.source ≪≫ h.source, by simp [Category.assoc, h.over, f.over],
      by intro i; simp [← Category.assoc, f.marking, h.marking], by
        simp only [Iso.trans_hom, Over.comp_left]
        rw [Category.assoc, h.map, ← Category.assoc, f.map, Category.assoc]⟩
  inv f :=
    ⟨⟨f.target.iso.symm, by rw [← f.target.over]; simp,
      by rw [← f.target.contraction]; simp⟩,
      f.source.symm, by rw [← f.over]; simp,
      by intro i; rw [← f.marking i]; simp, by
        dsimp only [Iso.symm_hom]
        apply (cancel_epi f.source.hom).1
        rw [← Category.assoc, f.source.hom_inv_id, Category.id_comp,
          ← Category.assoc, f.map, Category.assoc, ← Over.comp_left,
          f.target.iso.hom_inv_id, Over.id_left, Category.comp_id]⟩
  id_comp f := by apply FamilyIso.ext <;> ext <;> simp
  comp_id f := by apply FamilyIso.ext <;> ext <;> simp
  assoc f h j := by apply FamilyIso.ext <;> ext <;> simp
  inv_comp f := by apply FamilyIso.ext <;> ext <;> simp
  comp_inv f := by apply FamilyIso.ext <;> ext <;> simp

def fibreMap (F : Family W S n g T) {Ω : Type} [Field Ω] (x : Spec (.of Ω) ⟶ T.left) :
    pullback F.curve.π x ⟶ pullback F.target.projection.left x :=
  pullback.lift (pullback.fst F.curve.π x ≫ F.map) (pullback.snd F.curve.π x)
    (by rw [Category.assoc, F.over]; exact pullback.condition)

structure GeometricAutomorphism (F : Family W S n g T)
    (Ω : Type) [Field Ω] (x : Spec (.of Ω) ⟶ T.left) where
  source : pullback F.curve.π x ≅ pullback F.curve.π x
  target : pullback F.target.projection.left x ≅ pullback F.target.projection.left x
  sourceOver : source.hom ≫ pullback.snd F.curve.π x = pullback.snd F.curve.π x
  targetOver : target.hom ≫ pullback.snd F.target.projection.left x =
    pullback.snd F.target.projection.left x
  contraction : target.hom ≫ pullback.fst F.target.projection.left x ≫ F.target.contraction.left =
    pullback.fst F.target.projection.left x ≫ F.target.contraction.left
  marking : ∀ i, fiberMark F.curve.π (F.curve.marking i) (F.curve.section_eq i) x ≫ source.hom =
    fiberMark F.curve.π (F.curve.marking i) (F.curve.section_eq i) x
  map : source.hom ≫ fibreMap W S n g T F x = fibreMap W S n g T F x ≫ target.hom

def IsStable (F : Family W S n g T) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T.left),
    Finite (GeometricAutomorphism W S n g T F Ω x)

variable [LocallyOfFiniteType W0.scheme.hom] [IsNoetherian W0.scheme.left]

/-- The family has numerical class `beta` on every geometric fibre (Li, Def. 4.6). -/
def HasCurveClass (beta : StableMapNumericalClasses.NumericalClass W0.scheme.left)
    (F : Family W S n g T) : Prop :=
  StableMapNumericalClasses.HasNumericalClass (contractedFamily W S n g T F).curve.π
    (contractedFamily W S n g T F).map beta

abbrev StableFamily (beta : StableMapNumericalClasses.NumericalClass W0.scheme.left) :=
  (show ObjectProperty (Family W S n g T) from
    fun F => IsStable W S n g T F ∧ HasCurveClass W S n g T beta F).FullSubcategory

structure FamilyBaseChange {T U : Over (Spec (.of k))} (f : T ⟶ U)
    (F : Family W S n g T) (H : Family W S n g U) where
  target : F.target.scheme ⟶ H.target.scheme
  targetCartesian : IsPullback target F.target.projection H.target.projection f
  targetContraction : target ≫ H.target.contraction = F.target.contraction
  source : F.curve.X ⟶ H.curve.X
  sourceCartesian : IsPullback source F.curve.π H.curve.π f.left
  marking : ∀ i, F.curve.marking i ≫ source = f.left ≫ H.curve.marking i
  map : F.map ≫ target.left = source ≫ H.map

structure ModuliModel (beta : StableMapNumericalClasses.NumericalClass W0.scheme.left) where
  stack : Stack (Spec (.of k))
  family : ∀ T : Over (Spec (.of k)), stack.Fibre T ⥤ StableFamily W S n g T beta
  equivalence : ∀ T, (family T).IsEquivalence
  dm : stack.IsDeligneMumfordStack
  finiteType : FiniteTypeArtin k stack
  reindex : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : stack.Fibre U),
    FamilyBaseChange W S n g f ((family T).obj ((pull stack f).obj x)).obj ((family U).obj x).obj
  targetNaturality : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U)
      {x y : stack.Fibre U} (h : x ⟶ y),
    ((family T).map ((pull stack f).map h)).hom.target.iso.hom ≫ (reindex f y).target =
      (reindex f x).target ≫ ((family U).map h).hom.target.iso.hom
  sourceNaturality : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U)
      {x y : stack.Fibre U} (h : x ⟶ y),
    ((family T).map ((pull stack f).map h)).hom.source.hom ≫ (reindex f y).source =
      (reindex f x).source ≫ ((family U).map h).hom.source.hom
  targetUnit : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T),
    ((family T).map ((stack.toPseudofunctor.mapId (.mk (op T))).hom.toNatTrans.app x)).hom.target.iso.hom =
      (reindex (𝟙 T) x).target
  sourceUnit : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T),
    ((family T).map ((stack.toPseudofunctor.mapId (.mk (op T))).hom.toNatTrans.app x)).hom.source.hom =
      (reindex (𝟙 T) x).source
  targetComp : ∀ {T U V : Over (Spec (.of k))} (f : T ⟶ U) (g : U ⟶ V) (x : stack.Fibre V),
    ((family T).map
      ((stack.toPseudofunctor.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app x)).hom.target.iso.hom ≫
      (reindex (f ≫ g) x).target = (reindex f ((pull stack g).obj x)).target ≫ (reindex g x).target
  sourceComp : ∀ {T U V : Over (Spec (.of k))} (f : T ⟶ U) (g : U ⟶ V) (x : stack.Fibre V),
    ((family T).map
      ((stack.toPseudofunctor.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app x)).hom.source.hom ≫
      (reindex (f ≫ g) x).source = (reindex f ((pull stack g).obj x)).source ≫ (reindex g x).source

end MathlibExt.AlgebraicGeometry.LiExpandedCentralModels
