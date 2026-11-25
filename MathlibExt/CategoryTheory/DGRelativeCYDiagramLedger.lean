/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGMoritaCospanModels
public import MathlibExt.CategoryTheory.DGModuleDiagramModels
public import MathlibExt.CategoryTheory.DGInductionSplittingModels
public import MathlibExt.CategoryTheory.DGModuleBarDiagramModels
public import MathlibExt.CategoryTheory.DGModuleUniversalConeModels
public import MathlibExt.CategoryTheory.DGCoherentIndexModels
public import Mathlib.Order.ULift

/-!
# Actual module positions in the relative Calabi-Yau cospan diagrams

The source cospan, category-level bar/dual objects, all enveloping
inductions, relative counit cones and signed module shifts are retained.
Every entry below lies in the same actual category of Z-bimodules.
The completed corners are the actual relative counit/dual-counit cones,
not arbitrarily named fibres or dual objects.

These object definitions do not certify diagram commutativity or a
Calabi-Yau structure. Source arrow, summand, composition and whole-diagram
comparisons are further normalized construction outputs.

Reference: Brav--Dyckerhoff, arXiv:1606.00619v1, diagrams 4.10, 6.6
and 6.7 and Theorem 6.2. The base is a field, without a characteristic-zero
restriction on this theorem.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGRelativeCalabiYauModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGMoritaCospanModels
open MathlibExt.Algebra.Homology.DGCategoryTraceModels
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBarDiagonalModels
open MathlibExt.CategoryTheory.DGCalabiYauMapModels
open MathlibExt.CategoryTheory.DGBimodulePushforwardModels
open MathlibExt.CategoryTheory.DGInductionCoherenceModels
open MathlibExt.CategoryTheory.DGModuleBiproductModels
open MathlibExt.CategoryTheory.DGInductionSplittingModels
open MathlibExt.CategoryTheory.DGModuleUniversalConeModels
open MathlibExt.CategoryTheory.DGModuleDiagramModels
open MathlibExt.CategoryTheory.DGModuleBarDiagramModels
open MathlibExt.CategoryTheory.DGCoherentIndexModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [Field k]

/-- The actual DG cospan and its displayed strict pushout square. -/
structure Cospan where
  A : DGCat k
  B : DGCat k
  C : DGCat k
  X : DGCat k
  Y : DGCat k
  Z : DGCat k
  e : A ⟶ X
  f : B ⟶ X
  g : B ⟶ Y
  h : C ⟶ Y
  i : X ⟶ Z
  j : Y ⟶ Z
  square : f ≫ i = g ≫ j

def Cospan.middle (P : Cospan (k := k)) : P.B ⟶ P.Z := P.f ≫ P.i

/-- Source/target coproduct, bar, dual and induction data contain no CY assertion. -/
structure ModuleData (P : Cospan (k := k)) (S : NegativeTraceSystem k) (n : ℤ) where
  DA : CYCategoryData S P.A
  DB : CYCategoryData S P.B
  DC : CYCategoryData S P.C
  DX : CYCategoryData S P.X
  DY : CYCategoryData S P.Y
  DZ : CYCategoryData S P.Z
  AB : DGCoproductModel P.A P.B
  BC : DGCoproductModel P.B P.C
  AC : DGCoproductModel P.A P.C
  DAB : CYCategoryData S AB.category
  DBC : CYCategoryData S BC.category
  DAC : CYCategoryData S AC.category
  leftFunctor : CoproductFunctorModel AB P.e P.f
  rightFunctor : CoproductFunctorModel BC P.g P.h
  outerFunctor : CoproductFunctorModel AC (P.e ≫ P.i) (P.h ≫ P.j)
  left : RelativeCYContext S leftFunctor.functor DAB DX
  right : RelativeCYContext S rightFunctor.functor DBC DY
  outer : RelativeCYContext S outerFunctor.functor DAC DZ
  E : RelativeCYContext S P.e DA DX
  F : RelativeCYContext S P.f DB DX
  G : RelativeCYContext S P.g DB DY
  H : RelativeCYContext S P.h DC DY
  I : RelativeCYContext S P.i DX DZ
  J : RelativeCYContext S P.j DY DZ
  M : RelativeCYContext S P.middle DB DZ
  leftCone : RelativeConeContext left n
  rightCone : RelativeConeContext right n
  outerCone : RelativeConeContext outer n
  shiftedA : CofibrantShiftModel ⟨DA.bar.module, DA.bar.cofibrant⟩ (1 - n)
  shiftedB : CofibrantShiftModel ⟨DB.bar.module, DB.bar.cofibrant⟩ (1 - n)
  shiftedC : CofibrantShiftModel ⟨DC.bar.module, DC.bar.cofibrant⟩ (1 - n)

namespace ModuleData

variable {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
  (D : ModuleData P S n)

/-- The finite grid used by the completed sparse source diagrams. -/
abbrev Grid := Fin 3 × Fin 3

/-- The source's diagram 6.7, including its two completed corners. -/
def dualNode (q : Grid) : DGDerivedModules k (enveloping P.Z P.Z) :=
  match q.1.val, q.2.val with
  | 0, 0 => ⟨D.DZ.inverse.replacement.module, D.DZ.inverse.replacement.cofibrant⟩
  | 0, 1 => D.I.induction.functor.obj
      ⟨D.DX.inverse.replacement.module, D.DX.inverse.replacement.cofibrant⟩
  | 0, 2 => D.I.induction.functor.obj (D.E.induction.functor.obj
      ⟨D.DA.inverse.replacement.module, D.DA.inverse.replacement.cofibrant⟩)
  | 1, 0 => D.J.induction.functor.obj
      ⟨D.DY.inverse.replacement.module, D.DY.inverse.replacement.cofibrant⟩
  | 1, 1 => D.M.induction.functor.obj
      ⟨D.DB.inverse.replacement.module, D.DB.inverse.replacement.cofibrant⟩
  | 1, 2 => D.I.induction.functor.obj ⟨D.leftCone.coneDual.module, D.leftCone.coneDual.cofibrant⟩
  | 2, 0 => D.J.induction.functor.obj (D.H.induction.functor.obj
      ⟨D.DC.inverse.replacement.module, D.DC.inverse.replacement.cofibrant⟩)
  | 2, 1 => D.J.induction.functor.obj ⟨D.rightCone.coneDual.module, D.rightCone.coneDual.cofibrant⟩
  | _, _ => ⟨D.outerCone.coneDual.module, D.outerCone.coneDual.cofibrant⟩

/-- Diagram 6.6 in the common shift [1-n], with actual counit-cone fibres. -/
def shiftedNode (q : Grid) : DGDerivedModules k (enveloping P.Z P.Z) :=
  match q.1.val, q.2.val with
  | 0, 0 => ⟨D.outerCone.leftShift.module, D.outerCone.leftShift.cofibrant⟩
  | 0, 1 => D.I.induction.functor.obj ⟨D.leftCone.leftShift.module, D.leftCone.leftShift.cofibrant⟩
  | 0, 2 => D.I.induction.functor.obj (D.E.induction.functor.obj
      ⟨D.shiftedA.module, D.shiftedA.cofibrant⟩)
  | 1, 0 => D.J.induction.functor.obj ⟨D.rightCone.leftShift.module, D.rightCone.leftShift.cofibrant⟩
  | 1, 1 => D.M.induction.functor.obj ⟨D.shiftedB.module, D.shiftedB.cofibrant⟩
  | 1, 2 => D.I.induction.functor.obj ⟨D.leftCone.rightShift.module, D.leftCone.rightShift.cofibrant⟩
  | 2, 0 => D.J.induction.functor.obj (D.H.induction.functor.obj
      ⟨D.shiftedC.module, D.shiftedC.cofibrant⟩)
  | 2, 1 => D.J.induction.functor.obj ⟨D.rightCone.rightShift.module, D.rightCone.rightShift.cofibrant⟩
  | _, _ => ⟨D.outerCone.rightShift.module, D.outerCone.rightShift.cofibrant⟩

end ModuleData

/-- Transport changes only the displayed equal DG functor. -/
def castContext {A B : DGCat k} {S : NegativeTraceSystem k}
    {DA : CYCategoryData S A} {DB : CYCategoryData S B} {f g : A ⟶ B}
    (F : RelativeCYContext S f DA DB) (eq : f = g) : RelativeCYContext S g DA DB := eq ▸ F

/-- The actual induction functor is unchanged by that equality transport. -/
theorem castContext_induction {A B : DGCat k} {S : NegativeTraceSystem k}
    {DA : CYCategoryData S A} {DB : CYCategoryData S B} {f g : A ⟶ B}
    (F : RelativeCYContext S f DA DB) (eq : f = g) :
    (castContext F eq).induction.functor = F.induction.functor := by cases eq; rfl

namespace ModuleData

variable {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
  (D : ModuleData P S n)

/-- The same common B induction is transported along the actual cospan square. -/
def middleGJ : RelativeCYContext S (P.g ≫ P.j) D.DB D.DZ := castContext D.M P.square

/-- The six non-corner arrows on inverse duals use actual dual counits and their unit mates. -/
def dualCounitToInduced {A B : DGCat k} {DA : CYCategoryData S A} {DB : CYCategoryData S B}
    {f : A ⟶ B} (F : RelativeCYContext S f DA DB) :
    DB.inverse.replacement.module ⟶ (F.induction.functor.obj
      ⟨DA.inverse.replacement.module, DA.inverse.replacement.cofibrant⟩).obj :=
  F.dualCounit.map ≫ F.dualBaseChange.equivalence.inverse

end ModuleData

/-- Composition comparisons use the same native units and bar contexts at every vertex. -/
structure InductionData {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    (D : ModuleData P S n) where
  restrictionFI : RestrictionCompositionModel P.f P.i D.F.enveloping D.I.enveloping
    D.M.enveloping D.F.restriction D.I.restriction D.M.restriction
  FI : InductionCompositionModel D.F.induction D.I.induction D.M.induction restrictionFI
  restrictionGJ : RestrictionCompositionModel P.g P.j D.G.enveloping D.J.enveloping
    D.middleGJ.enveloping D.G.restriction D.J.restriction D.middleGJ.restriction
  GJ : InductionCompositionModel D.G.induction D.J.induction D.middleGJ.induction restrictionGJ

namespace InductionData

variable {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
  {D : ModuleData P S n} (K : InductionData D)

def middleIso (D : ModuleData P S n) (M : DGDerivedModules k (enveloping P.B P.B)) :
    (D.M.induction.functor.obj M).obj ≅ (D.middleGJ.induction.functor.obj M).obj :=
  eqToIso (congrArg (fun L => (L.obj M).obj) (castContext_induction D.M P.square).symm)

/-- M!B→I!X is the composition unit mate followed by the actual pushed F bar counit. -/
def topCounit : (pushedDiagonal D.M.induction D.DB.bar).obj ⟶
    (pushedDiagonal D.I.induction D.DX.bar).obj :=
  K.FI.map ⟨D.DB.bar.module, D.DB.bar.cofibrant⟩ ≫
    pushedModuleMap D.I.induction (pushedDiagonal D.F.induction D.DB.bar)
      ⟨D.DX.bar.module, D.DX.bar.cofibrant⟩ D.F.counit.map

/-- M!B→J!Y uses the same square transport and the G/J composition unit mate. -/
def leftCounit : (pushedDiagonal D.M.induction D.DB.bar).obj ⟶
    (pushedDiagonal D.J.induction D.DY.bar).obj :=
  (middleIso D ⟨D.DB.bar.module, D.DB.bar.cofibrant⟩).hom ≫
    K.GJ.map ⟨D.DB.bar.module, D.DB.bar.cofibrant⟩ ≫
      pushedModuleMap D.J.induction (pushedDiagonal D.G.induction D.DB.bar)
        ⟨D.DY.bar.module, D.DY.bar.cofibrant⟩ D.G.counit.map

end InductionData

/-- A coproduct split retains both actual inclusion contexts and their bar/adjunction mates. -/
structure CoproductSplitContext {A B X : DGCat k} {S : NegativeTraceSystem k}
    (P : DGCoproductModel A B) (f : A ⟶ X) (g : B ⟶ X) (U : CoproductFunctorModel P f g)
    (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (DP : CYCategoryData S P.category) (DX : CYCategoryData S X)
    (E : RelativeCYContext S f DA DX) (F : RelativeCYContext S g DB DX)
    (EF : RelativeCYContext S U.functor DP DX) where
  AInclusion : RelativeCYContext S P.inl DA DP
  BInclusion : RelativeCYContext S P.inr DB DP
  restrictionA : RestrictionCompositionModel P.inl U.functor AInclusion.enveloping EF.enveloping
    (castContext E U.inl_eq.symm).enveloping AInclusion.restriction EF.restriction
      (castContext E U.inl_eq.symm).restriction
  restrictionB : RestrictionCompositionModel P.inr U.functor BInclusion.enveloping EF.enveloping
    (castContext F U.inr_eq.symm).enveloping BInclusion.restriction EF.restriction
      (castContext F U.inr_eq.symm).restriction
  split : PushedDiagonalSplitModel P U.functor AInclusion.enveloping BInclusion.enveloping
    EF.enveloping (castContext E U.inl_eq.symm).enveloping (castContext F U.inr_eq.symm).enveloping
    AInclusion.restriction BInclusion.restriction EF.restriction
    (castContext E U.inl_eq.symm).restriction (castContext F U.inr_eq.symm).restriction
    EF.induction (castContext E U.inl_eq.symm).induction (castContext F U.inr_eq.symm).induction
    restrictionA restrictionB DA.bar DB.bar DP.bar AInclusion.barMap BInclusion.barMap

namespace CoproductSplitContext

variable {A B X : DGCat k} {S : NegativeTraceSystem k}
  {P : DGCoproductModel A B} {f : A ⟶ X} {g : B ⟶ X} {U : CoproductFunctorModel P f g}
  {DA : CYCategoryData S A} {DB : CYCategoryData S B}
  {DP : CYCategoryData S P.category} {DX : CYCategoryData S X}
  {E : RelativeCYContext S f DA DX} {F : RelativeCYContext S g DB DX}
  {EF : RelativeCYContext S U.functor DP DX}
  (K : CoproductSplitContext P f g U DA DB DP DX E F EF)

def inductionCastIso {A' B' : DGCat k} {DA' : CYCategoryData S A'} {DB' : CYCategoryData S B'}
    {f' g' : A' ⟶ B'} (F' : RelativeCYContext S f' DA' DB') (eq : f' = g')
    (M : DGDerivedModules k (enveloping A' A')) :
    (F'.induction.functor.obj M).obj ≅ ((castContext F' eq).induction.functor.obj M).obj :=
  eqToIso (congrArg (fun L => (L.obj M).obj) (castContext_induction F' eq).symm)

/-- The A projection is the inverse of the bar-inclusion split, then its native first projection. -/
def projectionA : (pushedDiagonal EF.induction DP.bar).obj ⟶ (pushedDiagonal E.induction DA.bar).obj :=
  K.split.equivalence.inverse ≫ K.split.sum.fst ≫
    (inductionCastIso E U.inl_eq.symm ⟨DA.bar.module, DA.bar.cofibrant⟩).inv

/-- The B projection is fixed by the same split and its native second projection. -/
def projectionB : (pushedDiagonal EF.induction DP.bar).obj ⟶ (pushedDiagonal F.induction DB.bar).obj :=
  K.split.equivalence.inverse ≫ K.split.sum.snd ≫
    (inductionCastIso F U.inr_eq.symm ⟨DB.bar.module, DB.bar.cofibrant⟩).inv

end CoproductSplitContext

/-- The source coproduct square operations are fixed on the native bar, shift and cone blocks.
Both second-summand signs are those of the biCartesian-square presentation. -/
structure CoproductSquareOperators {A B X : DGCat k} {S : NegativeTraceSystem k}
    {P : DGCoproductModel A B} {f : A ⟶ X} {g : B ⟶ X} {U : CoproductFunctorModel P f g}
    {DA : CYCategoryData S A} {DB : CYCategoryData S B}
    {DP : CYCategoryData S P.category} {DX : CYCategoryData S X}
    {E : RelativeCYContext S f DA DX} {F : RelativeCYContext S g DB DX}
    {EF : RelativeCYContext S U.functor DP DX}
    (K : CoproductSplitContext P f g U DA DB DP DX E F EF) (n : ℤ)
    (C : RelativeConeContext EF n)
    (SA : CofibrantShiftModel (⟨DA.bar.module, DA.bar.cofibrant⟩) (1 - n))
    (SB : CofibrantShiftModel (⟨DB.bar.module, DB.bar.cofibrant⟩) (1 - n)) where
  dualProjectionA : ModuleDualMapModel (pushedDiagonal EF.induction DP.bar)
    (pushedDiagonal E.induction DA.bar) K.projectionA EF.dualPush E.dualPush
  dualProjectionB : ModuleDualMapModel (pushedDiagonal EF.induction DP.bar)
    (pushedDiagonal F.induction DB.bar) K.projectionB EF.dualPush F.dualPush
  targetShiftA : CofibrantShiftModel (pushedDiagonal E.induction DA.bar) (1 - n)
  targetShiftB : CofibrantShiftModel (pushedDiagonal F.induction DB.bar) (1 - n)
  shiftUnitA : ShiftedInductionUnitModel E.induction (⟨DA.bar.module, DA.bar.cofibrant⟩)
    (1 - n) SA targetShiftA
  shiftUnitB : ShiftedInductionUnitModel F.induction (⟨DB.bar.module, DB.bar.cofibrant⟩)
    (1 - n) SB targetShiftB
  shiftA : InductionShiftModel E.induction (⟨DA.bar.module, DA.bar.cofibrant⟩)
    (1 - n) SA targetShiftA shiftUnitA
  shiftB : InductionShiftModel F.induction (⟨DB.bar.module, DB.bar.cofibrant⟩)
    (1 - n) SB targetShiftB shiftUnitB
  counitShiftA : ModuleShiftMapModel E.counit.map (1 - n)
    targetShiftA.toModuleShiftModel C.rightShift.toModuleShiftModel
  counitShiftB : ModuleShiftMapModel F.counit.map (1 - n)
    targetShiftB.toModuleShiftModel C.rightShift.toModuleShiftModel
  fibreA : C.leftShift.module ⟶ (E.induction.functor.obj ⟨SA.module, SA.cofibrant⟩).obj
  fibreB : C.leftShift.module ⟶ (F.induction.functor.obj ⟨SB.module, SB.cofibrant⟩).obj
  fibreA_eq : ∀ (x : X) (y : Xᵒᵖ) (r : ℤ),
    (moduleComponent (fibreA ≫ shiftA.map) (moduleIndex X X x y)).f r ≫
      (targetShiftA.valueIso (moduleIndex X X x y)).hom.f r ≫
      (((pushedDiagonal E.induction DA.bar).obj.toEnrichedFunctor.obj (moduleIndex X X x y)).shiftFunctorObjXIso
        (1 - n) r (r + 1 - n) (by omega)).hom =
      (C.leftShift.valueIso (moduleIndex X X x y)).hom.f r ≫
        ((C.coneCounit.module.toEnrichedFunctor.obj (moduleIndex X X x y)).shiftFunctorObjXIso
          (-n) r (r - n) (by omega)).hom ≫
        (C.coneCounit.valueIso (moduleIndex X X x y)).hom.f (r - n) ≫
        (CochainComplex.mappingCone.fst (moduleComponent EF.counit.map (moduleIndex X X x y))).val.v
          (r - n) (r + 1 - n) (by omega) ≫
        (moduleComponent K.projectionA (moduleIndex X X x y)).f (r + 1 - n)
  fibreB_eq : ∀ (x : X) (y : Xᵒᵖ) (r : ℤ),
    (moduleComponent (fibreB ≫ shiftB.map) (moduleIndex X X x y)).f r ≫
      (targetShiftB.valueIso (moduleIndex X X x y)).hom.f r ≫
      (((pushedDiagonal F.induction DB.bar).obj.toEnrichedFunctor.obj (moduleIndex X X x y)).shiftFunctorObjXIso
        (1 - n) r (r + 1 - n) (by omega)).hom =
      -( (C.leftShift.valueIso (moduleIndex X X x y)).hom.f r ≫
        ((C.coneCounit.module.toEnrichedFunctor.obj (moduleIndex X X x y)).shiftFunctorObjXIso
          (-n) r (r - n) (by omega)).hom ≫
        (C.coneCounit.valueIso (moduleIndex X X x y)).hom.f (r - n) ≫
        (CochainComplex.mappingCone.fst (moduleComponent EF.counit.map (moduleIndex X X x y))).val.v
          (r - n) (r + 1 - n) (by omega) ≫
        (moduleComponent K.projectionB (moduleIndex X X x y)).f (r + 1 - n))

namespace CoproductSquareOperators

variable {A B X : DGCat k} {S : NegativeTraceSystem k}
  {P : DGCoproductModel A B} {f : A ⟶ X} {g : B ⟶ X} {U : CoproductFunctorModel P f g}
  {DA : CYCategoryData S A} {DB : CYCategoryData S B}
  {DP : CYCategoryData S P.category} {DX : CYCategoryData S X}
  {E : RelativeCYContext S f DA DX} {F : RelativeCYContext S g DB DX}
  {EF : RelativeCYContext S U.functor DP DX}
  {K : CoproductSplitContext P f g U DA DB DP DX E F EF} {n : ℤ}
  {C : RelativeConeContext EF n}
  {SA : CofibrantShiftModel (⟨DA.bar.module, DA.bar.cofibrant⟩) (1 - n)}
  {SB : CofibrantShiftModel (⟨DB.bar.module, DB.bar.cofibrant⟩) (1 - n)}
  (O : CoproductSquareOperators K n C SA SB)

/-- The first dual summand enters the actual dual-counit cone by its normalized projection mate. -/
def dualA : (E.induction.functor.obj
    ⟨DA.inverse.replacement.module, DA.inverse.replacement.cofibrant⟩).obj ⟶ C.coneDual.module :=
  E.dualBaseChange.map ≫ O.dualProjectionA.map ≫ C.coneDual.inclusion

/-- The second dual summand has the source square's explicit minus sign. -/
def dualB : (F.induction.functor.obj
    ⟨DB.inverse.replacement.module, DB.inverse.replacement.cofibrant⟩).obj ⟶ C.coneDual.module :=
  moduleDifference
    ((DGFunctor.homEquivDGCycles k _ _).symm 0)
    (F.dualBaseChange.map ≫ O.dualProjectionB.map ≫ C.coneDual.inclusion)

/-- The source second-summand arrow is exactly native negation of its normalized dual-cone inclusion. -/
theorem dualB_eq_negated : O.dualB =
    negatedModuleMap (F.dualBaseChange.map ≫ O.dualProjectionB.map ≫ C.coneDual.inclusion) := by
  apply (DGFunctor.homEquivDGCycles k _ _).injective
  simp [dualB, moduleDifference, negatedModuleMap]

def shiftedCounitA : (E.induction.functor.obj ⟨SA.module, SA.cofibrant⟩).obj ⟶ C.rightShift.module :=
  O.shiftA.map ≫ O.counitShiftA.map

def shiftedCounitB : (F.induction.functor.obj ⟨SB.module, SB.cofibrant⟩).obj ⟶ C.rightShift.module :=
  O.shiftB.map ≫ O.counitShiftB.map

end CoproductSquareOperators

/-- The actual native functor-coherent counit square contains no CY class. -/
structure BarCounitSquare {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    (D : ModuleData P S n) (K : InductionData D) where
  comm : K.topCounit ≫ D.I.counit.map = K.leftCounit ≫ D.J.counit.map

/-- The source 6.1 square has the exact bar counits and zero strict-square cell. -/
def BarCounitSquare.square {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    {D : ModuleData P S n} {K : InductionData D} (B : BarCounitSquare D K) :
    ModuleHomotopySquare (enveloping P.Z P.Z) where
  topLeft := pushedDiagonal D.M.induction D.DB.bar
  topRight := pushedDiagonal D.I.induction D.DX.bar
  bottomLeft := pushedDiagonal D.J.induction D.DY.bar
  bottomRight := ⟨D.DZ.bar.module, D.DZ.bar.cofibrant⟩
  top := K.topCounit
  left := K.leftCounit
  right := D.I.counit.map
  bottom := D.J.counit.map
  cell := 0
  cell_boundary := by simp only [map_zero, B.comm, sub_self]

/-- Applying the actual representable-Hom left dual to the one source 6.1 total comparison. -/
structure DualCotangentComparison {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    {D : ModuleData P S n} {K : InductionData D} (B : BarCounitSquare D K)
    (Q : ModuleHomotopyPushout B.square) where
  coneDual : ModuleLeftDualModel P.Z (⟨Q.cone.module, Q.cone.cofibrant⟩)
  comparison : ModuleDualMapModel (⟨Q.cone.module, Q.cone.cofibrant⟩)
    (⟨D.DZ.bar.module, D.DZ.bar.cofibrant⟩) Q.comparison.map
    coneDual (MathlibExt.CategoryTheory.DGBimodulePushforwardModels.InverseDualModel.toModuleLeftDual D.DZ.inverse)
  equivalence : ModuleHomotopyEquivalence comparison.map

/-- The source composition, coproduct and shift operations contain no CY classes or nondegeneracy. -/
structure CospanOperations {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    (D : ModuleData P S n) where
  induction : InductionData D
  leftSplit : CoproductSplitContext D.AB P.e P.f D.leftFunctor
    D.DA D.DB D.DAB D.DX D.E D.F D.left
  rightSplit : CoproductSplitContext D.BC P.g P.h D.rightFunctor
    D.DB D.DC D.DBC D.DY D.G D.H D.right
  leftOperators : CoproductSquareOperators leftSplit n D.leftCone D.shiftedA D.shiftedB
  rightOperators : CoproductSquareOperators rightSplit n D.rightCone D.shiftedB D.shiftedC
  EA : RelativeCYContext S (P.e ≫ P.i) D.DA D.DZ
  HC : RelativeCYContext S (P.h ≫ P.j) D.DC D.DZ
  restrictionEI : RestrictionCompositionModel P.e P.i D.E.enveloping D.I.enveloping
    EA.enveloping D.E.restriction D.I.restriction EA.restriction
  restrictionHJ : RestrictionCompositionModel P.h P.j D.H.enveloping D.J.enveloping
    HC.enveloping D.H.restriction D.J.restriction HC.restriction
  EI : InductionCompositionModel D.E.induction D.I.induction EA.induction restrictionEI
  HJ : InductionCompositionModel D.H.induction D.J.induction HC.induction restrictionHJ
  outerSplit : CoproductSplitContext D.AC (P.e ≫ P.i) (P.h ≫ P.j) D.outerFunctor
    D.DA D.DC D.DAC D.DZ EA HC D.outer
  outerOperators : CoproductSquareOperators outerSplit n D.outerCone D.shiftedA D.shiftedC
  shiftedI : CofibrantShiftModel (pushedDiagonal D.I.induction D.DX.bar) (1 - n)
  shiftedJ : CofibrantShiftModel (pushedDiagonal D.J.induction D.DY.bar) (1 - n)
  unitI : ShiftedInductionUnitModel D.I.induction (⟨D.DX.bar.module, D.DX.bar.cofibrant⟩)
    (1 - n) D.leftCone.rightShift shiftedI
  unitJ : ShiftedInductionUnitModel D.J.induction (⟨D.DY.bar.module, D.DY.bar.cofibrant⟩)
    (1 - n) D.rightCone.rightShift shiftedJ
  shiftI : InductionShiftModel D.I.induction (⟨D.DX.bar.module, D.DX.bar.cofibrant⟩)
    (1 - n) D.leftCone.rightShift shiftedI unitI
  shiftJ : InductionShiftModel D.J.induction (⟨D.DY.bar.module, D.DY.bar.cofibrant⟩)
    (1 - n) D.rightCone.rightShift shiftedJ unitJ
  counitI : ModuleShiftMapModel D.I.counit.map (1 - n)
    shiftedI.toModuleShiftModel D.outerCone.rightShift.toModuleShiftModel
  counitJ : ModuleShiftMapModel D.J.counit.map (1 - n)
    shiftedJ.toModuleShiftModel D.outerCone.rightShift.toModuleShiftModel
  barSquare : BarCounitSquare D induction
  cotangentPushout : ModuleHomotopyPushout barSquare.square
  cotangentDual : DualCotangentComparison barSquare cotangentPushout

/-- The actual finite grid is lifted to the coefficient universe. -/
abbrev GridIndex : Type u := ULift.{u} ModuleData.Grid

local instance : DecidableLT ModuleData.Grid := decidableLTOfDecidableLE

/-- The twelve actual horizontal/vertical positions of the completed source grid. -/
inductive GridEdge
  | e00_01 | e00_10 | e01_02 | e01_11 | e10_11 | e10_20
  | e02_12 | e11_12 | e11_21 | e20_21 | e12_22 | e21_22
  deriving DecidableEq

def GridEdge.source : GridEdge → GridIndex
  | .e00_01 | .e00_10 => ⟨(0, 0)⟩
  | .e01_02 | .e01_11 => ⟨(0, 1)⟩
  | .e10_11 | .e10_20 => ⟨(1, 0)⟩
  | .e02_12 => ⟨(0, 2)⟩
  | .e11_12 | .e11_21 => ⟨(1, 1)⟩
  | .e20_21 => ⟨(2, 0)⟩
  | .e12_22 => ⟨(1, 2)⟩
  | .e21_22 => ⟨(2, 1)⟩

def GridEdge.target : GridEdge → GridIndex
  | .e00_01 => ⟨(0, 1)⟩
  | .e00_10 => ⟨(1, 0)⟩
  | .e01_02 => ⟨(0, 2)⟩
  | .e01_11 | .e10_11 => ⟨(1, 1)⟩
  | .e10_20 => ⟨(2, 0)⟩
  | .e02_12 | .e11_12 => ⟨(1, 2)⟩
  | .e11_21 | .e20_21 => ⟨(2, 1)⟩
  | .e12_22 | .e21_22 => ⟨(2, 2)⟩

def directGenerator (a b : GridIndex.{u}) (h : a < b) : Generator GridIndex a b 0 where
  vertices i := if i.val = 0 then a else b
  strict := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  first := rfl
  last := rfl

def GridEdge.generator (e : GridEdge) :
    Generator GridIndex.{u} (GridEdge.source.{u} e) (GridEdge.target.{u} e) 0 :=
  directGenerator (GridEdge.source.{u} e) (GridEdge.target.{u} e) (by
    apply ULift.down_lt.mp
    cases e <;> dsimp [GridEdge.source, GridEdge.target] <;> decide)

/-- A grid edge is the actual closed degree-zero image of its fixed index generator. -/
def coherentEdge {R : CoherentIndexModel k GridIndex} {C : DGCat k}
    (Q : CoherentDiagram R C) (e : GridEdge) :
    Q.toEnrichedFunctor.obj (R.objects.symm e.source) ⟶
      Q.toEnrichedFunctor.obj (R.objects.symm e.target) :=
  (DGFunctor.homEquivDGCycles k _ _).symm
    ⟨Q.toEnrichedFunctor.dgMap 0 (R.cell e.generator), (mem_dgCycles k).mpr
      (Q.toEnrichedFunctor.dgDifferential_dgMap_eq_zero (R.closed_arrow e.generator))⟩

/-- Transport changes only the displayed object equalities of the coherent diagram. -/
def edgeAtNodes {R : CoherentIndexModel k GridIndex} {C : DGCat k}
    (Q : CoherentDiagram R C) (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    (e : GridEdge) : (nodes e.source).obj ⟶ (nodes e.target).obj :=
  eqToHom (eq e.source).symm ≫ coherentEdge Q e ≫ eqToHom (eq e.target)

/-- The four interior unit/bar-normalized edges of diagram 6.7. -/
def CospanOperations.dualCoreEdge {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    {D : ModuleData P S n} (O : CospanOperations D) (e : GridEdge)
    (ordinary : e ≠ .e12_22 ∧ e ≠ .e21_22) :
    (D.dualNode e.source.down).obj ⟶ (D.dualNode e.target.down).obj := by
  cases e
  · exact ModuleData.dualCounitToInduced D.I
  · exact ModuleData.dualCounitToInduced D.J
  · exact pushedModuleMap D.I.induction _ _ (ModuleData.dualCounitToInduced D.E)
  · exact pushedModuleMap D.I.induction _ _ (ModuleData.dualCounitToInduced D.F) ≫
      (O.induction.FI.equivalence ⟨D.DB.inverse.replacement.module, D.DB.inverse.replacement.cofibrant⟩).inverse
  · exact pushedModuleMap D.J.induction _ _ (ModuleData.dualCounitToInduced D.G) ≫
      (O.induction.GJ.equivalence ⟨D.DB.inverse.replacement.module, D.DB.inverse.replacement.cofibrant⟩).inverse ≫
      (InductionData.middleIso D ⟨D.DB.inverse.replacement.module, D.DB.inverse.replacement.cofibrant⟩).inv
  · exact pushedModuleMap D.J.induction _ _ (ModuleData.dualCounitToInduced D.H)
  · exact pushedModuleMap D.I.induction _ _ O.leftOperators.dualA
  · exact O.induction.FI.map ⟨D.DB.inverse.replacement.module, D.DB.inverse.replacement.cofibrant⟩ ≫
      pushedModuleMap D.I.induction _ _ O.leftOperators.dualB
  · exact (InductionData.middleIso D ⟨D.DB.inverse.replacement.module, D.DB.inverse.replacement.cofibrant⟩).hom ≫
      O.induction.GJ.map ⟨D.DB.inverse.replacement.module, D.DB.inverse.replacement.cofibrant⟩ ≫
      pushedModuleMap D.J.induction _ _ O.rightOperators.dualA
  · exact pushedModuleMap D.J.induction _ _ O.rightOperators.dualB
  · exact False.elim (ordinary.1 rfl)
  · exact False.elim (ordinary.2 rfl)

/-- Diagram 6.6 uses the native fibre/summand maps and shifted bar counits. -/
def CospanOperations.shiftedCoreEdge {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    {D : ModuleData P S n} (O : CospanOperations D) (e : GridEdge)
    (ordinary : e ≠ .e00_01 ∧ e ≠ .e00_10) :
    (D.shiftedNode e.source.down).obj ⟶ (D.shiftedNode e.target.down).obj := by
  cases e
  · exact False.elim (ordinary.1 rfl)
  · exact False.elim (ordinary.2 rfl)
  · exact pushedModuleMap D.I.induction _ _ O.leftOperators.fibreA
  · exact pushedModuleMap D.I.induction _ _ O.leftOperators.fibreB ≫
      (O.induction.FI.equivalence ⟨D.shiftedB.module, D.shiftedB.cofibrant⟩).inverse
  · exact pushedModuleMap D.J.induction _ _ O.rightOperators.fibreA ≫
      (O.induction.GJ.equivalence ⟨D.shiftedB.module, D.shiftedB.cofibrant⟩).inverse ≫
      (InductionData.middleIso D ⟨D.shiftedB.module, D.shiftedB.cofibrant⟩).inv
  · exact pushedModuleMap D.J.induction _ _ O.rightOperators.fibreB
  · exact pushedModuleMap D.I.induction _ _ O.leftOperators.shiftedCounitA
  · exact O.induction.FI.map ⟨D.shiftedB.module, D.shiftedB.cofibrant⟩ ≫
      pushedModuleMap D.I.induction _ _ O.leftOperators.shiftedCounitB
  · exact (InductionData.middleIso D ⟨D.shiftedB.module, D.shiftedB.cofibrant⟩).hom ≫
      O.induction.GJ.map ⟨D.shiftedB.module, D.shiftedB.cofibrant⟩ ≫
      pushedModuleMap D.J.induction _ _ O.rightOperators.shiftedCounitA
  · exact pushedModuleMap D.J.induction _ _ O.rightOperators.shiftedCounitB
  · exact O.shiftI.map ≫ O.counitI.map
  · exact O.shiftJ.map ≫ O.counitJ.map

def chainGenerator (a b c : GridIndex.{u}) (hab : a < b) (hbc : b < c) :
    Generator GridIndex a c 1 where
  vertices i := if i.val = 0 then a else if i.val = 1 then b else c
  strict := by
    intro i j hij
    have hac := lt_trans hab hbc
    fin_cases i <;> fin_cases j <;> simp_all
  first := rfl
  last := rfl

/-- Every original index cochain is transported through the displayed node equalities. -/
def cochainAtNodes {R : CoherentIndexModel k GridIndex} {C : DGCat k}
    (Q : CoherentDiagram R C) (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    {a b : GridIndex} {m : ℕ} (g : Generator GridIndex a b m) :
    DGHom k (-(m : ℤ)) (nodes a).obj (nodes b).obj :=
  dgComp k (p := 0) (q := -(m : ℤ)) (n := -(m : ℤ)) (moduleCycle (eqToHom (eq a).symm))
    (dgComp k (p := -(m : ℤ)) (q := 0) (n := -(m : ℤ))
      (Q.toEnrichedFunctor.dgMap (-(m : ℤ)) (R.cell g))
      (moduleCycle (eqToHom (eq b))) (by omega)) (by omega)

def arrowAtNodes {R : CoherentIndexModel k GridIndex} {C : DGCat k}
    (Q : CoherentDiagram R C) (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    (a b : GridIndex) (hab : a < b) : (nodes a).obj ⟶ (nodes b).obj :=
  eqToHom (eq a).symm ≫
    (DGFunctor.homEquivDGCycles k _ _).symm
      ⟨Q.toEnrichedFunctor.dgMap 0 (R.cell (directGenerator a b hab)), (mem_dgCycles k).mpr
        (Q.toEnrichedFunctor.dgDifferential_dgMap_eq_zero
          (R.closed_arrow (directGenerator a b hab)))⟩ ≫ eqToHom (eq b)

inductive SmallSquare | upperLeft | upperRight | lowerLeft | lowerRight
  deriving DecidableEq

def SmallSquare.topLeft : SmallSquare → GridIndex
  | .upperLeft => ⟨(0, 0)⟩
  | .upperRight => ⟨(0, 1)⟩
  | .lowerLeft => ⟨(1, 0)⟩
  | .lowerRight => ⟨(1, 1)⟩

def SmallSquare.topRight : SmallSquare → GridIndex
  | .upperLeft => ⟨(0, 1)⟩
  | .upperRight => ⟨(0, 2)⟩
  | .lowerLeft => ⟨(1, 1)⟩
  | .lowerRight => ⟨(1, 2)⟩

def SmallSquare.bottomLeft : SmallSquare → GridIndex
  | .upperLeft => ⟨(1, 0)⟩
  | .upperRight => ⟨(1, 1)⟩
  | .lowerLeft => ⟨(2, 0)⟩
  | .lowerRight => ⟨(2, 1)⟩

def SmallSquare.bottomRight : SmallSquare → GridIndex
  | .upperLeft => ⟨(1, 1)⟩
  | .upperRight => ⟨(1, 2)⟩
  | .lowerLeft => ⟨(2, 1)⟩
  | .lowerRight => ⟨(2, 2)⟩

theorem SmallSquare.top_lt (s : SmallSquare) : SmallSquare.topLeft.{u} s < SmallSquare.topRight.{u} s := by
  apply ULift.down_lt.mp
  cases s <;> dsimp [SmallSquare.topLeft, SmallSquare.topRight] <;> decide

theorem SmallSquare.left_lt (s : SmallSquare) : SmallSquare.topLeft.{u} s < SmallSquare.bottomLeft.{u} s := by
  apply ULift.down_lt.mp
  cases s <;> dsimp [SmallSquare.topLeft, SmallSquare.bottomLeft] <;> decide

theorem SmallSquare.right_lt (s : SmallSquare) : SmallSquare.topRight.{u} s < SmallSquare.bottomRight.{u} s := by
  apply ULift.down_lt.mp
  cases s <;> dsimp [SmallSquare.topRight, SmallSquare.bottomRight] <;> decide

theorem SmallSquare.bottom_lt (s : SmallSquare) : SmallSquare.bottomLeft.{u} s < SmallSquare.bottomRight.{u} s := by
  apply ULift.down_lt.mp
  cases s <;> dsimp [SmallSquare.bottomLeft, SmallSquare.bottomRight] <;> decide

/-- A square cell is the signed difference of its two actual length-two index chains. -/
def squareCell {R : CoherentIndexModel k GridIndex} {C : DGCat k}
    (Q : CoherentDiagram R C) (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    (s : SmallSquare) : DGHom k (-1) (nodes s.topLeft).obj (nodes s.bottomRight).obj :=
  cochainAtNodes Q nodes eq (chainGenerator s.topLeft s.bottomLeft s.bottomRight s.left_lt s.bottom_lt) -
    cochainAtNodes Q nodes eq (chainGenerator s.topLeft s.topRight s.bottomRight s.top_lt s.right_lt)

/-- Only the native index differential identity is a proof dependency in forming a square. -/
structure CoherentSquareModel {R : CoherentIndexModel k GridIndex} {C : DGCat k}
    (Q : CoherentDiagram R C) (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    (s : SmallSquare) where
  boundary : dgDifferential k (-1) (squareCell Q nodes eq s) =
    moduleCycle (arrowAtNodes Q nodes eq s.topLeft s.topRight s.top_lt ≫
      arrowAtNodes Q nodes eq s.topRight s.bottomRight s.right_lt) -
    moduleCycle (arrowAtNodes Q nodes eq s.topLeft s.bottomLeft s.left_lt ≫
      arrowAtNodes Q nodes eq s.bottomLeft s.bottomRight s.bottom_lt)

def CoherentSquareModel.square {R : CoherentIndexModel k GridIndex} {C : DGCat k}
    {Q : CoherentDiagram R C} {nodes : GridIndex → DGDerivedModules k C}
    {eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj}
    {s : SmallSquare} (H : CoherentSquareModel Q nodes eq s) : ModuleHomotopySquare C where
  topLeft := nodes s.topLeft
  topRight := nodes s.topRight
  bottomLeft := nodes s.bottomLeft
  bottomRight := nodes s.bottomRight
  top := arrowAtNodes Q nodes eq s.topLeft s.topRight s.top_lt
  left := arrowAtNodes Q nodes eq s.topLeft s.bottomLeft s.left_lt
  right := arrowAtNodes Q nodes eq s.topRight s.bottomRight s.right_lt
  bottom := arrowAtNodes Q nodes eq s.bottomLeft s.bottomRight s.bottom_lt
  cell := squareCell Q nodes eq s
  cell_boundary := H.boundary

/-- The completed diagrams are one pair of actual coherent DG diagrams.
The corner arrows are outputs of their universal cone completion, with the
outer relative cone edges fixed by bar projections and native induction mates.
No separate arbitrary I!cofX→cofZ or J!cofY→cofZ callback is an input. -/
structure CompletedCospanDiagrams {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    {D : ModuleData P S n} (O : CospanOperations D) where
  index : CoherentIndexModel k GridIndex
  dual : CoherentDiagram index (enveloping P.Z P.Z)
  shifted : CoherentDiagram index (enveloping P.Z P.Z)
  dualObjects : ∀ q : GridIndex, dual.toEnrichedFunctor.obj (index.objects.symm q) = (D.dualNode q.down).obj
  shiftedObjects : ∀ q : GridIndex,
    shifted.toEnrichedFunctor.obj (index.objects.symm q) = (D.shiftedNode q.down).obj
  dualEdges : ∀ (e : GridEdge) (h : e ≠ .e12_22 ∧ e ≠ .e21_22),
    edgeAtNodes dual (fun q => D.dualNode q.down) dualObjects e = O.dualCoreEdge e h
  shiftedEdges : ∀ (e : GridEdge) (h : e ≠ .e00_01 ∧ e ≠ .e00_10),
    edgeAtNodes shifted (fun q => D.shiftedNode q.down) shiftedObjects e = O.shiftedCoreEdge e h
  outerDualA : arrowAtNodes dual (fun q => D.dualNode q.down) dualObjects ⟨(0, 0)⟩ ⟨(0, 2)⟩ (ULift.down_lt.mp (by decide)) =
    ModuleData.dualCounitToInduced O.EA ≫ O.EI.map
      ⟨D.DA.inverse.replacement.module, D.DA.inverse.replacement.cofibrant⟩
  outerDualC : arrowAtNodes dual (fun q => D.dualNode q.down) dualObjects ⟨(0, 0)⟩ ⟨(2, 0)⟩ (ULift.down_lt.mp (by decide)) =
    ModuleData.dualCounitToInduced O.HC ≫ O.HJ.map
      ⟨D.DC.inverse.replacement.module, D.DC.inverse.replacement.cofibrant⟩
  outerDualACone : arrowAtNodes dual (fun q => D.dualNode q.down) dualObjects ⟨(0, 2)⟩ ⟨(2, 2)⟩ (ULift.down_lt.mp (by decide)) =
    (O.EI.equivalence ⟨D.DA.inverse.replacement.module, D.DA.inverse.replacement.cofibrant⟩).inverse ≫
      O.outerOperators.dualA
  outerDualCCone : arrowAtNodes dual (fun q => D.dualNode q.down) dualObjects ⟨(2, 0)⟩ ⟨(2, 2)⟩ (ULift.down_lt.mp (by decide)) =
    (O.HJ.equivalence ⟨D.DC.inverse.replacement.module, D.DC.inverse.replacement.cofibrant⟩).inverse ≫
      O.outerOperators.dualB
  outerFibreA : arrowAtNodes shifted (fun q => D.shiftedNode q.down) shiftedObjects ⟨(0, 0)⟩ ⟨(0, 2)⟩ (ULift.down_lt.mp (by decide)) =
    O.outerOperators.fibreA ≫ O.EI.map ⟨D.shiftedA.module, D.shiftedA.cofibrant⟩
  outerFibreC : arrowAtNodes shifted (fun q => D.shiftedNode q.down) shiftedObjects ⟨(0, 0)⟩ ⟨(2, 0)⟩ (ULift.down_lt.mp (by decide)) =
    O.outerOperators.fibreB ≫ O.HJ.map ⟨D.shiftedC.module, D.shiftedC.cofibrant⟩
  outerCounitA : arrowAtNodes shifted (fun q => D.shiftedNode q.down) shiftedObjects ⟨(0, 2)⟩ ⟨(2, 2)⟩ (ULift.down_lt.mp (by decide)) =
    (O.EI.equivalence ⟨D.shiftedA.module, D.shiftedA.cofibrant⟩).inverse ≫ O.outerOperators.shiftedCounitA
  outerCounitC : arrowAtNodes shifted (fun q => D.shiftedNode q.down) shiftedObjects ⟨(2, 0)⟩ ⟨(2, 2)⟩ (ULift.down_lt.mp (by decide)) =
    (O.HJ.equivalence ⟨D.shiftedC.module, D.shiftedC.cofibrant⟩).inverse ≫ O.outerOperators.shiftedCounitB
  dualSquares : ∀ s : SmallSquare, CoherentSquareModel dual (fun q => D.dualNode q.down) dualObjects s
  shiftedSquares : ∀ s : SmallSquare,
    CoherentSquareModel shifted (fun q => D.shiftedNode q.down) shiftedObjects s
  dualPushout : ∀ s : SmallSquare, ModuleHomotopyPushout (dualSquares s).square
  shiftedPushout : ∀ s : SmallSquare, ModuleHomotopyPushout (shiftedSquares s).square
  dualPullback : ∀ s : SmallSquare, ModuleHomotopyPullback (dualSquares s).square
  shiftedPullback : ∀ s : SmallSquare, ModuleHomotopyPullback (shiftedSquares s).square
  cotangentCell : squareCell shifted (fun q => D.shiftedNode q.down) shiftedObjects .lowerRight = 0

end MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger
