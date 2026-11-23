/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.CategoryUniverseLift
public import MathlibExt.Algebra.Category.FGProjectiveCat.CategoryUniverseLiftZero
public import MathlibExt.KTheory.Exact.Quillen.Equivalence
public import MathlibExt.KTheory.Exact.Quillen.KSpaceTop
public import MathlibExt.KTheory.Exact.Quillen.ZeroCoherence
public import MathlibExt.KTheory.Exact.Quillen.SpanUnderlyingIsoNaturality
public import MathlibExt.KTheory.Exact.Extension.BasedSplitExactQLoopComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveLiftRealization
public import MathlibExt.CategoryTheory.NerveHomotopyRealization
public import MathlibExt.Topology.Category.TopCat.CofibrantPointTraceRetuning
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedObjectEqualityEdge
public import MathlibExt.Topology.Homotopy.StrictLoopMap
public import MathlibExt.Topology.Homotopy.PointRelativeComposition
public import MathlibExt.Topology.Homotopy.BasedLoopCWType
public import MathlibExt.Topology.Homotopy.WeaklyPointedMap
public import MathlibExt.Topology.Category.TopCat.TrivialCofibrationExtension
public import MathlibExt.Topology.Category.TopCat.WeakHomotopyEquivalenceHomotopy
public import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration
public import MathlibExt.Topology.CWComplex.BasedWhitehead
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import MathlibExt.Topology.Homotopy.LoopComponents
public import MathlibExt.KTheory.Exact.Extension.OriginalQK0ComparisonCompatibility
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct

/-!
# Original Quillen categories and native loop carriers under a universe lift

The actual projective category and its category lift are related by the
canonical exact equivalence. The induced Quillen functors retain their
original object and span maps. Native loop carriers use the original
realization with a literal carrier lift. Its projection and inclusion act
by postcomposition at every path parameter and preserve the constant loops.

The based native Q descent and inclusion are constructed by independent
homotopy extensions of the actual realized category maps along their original
chosen-zero paths. NativeRealizationData retains both complete traces. The
actual unit/counit cylinders and their zero-edge comparisons provide the null
traces from which both point-relative inverse families are derived.

QdownRetuningHomotopy and QupRetuningHomotopy are jointly continuous families
on the entire original loop spaces, comparing the based retunings with the
original weakly pointed Q maps. A weakly pointed map sends the constant loop
to the canonical padded backtrack along its zero path. The based retunings
have the strict constant-loop equations stated below.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra
open CategoryTheory.ExactCategory
open CategoryTheory.Limits
open AlgebraicKTheory.OriginalQK0Comparison
open scoped ContinuousMap Topology Simplicial TopCat.modelCategory ZeroObject

universe uR uM uObj uHom uNative

namespace AlgebraicKTheory.QuillenUniverseLift

universe uS uLift

private theorem liftedRealizedVertexCofibration
    (K : SSet.{uS}) (x : K _⦋0⦌) :
    Cofibration (TopCat.const (ULift.up (SSet.realizedVertex x)) :
      TopCat.of PUnit.{max uS uLift + 1} ⟶
        TopCat.uliftFunctor.{uLift, uS}.obj (SSet.toTop.obj K)) := by
  let L := SSet.uliftFunctor.{uLift, uS}
  let e := SSet.toTopULiftIso.{uS, uLift}.app K
  let y := SSet.realizedVertex (X := L.obj K) (ULift.up x)
  let p : TopCat.of PUnit.{max uS uLift + 1} ⟶ SSet.toTop.obj (L.obj K) :=
    TopCat.const y
  letI : Cofibration p := SSet.realizedVertex_pointMap_cofibration (L.obj K) (ULift.up x)
  have hp : (TopCat.const (ULift.up (SSet.realizedVertex x)) :
      TopCat.of PUnit.{max uS uLift + 1} ⟶
        TopCat.uliftFunctor.{uLift, uS}.obj (SSet.toTop.obj K)) = p ≫ e.hom := by
    apply TopCat.ext
    intro _
    exact (SSet.toTopULiftIso_hom_realizedVertex.{uS, uLift} K x).symm
  rw [hp]
  infer_instance

universe uC vC uD vD

section ActualZeroSpans

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- An exact functor sends the original zero-apex span to the same target
span after the actual mapped-zero-to-chosen-zero isomorphism. -/
private theorem mapZeroMonoHomPrivate (F : C ⥤ D) [F.Additive] [F.IsExact] (A : C) :
    (QuillenQ.map F).map (ExtensionCategory.zeroMonoHom A) =
      (QuillenQ.zeroComparisonIso F).hom ≫
        ExtensionCategory.zeroMonoHom (F.obj A) := by
  let S := QuillenSpan.map F (ExtensionCategory.zeroMonoSpan A)
  let T := ExtensionCategory.zeroMonoSpan (F.obj A)
  have hl : F.mapZeroObject.hom ≫ T.l = S.l ≫ F.mapZeroObject.hom := by
    change F.mapZeroObject.hom ≫ (𝟙 (0 : D)) =
      F.map (𝟙 (0 : C)) ≫ F.mapZeroObject.hom
    rw [F.map_id, Category.comp_id, Category.id_comp]
  have hr : F.mapZeroObject.hom ≫ T.r = S.r ≫ (Iso.refl (F.obj A)).hom := by
    change F.mapZeroObject.hom ≫ (0 : (0 : D) ⟶ F.obj A) =
      F.map (0 : (0 : C) ⟶ A) ≫ (𝟙 (F.obj A))
    simp only [Functor.map_zero, comp_zero, zero_comp]
  have h := QuillenQ.mkHom_naturality_of_span_iso S T F.mapZeroObject
    (Iso.refl (F.obj A)) F.mapZeroObject hl hr
  have hSpan :
      (QuillenQ.mkHom S : (⟨F.obj (0 : C)⟩ : QuillenQ D) ⟶ ⟨F.obj A⟩) =
        (QuillenQ.underlyingIso F.mapZeroObject).hom ≫ QuillenQ.mkHom T := by
    simpa only [QuillenQ.underlyingIso_refl, Iso.refl_hom, Category.comp_id] using h
  exact (QuillenQ.map_mk F (X := ⟨0⟩) (Y := ⟨A⟩)
    (ExtensionCategory.zeroMonoSpan A)).trans hSpan

/-- The original object-apex zero span obeys the same actual zero-isomorphism
square, in independently sized source and target categories. -/
private theorem mapZeroEpiHomPrivate (F : C ⥤ D) [F.Additive] [F.IsExact] (A : C) :
    (QuillenQ.map F).map (ExtensionCategory.zeroEpiHom A) =
      (QuillenQ.zeroComparisonIso F).hom ≫
        ExtensionCategory.zeroEpiHom (F.obj A) := by
  let S := QuillenSpan.map F (ExtensionCategory.zeroEpiSpan A)
  let T := ExtensionCategory.zeroEpiSpan (F.obj A)
  have hl : (Iso.refl (F.obj A)).hom ≫ T.l = S.l ≫ F.mapZeroObject.hom := by
    change (𝟙 (F.obj A)) ≫ (0 : F.obj A ⟶ (0 : D)) =
      F.map (0 : A ⟶ (0 : C)) ≫ F.mapZeroObject.hom
    simp only [Category.id_comp, Functor.map_zero, zero_comp]
  have hr : (Iso.refl (F.obj A)).hom ≫ T.r = S.r ≫ (Iso.refl (F.obj A)).hom := by
    change (𝟙 (F.obj A)) ≫ (𝟙 (F.obj A)) =
      F.map (𝟙 A) ≫ (𝟙 (F.obj A))
    rw [F.map_id]
  have h := QuillenQ.mkHom_naturality_of_span_iso S T F.mapZeroObject
    (Iso.refl (F.obj A)) (Iso.refl (F.obj A)) hl hr
  have hSpan :
      (QuillenQ.mkHom S : (⟨F.obj (0 : C)⟩ : QuillenQ D) ⟶ ⟨F.obj A⟩) =
        (QuillenQ.underlyingIso F.mapZeroObject).hom ≫ QuillenQ.mkHom T := by
    simpa only [QuillenQ.underlyingIso_refl, Iso.refl_hom, Category.comp_id] using h
  exact (QuillenQ.map_mk F (X := ⟨0⟩) (Y := ⟨A⟩)
    (ExtensionCategory.zeroEpiSpan A)).trans hSpan

end ActualZeroSpans

section ActualEquivalenceZeroTriangles

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- Application preserves the actual functor-equality transport, by equality elimination. -/
private theorem natIsoTransportAppHEq
    {A : Type uC} [Category.{vC} A] {B : Type uD} [Category.{vD} B]
    {F F' G G' : A ⥤ B} (hF : F = F') (hG : G = G')
    (e : F ≅ G) (x : A) :
    HEq (((eqToIso hF).symm ≪≫ e ≪≫ eqToIso hG).hom.app x) (e.hom.app x) := by
  cases hF
  cases hG
  have hFRefl : (eqToIso (rfl : F = F)).symm = Iso.refl F :=
    (congrArg (fun i : F ≅ F => i.symm)
      (eqToIso_refl (rfl : F = F))).trans (Iso.refl_symm F)
  have hGRefl : eqToIso (rfl : G = G) = Iso.refl G :=
    eqToIso_refl (rfl : G = G)
  have hRight : e ≪≫ eqToIso (rfl : G = G) = e :=
    (congrArg (fun i : G ≅ G => e ≪≫ i) hGRefl).trans (Iso.trans_refl e)
  have hWhole :
      (eqToIso (rfl : F = F)).symm ≪≫ e ≪≫ eqToIso (rfl : G = G) = e :=
    (congrArg (fun i : F ≅ F => i ≪≫ (e ≪≫ eqToIso (rfl : G = G))) hFRefl).trans
      ((Iso.refl_trans (e ≪≫ eqToIso (rfl : G = G))).trans hRight)
  exact heq_of_eq (congrArg (fun i : F ≅ G => i.hom.app x) hWhole)

/-- The original inverse-unit transformation, before any adjointification. -/
private def actualQUnitInverse (E : C ≌ D)
    [E.functor.Additive] [E.inverse.Additive]
    [E.functor.IsExact] [E.inverse.IsExact] :
    QuillenQ.map E.functor ⋙ QuillenQ.map E.inverse ≅ 𝟭 (QuillenQ C) :=
  (eqToIso (QuillenQ.map_comp E.functor E.inverse)).symm ≪≫
    QuillenQ.mapNatIso (E.functor ⋙ E.inverse) (𝟭 C) E.unitIso.symm ≪≫
      eqToIso QuillenQ.map_id

/-- The original counit transformation, with the actual Q functor transports. -/
private def actualQCounit (E : C ≌ D)
    [E.functor.Additive] [E.inverse.Additive]
    [E.functor.IsExact] [E.inverse.IsExact] :
    QuillenQ.map E.inverse ⋙ QuillenQ.map E.functor ≅ 𝟭 (QuillenQ D) :=
  (eqToIso (QuillenQ.map_comp E.inverse E.functor)).symm ≪≫
    QuillenQ.mapNatIso (E.inverse ⋙ E.functor) (𝟭 D) E.counitIso ≪≫
      eqToIso QuillenQ.map_id

/-- The up/down zero composite is the lifted original inverse-unit component.
The equality is proved in the exact categories through zero-comparison
naturality; it does not assert that the Q zero object is categorically zero. -/
private theorem actualQUnitZeroComposite (E : C ≌ D)
    [E.functor.Additive] [E.inverse.Additive]
    [E.functor.IsExact] [E.inverse.IsExact] :
    ((QuillenQ.map E.inverse).mapIso
        (QuillenQ.zeroComparisonIso E.functor)).trans
        (QuillenQ.zeroComparisonIso E.inverse) =
      (QuillenQ.mapNatIso (E.functor ⋙ E.inverse) (𝟭 C)
        E.unitIso.symm).app (⟨0⟩ : QuillenQ C) := by
  have hNatural := QuillenQ.zeroComparisonIso_naturality
    (E.functor ⋙ E.inverse) (𝟭 C) E.unitIso.symm
  have hUnit :
      (QuillenQ.mapNatIso (E.functor ⋙ E.inverse) (𝟭 C)
        E.unitIso.symm).app (⟨0⟩ : QuillenQ C) =
        QuillenQ.zeroComparisonIso (E.functor ⋙ E.inverse) := by
    let q0 : QuillenQ C := ⟨0⟩
    let beta := (QuillenQ.mapNatIso (E.functor ⋙ E.inverse) (𝟭 C) E.unitIso.symm).app q0
    have hCleanup : beta ≪≫ QuillenQ.zeroComparisonIso (𝟭 C) = beta :=
      (congrArg (fun z : q0 ≅ q0 => beta ≪≫ z)
        (QuillenQ.zeroComparisonIso_id (C := C))).trans (Iso.trans_refl beta)
    exact hCleanup.symm.trans hNatural
  exact (QuillenQ.zeroComparisonIso_comp E.functor E.inverse).symm.trans hUnit.symm

/-- The down/up zero composite is the lifted original counit component. -/
private theorem actualQCounitZeroComposite (E : C ≌ D)
    [E.functor.Additive] [E.inverse.Additive]
    [E.functor.IsExact] [E.inverse.IsExact] :
    ((QuillenQ.map E.functor).mapIso
        (QuillenQ.zeroComparisonIso E.inverse)).trans
        (QuillenQ.zeroComparisonIso E.functor) =
      (QuillenQ.mapNatIso (E.inverse ⋙ E.functor) (𝟭 D)
        E.counitIso).app (⟨0⟩ : QuillenQ D) := by
  have hNatural := QuillenQ.zeroComparisonIso_naturality
    (E.inverse ⋙ E.functor) (𝟭 D) E.counitIso
  have hCounit :
      (QuillenQ.mapNatIso (E.inverse ⋙ E.functor) (𝟭 D)
        E.counitIso).app (⟨0⟩ : QuillenQ D) =
        QuillenQ.zeroComparisonIso (E.inverse ⋙ E.functor) := by
    let q0 : QuillenQ D := ⟨0⟩
    let beta := (QuillenQ.mapNatIso (E.inverse ⋙ E.functor) (𝟭 D) E.counitIso).app q0
    have hCleanup : beta ≪≫ QuillenQ.zeroComparisonIso (𝟭 D) = beta :=
      (congrArg (fun z : q0 ≅ q0 => beta ≪≫ z)
        (QuillenQ.zeroComparisonIso_id (C := D))).trans (Iso.trans_refl beta)
    exact hCleanup.symm.trans hNatural
  exact (QuillenQ.zeroComparisonIso_comp E.inverse E.functor).symm.trans hCounit.symm

/-- The functor-equality transports leave the original zero component intact. -/
private theorem actualQUnitInverse_zero (E : C ≌ D)
    [E.functor.Additive] [E.inverse.Additive]
    [E.functor.IsExact] [E.inverse.IsExact] :
    (QuillenQ.map E.inverse).map (QuillenQ.zeroComparisonIso E.functor).hom ≫
        (QuillenQ.zeroComparisonIso E.inverse).hom =
      (actualQUnitInverse E).hom.app (⟨0⟩ : QuillenQ C) := by
  have h := congrArg (fun e => e.hom) (actualQUnitZeroComposite E)
  have hComponent :
      (actualQUnitInverse E).hom.app (⟨0⟩ : QuillenQ C) =
        (QuillenQ.mapNatIso (E.functor ⋙ E.inverse) (𝟭 C)
          E.unitIso.symm).hom.app (⟨0⟩ : QuillenQ C) := by
    exact eq_of_heq (natIsoTransportAppHEq
      (QuillenQ.map_comp E.functor E.inverse) (QuillenQ.map_id (C := C))
      (QuillenQ.mapNatIso (E.functor ⋙ E.inverse) (𝟭 C) E.unitIso.symm)
      (⟨0⟩ : QuillenQ C))
  exact h.trans hComponent.symm

/-- The reverse functor-equality transports preserve the original counit zero component. -/
private theorem actualQCounit_zero (E : C ≌ D)
    [E.functor.Additive] [E.inverse.Additive]
    [E.functor.IsExact] [E.inverse.IsExact] :
    (QuillenQ.map E.functor).map (QuillenQ.zeroComparisonIso E.inverse).hom ≫
        (QuillenQ.zeroComparisonIso E.functor).hom =
      (actualQCounit E).hom.app (⟨0⟩ : QuillenQ D) := by
  have h := congrArg (fun e => e.hom) (actualQCounitZeroComposite E)
  have hComponent :
      (actualQCounit E).hom.app (⟨0⟩ : QuillenQ D) =
        (QuillenQ.mapNatIso (E.inverse ⋙ E.functor) (𝟭 D)
          E.counitIso).hom.app (⟨0⟩ : QuillenQ D) := by
    exact eq_of_heq (natIsoTransportAppHEq
      (QuillenQ.map_comp E.inverse E.functor) (QuillenQ.map_id (C := D))
      (QuillenQ.mapNatIso (E.inverse ⋙ E.functor) (𝟭 D) E.counitIso)
      (⟨0⟩ : QuillenQ D))
  exact h.trans hComponent.symm

end ActualEquivalenceZeroTriangles


section RetunedCompositionTrace

universe uTraceSource uTraceTarget

variable {X : Type uTraceSource} {Y : Type uTraceTarget}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Independently retuning the two original maps retains the actual composite
zero trace. After comparison with the original inverse homotopy's trace, the
resulting inverse family has a genuinely null marked-point trace. -/
private theorem retunedCompositionNullTrace
    (x : X) (y : Y) (fd d : C(X, Y)) (fu u : C(Y, X))
    (hd : d x = y) (hu : u y = x)
    (pd : _root_.Path (fd x) y) (pu : _root_.Path (fu y) x)
    (Hd : ContinuousMap.Homotopy fd d) (Hu : ContinuousMap.Homotopy fu u)
    (hDownTrace : ∀ t : unitInterval, Hd (t, x) = pd t)
    (hUpTrace : ∀ t : unitInterval, Hu (t, y) = pu t)
    (H0 : ContinuousMap.Homotopy (fu.comp fd) (ContinuousMap.id X))
    (hCanonical : ((pd.map fu.continuous).trans pu).Homotopic (H0.evalAt x)) :
    ∃ H : ContinuousMap.Homotopy (u.comp d) (ContinuousMap.id X),
      ((H.evalAt x).cast ((congrArg u hd).trans hu).symm rfl).Homotopic
        (_root_.Path.refl x) := by
  let A := (ContinuousMap.Homotopy.refl fu).comp Hd
  let B := Hu.compContinuousMap d
  let T := A.trans B
  let p := (pd.map fu.continuous).trans pu
  have hA (t : unitInterval) : A (t, x) = (pd.map fu.continuous) t := by
    change fu (Hd (t, x)) = fu (pd t)
    exact congrArg fu (hDownTrace t)
  have hB (t : unitInterval) : B (t, x) = pu t := by
    change Hu (t, d x) = pu t
    exact (congrArg (fun z => Hu (t, z)) hd).trans (hUpTrace t)
  have hT (t : unitInterval) : T (t, x) = p t := by
    change (A.trans B) (t, x) = ((pd.map fu.continuous).trans pu) t
    rw [ContinuousMap.Homotopy.trans_apply, _root_.Path.trans_apply]
    split_ifs with h
    · exact hA _
    · exact hB _
  let H := T.symm.trans H0
  have hPoint : (u.comp d) x = x := (congrArg u hd).trans hu
  have hReverse (t : unitInterval) : T.symm (t, x) = p.symm t := by
    exact hT (unitInterval.symm t)
  have hTrace :
      (H.evalAt x).cast hPoint.symm rfl = p.symm.trans (H0.evalAt x) := by
    apply _root_.Path.ext
    funext t
    change (T.symm.trans H0) (t, x) = (p.symm.trans (H0.evalAt x)) t
    rw [ContinuousMap.Homotopy.trans_apply, _root_.Path.trans_apply]
    split_ifs with h
    · exact hReverse _
    · rfl
  obtain ⟨Hcanonical⟩ := hCanonical
  let K : (p.symm.trans (H0.evalAt x)).Homotopy (_root_.Path.refl x) :=
    ((_root_.Path.Homotopy.refl p.symm).hcomp Hcanonical.symm).trans
      (_root_.Path.Homotopy.reflSymmTrans p).symm
  exact ⟨H, ⟨_root_.Path.Homotopy.cast K hTrace.symm rfl⟩⟩

end RetunedCompositionTrace

section WholeLoopRetuning

universe uLoopSource uLoopTarget

variable {X : Type uLoopSource} {Y : Type uLoopTarget}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- A retained point trace gives a joint loop-space homotopy to the original
weakly pointed map. The endpoint map is the actual strict postcomposition
map specified by its value formula, not a newly selected inverse. -/
private def loopRetuningHomotopy {x : X} {y : Y}
    (f : ContinuousMap.WeaklyPointed x y) (d : C(X, Y)) (hd : d x = y)
    (H : ContinuousMap.Homotopy f.hom d)
    (hTrace : ∀ t : unitInterval, H (t, x) = f.rootPath t)
    (k : C(LoopSpace X x, LoopSpace Y y))
    (hMap : ∀ (gamma : LoopSpace X x) (t : unitInterval), k gamma t = d (gamma t)) :
    ContinuousMap.Homotopy f.loopMap k := by
  subst y
  have hRoot : H.evalAt x = f.rootPath := by
    apply _root_.Path.ext
    funext t
    exact hTrace t
  let K := ContinuousMap.Homotopy.traceConjugationLoopHomotopy H x
  have hSource :
      (ContinuousMap.loopBasepointChange (H.evalAt x)).comp
          (ContinuousMap.strictLoopMap f.hom x) = f.loopMap :=
    (congrArg (fun p : _root_.Path (f.hom x) (d x) =>
      (ContinuousMap.loopBasepointChange p).comp
        (ContinuousMap.strictLoopMap f.hom x)) hRoot).trans
      (ContinuousMap.WeaklyPointed.loopMap_eq_loopBasepointChange_comp_strictLoopMap f).symm
  have hTarget : ContinuousMap.strictLoopMap d x = k := by
    apply ContinuousMap.ext
    intro gamma
    apply _root_.Path.ext
    funext t
    exact (hMap gamma t).symm
  exact K.cast hSource hTarget

private theorem loopRetuningHomotopy_unit_value {x : X} {y : Y}
    (f : ContinuousMap.WeaklyPointed x y) (d : C(X, Y)) (hd : d x = y)
    (H : ContinuousMap.Homotopy f.hom d)
    (hTrace : ∀ t : unitInterval, H (t, x) = f.rootPath t)
    (k : C(LoopSpace X x, LoopSpace Y y))
    (hMap : ∀ (gamma : LoopSpace X x) (t : unitInterval), k gamma t = d (gamma t))
    (t s : unitInterval) :
    (((loopRetuningHomotopy f d hd H hTrace k hMap).toContinuousMap.toFun
      (t, Path.refl x)).toContinuousMap).toFun s =
      f.rootPath.toContinuousMap.toFun
        (ContinuousMap.Homotopy.traceConjugationLoopHomotopy
          ContinuousMap.Homotopy.intervalCoordinateHomotopy (0 : unitInterval)
          (t, Path.refl (0 : unitInterval)) s) := by
  subst y
  unfold loopRetuningHomotopy
  change ContinuousMap.Homotopy.traceConjugationLoopHomotopy H x (t, Path.refl x) s = _
  exact (ContinuousMap.Homotopy.traceConjugationLoopHomotopy_refl_template_value H x t s).trans
    (hTrace _)

end WholeLoopRetuning


variable (R : Type uR) [Ring R]

local instance categoryEquivalenceFunctorAdditive :
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).functor.Additive :=
  FGProjectiveCat.CategoryUniverseLift.upFunctorAdditive.{uR, uM, uObj, uHom} R

local instance categoryEquivalenceInverseAdditive :
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).inverse.Additive :=
  FGProjectiveCat.CategoryUniverseLift.downFunctorAdditive.{uR, uM, uObj, uHom} R

local instance categoryEquivalenceFunctorIsExact :
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).functor.IsExact :=
  FGProjectiveCat.CategoryUniverseLift.upFunctorIsExact.{uR, uM, uObj, uHom} R

local instance categoryEquivalenceInverseIsExact :
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).inverse.IsExact :=
  FGProjectiveCat.CategoryUniverseLift.downFunctorIsExact.{uR, uM, uObj, uHom} R

/-- The original projective category in the independently selected module universe. -/
public abbrev canonicalCategory := FGProjectiveCat.{max uR uM} R

/-- The actual category with independently lifted object and morphism universes. -/
public abbrev liftedCategory :=
  FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R

/-- The original Quillen categories are related by the canonical exact equivalence. -/
public def qCategoryEquivalence :
    QuillenQ (canonicalCategory.{uR, uM} R) ≌
      QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) :=
  QuillenQ.equivOfEquivalence
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R)

/-- The forward Quillen functor is induced by the actual category inclusion. -/
public def qUpFunctor :
    QuillenQ (canonicalCategory.{uR, uM} R) ⥤
      QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) :=
  (qCategoryEquivalence.{uR, uM, uObj, uHom} R).functor

/-- The backward Quillen functor is induced by the actual category projection. -/
public def qDownFunctor :
    QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) ⥤
      QuillenQ (canonicalCategory.{uR, uM} R) :=
  (qCategoryEquivalence.{uR, uM, uObj, uHom} R).inverse

/-- The forward projection retains the original additive exact functor. -/
public theorem qUpFunctor_eq_map (R : Type uR) [Ring R] :
    qUpFunctor.{uR, uM, uObj, uHom} R =
      QuillenQ.map
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R) :=
  QuillenQ.equivOfEquivalence_functor
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R)

/-- The backward projection retains the original additive exact inverse. -/
public theorem qDownFunctor_eq_map (R : Type uR) [Ring R] :
    qDownFunctor.{uR, uM, uObj, uHom} R =
      QuillenQ.map
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R) :=
  QuillenQ.equivOfEquivalence_inverse
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R)

/-- The original Q inclusion has exactly the actual included object. -/
public theorem qUpFunctor_obj (R : Type uR) [Ring R]
    (X : canonicalCategory.{uR, uM} R) :
    (qUpFunctor.{uR, uM, uObj, uHom} R).obj
        (⟨X⟩ : QuillenQ (canonicalCategory.{uR, uM} R)) =
      (⟨(FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R).obj X⟩ :
        QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) :=
  congrArg
    (fun F : QuillenQ (canonicalCategory.{uR, uM} R) ⥤
        QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) => F.obj ⟨X⟩)
    (qUpFunctor_eq_map.{uR, uM, uObj, uHom} R)

/-- The original Q projection has exactly the actual descended object. -/
public theorem qDownFunctor_obj (R : Type uR) [Ring R]
    (X : liftedCategory.{uR, uM, uObj, uHom} R) :
    (qDownFunctor.{uR, uM, uObj, uHom} R).obj
        (⟨X⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) =
      (⟨(FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj X⟩ :
        QuillenQ (canonicalCategory.{uR, uM} R)) :=
  congrArg
    (fun F : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) ⥤
        QuillenQ (canonicalCategory.{uR, uM} R) => F.obj ⟨X⟩)
    (qDownFunctor_eq_map.{uR, uM, uObj, uHom} R)

/-- The entire original loop carrier at its literal zero vertex. -/
public abbrev originalLoops :=
  BasedSplitExactQLoop.originalQLoops
    (C := liftedCategory.{uR, uM, uObj, uHom} R)

/-- The original constant loop, with the same literal zero vertex. -/
public abbrev originalConstantLoop :=
  BasedSplitExactQLoop.constantQLoop
    (C := liftedCategory.{uR, uM, uObj, uHom} R)

/-- The original small-projective loop carrier retained by the existing comparison. -/
public abbrev canonicalLoops :=
  BasedSplitExactQLoop.originalQLoops (C := canonicalCategory.{uR, uM} R)

/-- The original small-projective constant loop. -/
public abbrev canonicalConstantLoop :=
  BasedSplitExactQLoop.constantQLoop (C := canonicalCategory.{uR, uM} R)

/-- The actual Q-category equivalence supplies the original realized inverse maps. -/
public def qRealizationHomotopyEquiv :
    NQReal (canonicalCategory.{uR, uM} R) ≃ₕ
      NQReal (liftedCategory.{uR, uM, uObj, uHom} R) :=
  CategoryTheory.realizedNerveEquivalence
    (qCategoryEquivalence.{uR, uM, uObj, uHom} R)

/-- Realization of the actual Quillen object/Hom inclusion. -/
public def qRealizationUp :
    C(NQReal (canonicalCategory.{uR, uM} R),
      NQReal (liftedCategory.{uR, uM, uObj, uHom} R)) :=
  (qRealizationHomotopyEquiv.{uR, uM, uObj, uHom} R).toFun

/-- Realization of the actual Quillen object/Hom projection. -/
public def qRealizationDown :
    C(NQReal (liftedCategory.{uR, uM, uObj, uHom} R),
      NQReal (canonicalCategory.{uR, uM} R)) :=
  (qRealizationHomotopyEquiv.{uR, uM, uObj, uHom} R).invFun

/-- The actual forward map sends every original object vertex to its original image. -/
public theorem qRealizationUp_vertex
    (X : QuillenQ (canonicalCategory.{uR, uM} R)) :
    qRealizationUp.{uR, uM, uObj, uHom} R
        (SSet.realizedVertex (ComposableArrows.mk₀ X)) =
      SSet.realizedVertex (ComposableArrows.mk₀
        ((qUpFunctor.{uR, uM, uObj, uHom} R).obj X)) :=
  CategoryTheory.realizedNerveEquivalence_vertex
    (qCategoryEquivalence.{uR, uM, uObj, uHom} R) X

/-- The actual inverse map sends every original object vertex to its original image. -/
public theorem qRealizationDown_vertex
    (X : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) :
    qRealizationDown.{uR, uM, uObj, uHom} R
        (SSet.realizedVertex (ComposableArrows.mk₀ X)) =
      SSet.realizedVertex (ComposableArrows.mk₀
        ((qDownFunctor.{uR, uM, uObj, uHom} R).obj X)) :=
  CategoryTheory.realizedNerveEquivalence_inv_vertex
    (qCategoryEquivalence.{uR, uM, uObj, uHom} R) X

/-- The original Quillen zero comparison, derived from the actual category inclusion. -/
public def qUpZeroIso :
    (qUpFunctor.{uR, uM, uObj, uHom} R).obj
        (⟨0⟩ : QuillenQ (canonicalCategory.{uR, uM} R)) ≅
      (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) :=
  QuillenQ.zeroComparisonIso
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).functor

/-- The original Quillen zero comparison, derived from the actual category projection. -/
public def qDownZeroIso :
    (qDownFunctor.{uR, uM, uObj, uHom} R).obj
        (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) ≅
      (⟨0⟩ : QuillenQ (canonicalCategory.{uR, uM} R)) :=
  QuillenQ.zeroComparisonIso
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).inverse

private def qActualUnitInverse :
    qUpFunctor.{uR, uM, uObj, uHom} R ⋙ qDownFunctor.{uR, uM, uObj, uHom} R ≅
      𝟭 (QuillenQ (canonicalCategory.{uR, uM} R)) :=
  actualQUnitInverse
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R)

private def qActualCounit :
    qDownFunctor.{uR, uM, uObj, uHom} R ⋙ qUpFunctor.{uR, uM, uObj, uHom} R ≅
      𝟭 (QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) :=
  actualQCounit
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R)

private theorem qActualUnitInverse_zero :
    (qDownFunctor.{uR, uM, uObj, uHom} R).map
        (qUpZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        (qDownZeroIso.{uR, uM, uObj, uHom} R).hom =
      (qActualUnitInverse.{uR, uM, uObj, uHom} R).hom.app
        (⟨0⟩ : QuillenQ (canonicalCategory.{uR, uM} R)) :=
  actualQUnitInverse_zero
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R)

private theorem qActualCounit_zero :
    (qUpFunctor.{uR, uM, uObj, uHom} R).map
        (qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        (qUpZeroIso.{uR, uM, uObj, uHom} R).hom =
      (qActualCounit.{uR, uM, uObj, uHom} R).hom.app
        (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) :=
  actualQCounit_zero
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R)

private theorem qUpZeroIso_hom_transport (R : Type uR) [Ring R] :
    (qUpZeroIso.{uR, uM, uObj, uHom} R).hom =
      eqToHom (qUpFunctor_obj.{uR, uM, uObj, uHom} R (0 : canonicalCategory.{uR, uM} R)) ≫
        (QuillenQ.zeroComparisonIso
          (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R)).hom := by
  have hRecipe : HEq (qUpZeroIso.{uR, uM, uObj, uHom} R).hom
      (QuillenQ.zeroComparisonIso
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R)).hom := by
    dsimp only [qUpZeroIso]
    rfl
  let U := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R
  let Y : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) := ⟨0⟩
  let Z : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) := ⟨U.obj (0 : canonicalCategory.{uR, uM} R)⟩
  let h0 := qUpFunctor_obj.{uR, uM, uObj, uHom} R (0 : canonicalCategory.{uR, uM} R)
  let g : Z ⟶ Y := (QuillenQ.zeroComparisonIso U).hom
  have hConj : (qUpZeroIso.{uR, uM, uObj, uHom} R).hom =
      eqToHom h0 ≫ (g ≫ eqToHom (rfl : Y = Y)) :=
    (conj_eqToHom_iff_heq'
      (qUpZeroIso.{uR, uM, uObj, uHom} R).hom g h0 rfl).2 hRecipe
  have hUnit : g ≫ eqToHom (rfl : Y = Y) = g :=
    (congrArg (fun k : Y ⟶ Y => g ≫ k)
      (eqToHom_refl Y (rfl : Y = Y))).trans (Category.comp_id g)
  exact hConj.trans (congrArg (fun k : Z ⟶ Y => eqToHom h0 ≫ k) hUnit)

private theorem qDownZeroIso_hom_transport (R : Type uR) [Ring R] :
    (qDownZeroIso.{uR, uM, uObj, uHom} R).hom =
      eqToHom (qDownFunctor_obj.{uR, uM, uObj, uHom} R (0 : liftedCategory.{uR, uM, uObj, uHom} R)) ≫
        (QuillenQ.zeroComparisonIso
          (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)).hom := by
  have hRecipe : HEq (qDownZeroIso.{uR, uM, uObj, uHom} R).hom
      (QuillenQ.zeroComparisonIso
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)).hom := by
    dsimp only [qDownZeroIso]
    rfl
  let U := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  let Y : QuillenQ (canonicalCategory.{uR, uM} R) := ⟨0⟩
  let Z : QuillenQ (canonicalCategory.{uR, uM} R) := ⟨U.obj (0 : liftedCategory.{uR, uM, uObj, uHom} R)⟩
  let h0 := qDownFunctor_obj.{uR, uM, uObj, uHom} R (0 : liftedCategory.{uR, uM, uObj, uHom} R)
  let g : Z ⟶ Y := (QuillenQ.zeroComparisonIso U).hom
  have hConj : (qDownZeroIso.{uR, uM, uObj, uHom} R).hom =
      eqToHom h0 ≫ (g ≫ eqToHom (rfl : Y = Y)) :=
    (conj_eqToHom_iff_heq'
      (qDownZeroIso.{uR, uM, uObj, uHom} R).hom g h0 rfl).2 hRecipe
  have hUnit : g ≫ eqToHom (rfl : Y = Y) = g :=
    (congrArg (fun k : Y ⟶ Y => g ≫ k)
      (eqToHom_refl Y (rfl : Y = Y))).trans (Category.comp_id g)
  exact hConj.trans (congrArg (fun k : Z ⟶ Y => eqToHom h0 ≫ k) hUnit)

/-- The original Q zero isomorphism uses the actual source-object transport
and the category owner's canonical chosen-zero isomorphism. -/
public theorem qUpZeroIso_eq_underlyingIso (R : Type uR) [Ring R] :
    qUpZeroIso.{uR, uM, uObj, uHom} R =
      eqToIso (qUpFunctor_obj.{uR, uM, uObj, uHom} R (0 : canonicalCategory.{uR, uM} R)) ≪≫
        QuillenQ.underlyingIso
          (FGProjectiveCat.CategoryUniverseLift.upZeroIso.{uR, uM, uObj, uHom} R) := by
  apply Iso.ext
  let U := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R
  let h0 := qUpFunctor_obj.{uR, uM, uObj, uHom} R (0 : canonicalCategory.{uR, uM} R)
  have hZero : (QuillenQ.zeroComparisonIso U).hom =
      (QuillenQ.underlyingIso
        (FGProjectiveCat.CategoryUniverseLift.upZeroIso.{uR, uM, uObj, uHom} R)).hom :=
    congrArg (fun e : U.obj (0 : canonicalCategory.{uR, uM} R) ≅ (0 : liftedCategory.{uR, uM, uObj, uHom} R) =>
      (QuillenQ.underlyingIso e).hom)
      (FGProjectiveCat.CategoryUniverseLift.upFunctorMapZeroObject.{uR, uM, uObj, uHom} R)
  exact (qUpZeroIso_hom_transport.{uR, uM, uObj, uHom} R).trans
    (congrArg (fun f : (⟨U.obj (0 : canonicalCategory.{uR, uM} R)⟩ :
      QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) ⟶ ⟨0⟩ =>
      eqToHom h0 ≫ f) hZero)

/-- The original Q zero isomorphism uses the actual source-object transport
and the category owner's canonical chosen-zero isomorphism. -/
public theorem qDownZeroIso_eq_underlyingIso (R : Type uR) [Ring R] :
    qDownZeroIso.{uR, uM, uObj, uHom} R =
      eqToIso (qDownFunctor_obj.{uR, uM, uObj, uHom} R (0 : liftedCategory.{uR, uM, uObj, uHom} R)) ≪≫
        QuillenQ.underlyingIso
          (FGProjectiveCat.CategoryUniverseLift.downZeroIso.{uR, uM, uObj, uHom} R) := by
  apply Iso.ext
  let U := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  let h0 := qDownFunctor_obj.{uR, uM, uObj, uHom} R (0 : liftedCategory.{uR, uM, uObj, uHom} R)
  have hZero : (QuillenQ.zeroComparisonIso U).hom =
      (QuillenQ.underlyingIso
        (FGProjectiveCat.CategoryUniverseLift.downZeroIso.{uR, uM, uObj, uHom} R)).hom :=
    congrArg (fun e : U.obj (0 : liftedCategory.{uR, uM, uObj, uHom} R) ≅ (0 : canonicalCategory.{uR, uM} R) =>
      (QuillenQ.underlyingIso e).hom)
      (FGProjectiveCat.CategoryUniverseLift.downFunctorMapZeroObject.{uR, uM, uObj, uHom} R)
  exact (qDownZeroIso_hom_transport.{uR, uM, uObj, uHom} R).trans
    (congrArg (fun f : (⟨U.obj (0 : liftedCategory.{uR, uM, uObj, uHom} R)⟩ :
      QuillenQ (canonicalCategory.{uR, uM} R)) ⟶ ⟨0⟩ =>
      eqToHom h0 ≫ f) hZero)

/-- The original Q zero-mono span is retained after its canonical
target-object transport, with the same chosen-zero comparison. -/
public theorem qUpFunctor_zeroMono (R : Type uR) [Ring R]
    (X : canonicalCategory.{uR, uM} R) :
    (qUpFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroMonoHom X) ≫
        eqToHom (qUpFunctor_obj.{uR, uM, uObj, uHom} R X) =
      (qUpZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroMonoHom
          ((FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R).obj X) := by
  let U := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R
  let Q0 : QuillenQ (canonicalCategory.{uR, uM} R) := ⟨0⟩
  let QX : QuillenQ (canonicalCategory.{uR, uM} R) := ⟨X⟩
  let h0 := qUpFunctor_obj.{uR, uM, uObj, uHom} R (0 : canonicalCategory.{uR, uM} R)
  let hX := qUpFunctor_obj.{uR, uM, uObj, uHom} R X
  have hMap := Functor.congr_hom
    (qUpFunctor_eq_map.{uR, uM, uObj, uHom} R)
    (ExtensionCategory.zeroMonoHom X)
  have hSpan := mapZeroMonoHomPrivate U X
  have hZero := qUpZeroIso_hom_transport.{uR, uM, uObj, uHom} R
  apply (comp_eqToHom_iff hX
    ((qUpFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroMonoHom X))
    ((qUpZeroIso.{uR, uM, uObj, uHom} R).hom ≫
      ExtensionCategory.zeroMonoHom (U.obj X))).2
  calc
    (qUpFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroMonoHom X) =
        eqToHom h0 ≫ (QuillenQ.map U).map (ExtensionCategory.zeroMonoHom X) ≫
          eqToHom hX.symm := hMap
    _ = eqToHom h0 ≫
        ((QuillenQ.zeroComparisonIso U).hom ≫ ExtensionCategory.zeroMonoHom (U.obj X)) ≫
          eqToHom hX.symm :=
      congrArg (fun f : (QuillenQ.map U).obj Q0 ⟶ (QuillenQ.map U).obj QX =>
        eqToHom h0 ≫ f ≫ eqToHom hX.symm) hSpan
    _ = eqToHom h0 ≫ ((QuillenQ.zeroComparisonIso U).hom ≫
        (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm)) :=
      congrArg (fun k : (⟨U.obj (0 : canonicalCategory.{uR, uM} R)⟩ :
        QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) ⟶
          (qUpFunctor.{uR, uM, uObj, uHom} R).obj QX => eqToHom h0 ≫ k)
        (Category.assoc (QuillenQ.zeroComparisonIso U).hom
          (ExtensionCategory.zeroMonoHom (U.obj X)) (eqToHom hX.symm))
    _ = (eqToHom h0 ≫ (QuillenQ.zeroComparisonIso U).hom) ≫
        (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm) :=
      (Category.assoc (eqToHom h0) (QuillenQ.zeroComparisonIso U).hom
        (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm)).symm
    _ = (qUpZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm) :=
      congrArg (fun k : (qUpFunctor.{uR, uM, uObj, uHom} R).obj Q0 ⟶
          (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) =>
        k ≫ (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm)) hZero.symm
    _ = ((qUpZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroMonoHom (U.obj X)) ≫ eqToHom hX.symm :=
      (Category.assoc (qUpZeroIso.{uR, uM, uObj, uHom} R).hom
        (ExtensionCategory.zeroMonoHom (U.obj X)) (eqToHom hX.symm)).symm

/-- The original Q zero-epi span is retained after its canonical
target-object transport, with the same chosen-zero comparison. -/
public theorem qUpFunctor_zeroEpi (R : Type uR) [Ring R]
    (X : canonicalCategory.{uR, uM} R) :
    (qUpFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroEpiHom X) ≫
        eqToHom (qUpFunctor_obj.{uR, uM, uObj, uHom} R X) =
      (qUpZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroEpiHom
          ((FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R).obj X) := by
  let U := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R
  let Q0 : QuillenQ (canonicalCategory.{uR, uM} R) := ⟨0⟩
  let QX : QuillenQ (canonicalCategory.{uR, uM} R) := ⟨X⟩
  let h0 := qUpFunctor_obj.{uR, uM, uObj, uHom} R (0 : canonicalCategory.{uR, uM} R)
  let hX := qUpFunctor_obj.{uR, uM, uObj, uHom} R X
  have hMap := Functor.congr_hom
    (qUpFunctor_eq_map.{uR, uM, uObj, uHom} R)
    (ExtensionCategory.zeroEpiHom X)
  have hSpan := mapZeroEpiHomPrivate U X
  have hZero := qUpZeroIso_hom_transport.{uR, uM, uObj, uHom} R
  apply (comp_eqToHom_iff hX
    ((qUpFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroEpiHom X))
    ((qUpZeroIso.{uR, uM, uObj, uHom} R).hom ≫
      ExtensionCategory.zeroEpiHom (U.obj X))).2
  calc
    (qUpFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroEpiHom X) =
        eqToHom h0 ≫ (QuillenQ.map U).map (ExtensionCategory.zeroEpiHom X) ≫
          eqToHom hX.symm := hMap
    _ = eqToHom h0 ≫
        ((QuillenQ.zeroComparisonIso U).hom ≫ ExtensionCategory.zeroEpiHom (U.obj X)) ≫
          eqToHom hX.symm :=
      congrArg (fun f : (QuillenQ.map U).obj Q0 ⟶ (QuillenQ.map U).obj QX =>
        eqToHom h0 ≫ f ≫ eqToHom hX.symm) hSpan
    _ = eqToHom h0 ≫ ((QuillenQ.zeroComparisonIso U).hom ≫
        (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm)) :=
      congrArg (fun k : (⟨U.obj (0 : canonicalCategory.{uR, uM} R)⟩ :
        QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) ⟶
          (qUpFunctor.{uR, uM, uObj, uHom} R).obj QX => eqToHom h0 ≫ k)
        (Category.assoc (QuillenQ.zeroComparisonIso U).hom
          (ExtensionCategory.zeroEpiHom (U.obj X)) (eqToHom hX.symm))
    _ = (eqToHom h0 ≫ (QuillenQ.zeroComparisonIso U).hom) ≫
        (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm) :=
      (Category.assoc (eqToHom h0) (QuillenQ.zeroComparisonIso U).hom
        (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm)).symm
    _ = (qUpZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm) :=
      congrArg (fun k : (qUpFunctor.{uR, uM, uObj, uHom} R).obj Q0 ⟶
          (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) =>
        k ≫ (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm)) hZero.symm
    _ = ((qUpZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroEpiHom (U.obj X)) ≫ eqToHom hX.symm :=
      (Category.assoc (qUpZeroIso.{uR, uM, uObj, uHom} R).hom
        (ExtensionCategory.zeroEpiHom (U.obj X)) (eqToHom hX.symm)).symm

/-- The original Q zero-mono span is retained after its canonical
target-object transport, with the same chosen-zero comparison. -/
public theorem qDownFunctor_zeroMono (R : Type uR) [Ring R]
    (X : liftedCategory.{uR, uM, uObj, uHom} R) :
    (qDownFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroMonoHom X) ≫
        eqToHom (qDownFunctor_obj.{uR, uM, uObj, uHom} R X) =
      (qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroMonoHom
          ((FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj X) := by
  let U := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  let Q0 : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) := ⟨0⟩
  let QX : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) := ⟨X⟩
  let h0 := qDownFunctor_obj.{uR, uM, uObj, uHom} R (0 : liftedCategory.{uR, uM, uObj, uHom} R)
  let hX := qDownFunctor_obj.{uR, uM, uObj, uHom} R X
  have hMap := Functor.congr_hom
    (qDownFunctor_eq_map.{uR, uM, uObj, uHom} R)
    (ExtensionCategory.zeroMonoHom X)
  have hSpan := mapZeroMonoHomPrivate U X
  have hZero := qDownZeroIso_hom_transport.{uR, uM, uObj, uHom} R
  apply (comp_eqToHom_iff hX
    ((qDownFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroMonoHom X))
    ((qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
      ExtensionCategory.zeroMonoHom (U.obj X))).2
  calc
    (qDownFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroMonoHom X) =
        eqToHom h0 ≫ (QuillenQ.map U).map (ExtensionCategory.zeroMonoHom X) ≫
          eqToHom hX.symm := hMap
    _ = eqToHom h0 ≫
        ((QuillenQ.zeroComparisonIso U).hom ≫ ExtensionCategory.zeroMonoHom (U.obj X)) ≫
          eqToHom hX.symm :=
      congrArg (fun f : (QuillenQ.map U).obj Q0 ⟶ (QuillenQ.map U).obj QX =>
        eqToHom h0 ≫ f ≫ eqToHom hX.symm) hSpan
    _ = eqToHom h0 ≫ ((QuillenQ.zeroComparisonIso U).hom ≫
        (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm)) :=
      congrArg (fun k : (⟨U.obj (0 : liftedCategory.{uR, uM, uObj, uHom} R)⟩ :
        QuillenQ (canonicalCategory.{uR, uM} R)) ⟶
          (qDownFunctor.{uR, uM, uObj, uHom} R).obj QX => eqToHom h0 ≫ k)
        (Category.assoc (QuillenQ.zeroComparisonIso U).hom
          (ExtensionCategory.zeroMonoHom (U.obj X)) (eqToHom hX.symm))
    _ = (eqToHom h0 ≫ (QuillenQ.zeroComparisonIso U).hom) ≫
        (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm) :=
      (Category.assoc (eqToHom h0) (QuillenQ.zeroComparisonIso U).hom
        (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm)).symm
    _ = (qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm) :=
      congrArg (fun k : (qDownFunctor.{uR, uM, uObj, uHom} R).obj Q0 ⟶
          (⟨0⟩ : QuillenQ (canonicalCategory.{uR, uM} R)) =>
        k ≫ (ExtensionCategory.zeroMonoHom (U.obj X) ≫ eqToHom hX.symm)) hZero.symm
    _ = ((qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroMonoHom (U.obj X)) ≫ eqToHom hX.symm :=
      (Category.assoc (qDownZeroIso.{uR, uM, uObj, uHom} R).hom
        (ExtensionCategory.zeroMonoHom (U.obj X)) (eqToHom hX.symm)).symm

/-- The original Q zero-epi span is retained after its canonical
target-object transport, with the same chosen-zero comparison. -/
public theorem qDownFunctor_zeroEpi (R : Type uR) [Ring R]
    (X : liftedCategory.{uR, uM, uObj, uHom} R) :
    (qDownFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroEpiHom X) ≫
        eqToHom (qDownFunctor_obj.{uR, uM, uObj, uHom} R X) =
      (qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroEpiHom
          ((FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj X) := by
  let U := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  let Q0 : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) := ⟨0⟩
  let QX : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) := ⟨X⟩
  let h0 := qDownFunctor_obj.{uR, uM, uObj, uHom} R (0 : liftedCategory.{uR, uM, uObj, uHom} R)
  let hX := qDownFunctor_obj.{uR, uM, uObj, uHom} R X
  have hMap := Functor.congr_hom
    (qDownFunctor_eq_map.{uR, uM, uObj, uHom} R)
    (ExtensionCategory.zeroEpiHom X)
  have hSpan := mapZeroEpiHomPrivate U X
  have hZero := qDownZeroIso_hom_transport.{uR, uM, uObj, uHom} R
  apply (comp_eqToHom_iff hX
    ((qDownFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroEpiHom X))
    ((qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
      ExtensionCategory.zeroEpiHom (U.obj X))).2
  calc
    (qDownFunctor.{uR, uM, uObj, uHom} R).map (ExtensionCategory.zeroEpiHom X) =
        eqToHom h0 ≫ (QuillenQ.map U).map (ExtensionCategory.zeroEpiHom X) ≫
          eqToHom hX.symm := hMap
    _ = eqToHom h0 ≫
        ((QuillenQ.zeroComparisonIso U).hom ≫ ExtensionCategory.zeroEpiHom (U.obj X)) ≫
          eqToHom hX.symm :=
      congrArg (fun f : (QuillenQ.map U).obj Q0 ⟶ (QuillenQ.map U).obj QX =>
        eqToHom h0 ≫ f ≫ eqToHom hX.symm) hSpan
    _ = eqToHom h0 ≫ ((QuillenQ.zeroComparisonIso U).hom ≫
        (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm)) :=
      congrArg (fun k : (⟨U.obj (0 : liftedCategory.{uR, uM, uObj, uHom} R)⟩ :
        QuillenQ (canonicalCategory.{uR, uM} R)) ⟶
          (qDownFunctor.{uR, uM, uObj, uHom} R).obj QX => eqToHom h0 ≫ k)
        (Category.assoc (QuillenQ.zeroComparisonIso U).hom
          (ExtensionCategory.zeroEpiHom (U.obj X)) (eqToHom hX.symm))
    _ = (eqToHom h0 ≫ (QuillenQ.zeroComparisonIso U).hom) ≫
        (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm) :=
      (Category.assoc (eqToHom h0) (QuillenQ.zeroComparisonIso U).hom
        (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm)).symm
    _ = (qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm) :=
      congrArg (fun k : (qDownFunctor.{uR, uM, uObj, uHom} R).obj Q0 ⟶
          (⟨0⟩ : QuillenQ (canonicalCategory.{uR, uM} R)) =>
        k ≫ (ExtensionCategory.zeroEpiHom (U.obj X) ≫ eqToHom hX.symm)) hZero.symm
    _ = ((qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroEpiHom (U.obj X)) ≫ eqToHom hX.symm :=
      (Category.assoc (qDownZeroIso.{uR, uM, uObj, uHom} R).hom
        (ExtensionCategory.zeroEpiHom (U.obj X)) (eqToHom hX.symm)).symm

/-- The actual mapped-zero-to-chosen-zero path for the realized inclusion. -/
public def qUpZeroPath :
    Path
      (qRealizationUp.{uR, uM, uObj, uHom} R
        (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R)))
      (OriginalQZeroComparison.zeroQVertex
        (C := liftedCategory.{uR, uM, uObj, uHom} R)) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath
    (CategoryTheory.nerve.edgeMk (qUpZeroIso.{uR, uM, uObj, uHom} R).hom))).cast
      (qRealizationUp_vertex.{uR, uM, uObj, uHom} R ⟨0⟩) rfl

/-- The actual mapped-zero-to-chosen-zero path for the realized projection. -/
public def qDownZeroPath :
    Path
      (qRealizationDown.{uR, uM, uObj, uHom} R
        (OriginalQZeroComparison.zeroQVertex
          (C := liftedCategory.{uR, uM, uObj, uHom} R)))
      (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R)) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath
    (CategoryTheory.nerve.edgeMk (qDownZeroIso.{uR, uM, uObj, uHom} R).hom))).cast
      (qRealizationDown_vertex.{uR, uM, uObj, uHom} R ⟨0⟩) rfl

private theorem qUpDownZeroPath_homotopic_unitEdge :
    (((qUpZeroPath.{uR, uM, uObj, uHom} R).map
        (qRealizationDown.{uR, uM, uObj, uHom} R).continuous).trans
        (qDownZeroPath.{uR, uM, uObj, uHom} R)).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((qActualUnitInverse.{uR, uM, uObj, uHom} R).hom.app
          (⟨0⟩ : QuillenQ (canonicalCategory.{uR, uM} R)))))).cast
        ((congrArg (qRealizationDown.{uR, uM, uObj, uHom} R)
            (qRealizationUp_vertex.{uR, uM, uObj, uHom} R
              (⟨0⟩ : QuillenQ (canonicalCategory.{uR, uM} R)))).trans
          (qRealizationDown_vertex.{uR, uM, uObj, uHom} R
            ((qUpFunctor.{uR, uM, uObj, uHom} R).obj ⟨0⟩))) rfl) := by
  let E := qCategoryEquivalence.{uR, uM, uObj, uHom} R
  let x : QuillenQ (canonicalCategory.{uR, uM} R) := ⟨0⟩
  let y : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) := ⟨0⟩
  let f := (qUpZeroIso.{uR, uM, uObj, uHom} R).hom
  let g := (qDownZeroIso.{uR, uM, uObj, uHom} R).hom
  let D := qRealizationDown.{uR, uM, uObj, uHom} R
  let p := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk f))
  let q := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk g))
  let m := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk ((qDownFunctor.{uR, uM, uObj, uHom} R).map f)))
  let e := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk ((qActualUnitInverse.{uR, uM, uObj, uHom} R).hom.app x)))
  let hx := qRealizationUp_vertex.{uR, uM, uObj, uHom} R x
  let hy := qRealizationDown_vertex.{uR, uM, uObj, uHom} R y
  let hxy := qRealizationDown_vertex.{uR, uM, uObj, uHom} R
    ((qUpFunctor.{uR, uM, uObj, uHom} R).obj x)
  let h0 := (congrArg D hx).trans hxy
  have hMapped :=
    (CategoryTheory.realizedNerveEquivalence_inv_edge_homotopic E f).pathCast h0 hy
  have hLeft :
      (((p.map D.continuous).cast hxy.symm hy.symm).cast h0 hy) =
        (qUpZeroPath.{uR, uM, uObj, uHom} R).map D.continuous := by
    apply _root_.Path.ext
    funext t
    rfl
  obtain ⟨Hmapped⟩ := hMapped
  let Hmapped' := _root_.Path.Homotopy.cast Hmapped hLeft rfl
  let Hpair := Hmapped'.hcomp
    (_root_.Path.Homotopy.refl (qDownZeroPath.{uR, uM, uObj, uHom} R))
  have hRight :
      (m.cast h0 hy).trans (qDownZeroPath.{uR, uM, uObj, uHom} R) =
        (m.trans q).cast h0 rfl :=
    (_root_.Path.cast_trans m q h0 hy rfl).symm
  have hPair :
      (((qUpZeroPath.{uR, uM, uObj, uHom} R).map D.continuous).trans
        (qDownZeroPath.{uR, uM, uObj, uHom} R)).Homotopic
        ((m.trans q).cast h0 rfl) :=
    ⟨_root_.Path.Homotopy.cast Hpair rfl hRight⟩
  obtain ⟨hc⟩ := (nerve.nonempty_compStruct_iff
    ((qDownFunctor.{uR, uM, uObj, uHom} R).map f) g
    ((qActualUnitInverse.{uR, uM, uObj, uHom} R).hom.app x)).mpr
      (qActualUnitInverse_zero.{uR, uM, uObj, uHom} R)
  have hDirect : e.Homotopic (m.trans q) := SSet.realizedCompStructHomotopic hc
  exact hPair.trans (hDirect.pathCast h0 rfl).symm

private theorem qDownUpZeroPath_homotopic_counitEdge :
    (((qDownZeroPath.{uR, uM, uObj, uHom} R).map
        (qRealizationUp.{uR, uM, uObj, uHom} R).continuous).trans
        (qUpZeroPath.{uR, uM, uObj, uHom} R)).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((qActualCounit.{uR, uM, uObj, uHom} R).hom.app
          (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)))))).cast
        ((congrArg (qRealizationUp.{uR, uM, uObj, uHom} R)
            (qRealizationDown_vertex.{uR, uM, uObj, uHom} R
              (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)))).trans
          (qRealizationUp_vertex.{uR, uM, uObj, uHom} R
            ((qDownFunctor.{uR, uM, uObj, uHom} R).obj ⟨0⟩))) rfl) := by
  let E := qCategoryEquivalence.{uR, uM, uObj, uHom} R
  let x : QuillenQ (canonicalCategory.{uR, uM} R) := ⟨0⟩
  let y : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) := ⟨0⟩
  let f := (qDownZeroIso.{uR, uM, uObj, uHom} R).hom
  let g := (qUpZeroIso.{uR, uM, uObj, uHom} R).hom
  let U := qRealizationUp.{uR, uM, uObj, uHom} R
  let p := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk f))
  let q := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk g))
  let m := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk ((qUpFunctor.{uR, uM, uObj, uHom} R).map f)))
  let e := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk ((qActualCounit.{uR, uM, uObj, uHom} R).hom.app y)))
  let hy := qRealizationDown_vertex.{uR, uM, uObj, uHom} R y
  let hx := qRealizationUp_vertex.{uR, uM, uObj, uHom} R x
  let hyx := qRealizationUp_vertex.{uR, uM, uObj, uHom} R
    ((qDownFunctor.{uR, uM, uObj, uHom} R).obj y)
  let h0 := (congrArg U hy).trans hyx
  have hMapped :=
    (CategoryTheory.realizedNerveEquivalence_edge_homotopic E f).pathCast h0 hx
  have hLeft :
      (((p.map U.continuous).cast hyx.symm hx.symm).cast h0 hx) =
        (qDownZeroPath.{uR, uM, uObj, uHom} R).map U.continuous := by
    apply _root_.Path.ext
    funext t
    rfl
  obtain ⟨Hmapped⟩ := hMapped
  let Hmapped' := _root_.Path.Homotopy.cast Hmapped hLeft rfl
  let Hpair := Hmapped'.hcomp
    (_root_.Path.Homotopy.refl (qUpZeroPath.{uR, uM, uObj, uHom} R))
  have hRight :
      (m.cast h0 hx).trans (qUpZeroPath.{uR, uM, uObj, uHom} R) =
        (m.trans q).cast h0 rfl :=
    (_root_.Path.cast_trans m q h0 hx rfl).symm
  have hPair :
      (((qDownZeroPath.{uR, uM, uObj, uHom} R).map U.continuous).trans
        (qUpZeroPath.{uR, uM, uObj, uHom} R)).Homotopic
        ((m.trans q).cast h0 rfl) :=
    ⟨_root_.Path.Homotopy.cast Hpair rfl hRight⟩
  obtain ⟨hc⟩ := (nerve.nonempty_compStruct_iff
    ((qUpFunctor.{uR, uM, uObj, uHom} R).map f) g
    ((qActualCounit.{uR, uM, uObj, uHom} R).hom.app y)).mpr
      (qActualCounit_zero.{uR, uM, uObj, uHom} R)
  have hDirect : e.Homotopic (m.trans q) := SSet.realizedCompStructHomotopic hc
  exact hPair.trans (hDirect.pathCast h0 rfl).symm

private def qOriginalUnitHomotopy :
    ContinuousMap.Homotopy
      ((qRealizationDown.{uR, uM, uObj, uHom} R).comp
        (qRealizationUp.{uR, uM, uObj, uHom} R))
      (ContinuousMap.id (NQReal (canonicalCategory.{uR, uM} R))) := by
  let C := QuillenQ (canonicalCategory.{uR, uM} R)
  let F := qUpFunctor.{uR, uM, uObj, uHom} R ⋙
    qDownFunctor.{uR, uM, uObj, uHom} R
  let alpha : F ⟶ 𝟭 C := (qActualUnitInverse.{uR, uM, uObj, uHom} R).hom
  let H := SSet.realizeHomotopy (nerve C) (nerve C)
    (nerveMap F) (nerveMap (𝟭 C)) (CategoryTheory.NatTrans.nerveHomotopy alpha)
  have hStart : (SSet.toTop.map (nerveMap F)).hom =
      (qRealizationDown.{uR, uM, uObj, uHom} R).comp
        (qRealizationUp.{uR, uM, uObj, uHom} R) :=
    (CategoryTheory.realizedNerveEquivalence_invFun_comp_toFun
      (qCategoryEquivalence.{uR, uM, uObj, uHom} R)).symm
  have hEnd : (SSet.toTop.map (nerveMap (𝟭 C))).hom =
      ContinuousMap.id (NQReal (canonicalCategory.{uR, uM} R)) := by
    rw [CategoryTheory.nerveMap_id, CategoryTheory.Functor.map_id, TopCat.hom_id]
  exact H.cast hStart hEnd

private def qOriginalCounitHomotopy :
    ContinuousMap.Homotopy
      ((qRealizationUp.{uR, uM, uObj, uHom} R).comp
        (qRealizationDown.{uR, uM, uObj, uHom} R))
      (ContinuousMap.id (NQReal (liftedCategory.{uR, uM, uObj, uHom} R))) := by
  let D := QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)
  let F := qDownFunctor.{uR, uM, uObj, uHom} R ⋙
    qUpFunctor.{uR, uM, uObj, uHom} R
  let alpha : F ⟶ 𝟭 D := (qActualCounit.{uR, uM, uObj, uHom} R).hom
  let H := SSet.realizeHomotopy (nerve D) (nerve D)
    (nerveMap F) (nerveMap (𝟭 D)) (CategoryTheory.NatTrans.nerveHomotopy alpha)
  have hStart : (SSet.toTop.map (nerveMap F)).hom =
      (qRealizationUp.{uR, uM, uObj, uHom} R).comp
        (qRealizationDown.{uR, uM, uObj, uHom} R) :=
    (CategoryTheory.realizedNerveEquivalence_toFun_comp_invFun
      (qCategoryEquivalence.{uR, uM, uObj, uHom} R)).symm
  have hEnd : (SSet.toTop.map (nerveMap (𝟭 D))).hom =
      ContinuousMap.id (NQReal (liftedCategory.{uR, uM, uObj, uHom} R)) := by
    rw [CategoryTheory.nerveMap_id, CategoryTheory.Functor.map_id, TopCat.hom_id]
  exact H.cast hStart hEnd

private theorem qOriginalUnitHomotopy_apply_computed (t : unitInterval)
    (z : NQReal (canonicalCategory.{uR, uM} R)) :
    qOriginalUnitHomotopy.{uR, uM, uObj, uHom} R (t, z) =
      SSet.realizeHomotopy
        (nerve (QuillenQ (canonicalCategory.{uR, uM} R)))
        (nerve (QuillenQ (canonicalCategory.{uR, uM} R)))
        (nerveMap (qUpFunctor.{uR, uM, uObj, uHom} R ⋙
          qDownFunctor.{uR, uM, uObj, uHom} R))
        (nerveMap (𝟭 (QuillenQ (canonicalCategory.{uR, uM} R))))
        (CategoryTheory.NatTrans.nerveHomotopy
          (qActualUnitInverse.{uR, uM, uObj, uHom} R).hom) (t, z) := rfl

private theorem qOriginalCounitHomotopy_apply_computed (t : unitInterval)
    (z : NQReal (liftedCategory.{uR, uM, uObj, uHom} R)) :
    qOriginalCounitHomotopy.{uR, uM, uObj, uHom} R (t, z) =
      SSet.realizeHomotopy
        (nerve (QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)))
        (nerve (QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)))
        (nerveMap (qDownFunctor.{uR, uM, uObj, uHom} R ⋙
          qUpFunctor.{uR, uM, uObj, uHom} R))
        (nerveMap (𝟭 (QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R))))
        (CategoryTheory.NatTrans.nerveHomotopy
          (qActualCounit.{uR, uM, uObj, uHom} R).hom) (t, z) := rfl

private theorem qOriginalUnitHomotopy_zero :
    (qOriginalUnitHomotopy.{uR, uM, uObj, uHom} R).evalAt
        (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R)) =
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((qActualUnitInverse.{uR, uM, uObj, uHom} R).hom.app
          (⟨0⟩ : QuillenQ (canonicalCategory.{uR, uM} R)))))).cast
        ((congrArg (qRealizationDown.{uR, uM, uObj, uHom} R)
            (qRealizationUp_vertex.{uR, uM, uObj, uHom} R
              (⟨0⟩ : QuillenQ (canonicalCategory.{uR, uM} R)))).trans
          (qRealizationDown_vertex.{uR, uM, uObj, uHom} R
            ((qUpFunctor.{uR, uM, uObj, uHom} R).obj ⟨0⟩))) rfl := by
  let C := QuillenQ (canonicalCategory.{uR, uM} R)
  let F := qUpFunctor.{uR, uM, uObj, uHom} R ⋙
    qDownFunctor.{uR, uM, uObj, uHom} R
  let alpha : F ⟶ 𝟭 C := (qActualUnitInverse.{uR, uM, uObj, uHom} R).hom
  let x : C := ⟨0⟩
  let v : NQReal (canonicalCategory.{uR, uM} R) :=
    SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ x)
  apply _root_.Path.ext
  funext t
  have hValue := congrArg
    (fun p : _root_.Path ((SSet.toTop.map (nerveMap F)).hom v)
        ((SSet.toTop.map (nerveMap (𝟭 C))).hom v) => p t)
    (SSet.realizeHomotopy_nerveHomotopy_evalAt_polymorphic alpha x)
  exact (qOriginalUnitHomotopy_apply_computed.{uR, uM, uObj, uHom} R t v).trans hValue

private theorem qOriginalCounitHomotopy_zero :
    (qOriginalCounitHomotopy.{uR, uM, uObj, uHom} R).evalAt
        (OriginalQZeroComparison.zeroQVertex
          (C := liftedCategory.{uR, uM, uObj, uHom} R)) =
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((qActualCounit.{uR, uM, uObj, uHom} R).hom.app
          (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)))))).cast
        ((congrArg (qRealizationUp.{uR, uM, uObj, uHom} R)
            (qRealizationDown_vertex.{uR, uM, uObj, uHom} R
              (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)))).trans
          (qRealizationUp_vertex.{uR, uM, uObj, uHom} R
            ((qDownFunctor.{uR, uM, uObj, uHom} R).obj ⟨0⟩))) rfl := by
  let D := QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)
  let F := qDownFunctor.{uR, uM, uObj, uHom} R ⋙
    qUpFunctor.{uR, uM, uObj, uHom} R
  let alpha : F ⟶ 𝟭 D := (qActualCounit.{uR, uM, uObj, uHom} R).hom
  let x : D := ⟨0⟩
  let v : NQReal (liftedCategory.{uR, uM, uObj, uHom} R) :=
    SSet.realizedVertex (X := nerve D) (ComposableArrows.mk₀ x)
  apply _root_.Path.ext
  funext t
  have hValue := congrArg
    (fun p : _root_.Path ((SSet.toTop.map (nerveMap F)).hom v)
        ((SSet.toTop.map (nerveMap (𝟭 D))).hom v) => p t)
    (SSet.realizeHomotopy_nerveHomotopy_evalAt_polymorphic alpha x)
  exact (qOriginalCounitHomotopy_apply_computed.{uR, uM, uObj, uHom} R t v).trans hValue

private theorem qUpDownZeroPath_homotopic_unitTrace :
    (((qUpZeroPath.{uR, uM, uObj, uHom} R).map
        (qRealizationDown.{uR, uM, uObj, uHom} R).continuous).trans
        (qDownZeroPath.{uR, uM, uObj, uHom} R)).Homotopic
      ((qOriginalUnitHomotopy.{uR, uM, uObj, uHom} R).evalAt
        (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))) := by
  obtain ⟨H⟩ := qUpDownZeroPath_homotopic_unitEdge.{uR, uM, uObj, uHom} R
  exact ⟨_root_.Path.Homotopy.cast H rfl
    (qOriginalUnitHomotopy_zero.{uR, uM, uObj, uHom} R).symm⟩

private theorem qDownUpZeroPath_homotopic_counitTrace :
    (((qDownZeroPath.{uR, uM, uObj, uHom} R).map
        (qRealizationUp.{uR, uM, uObj, uHom} R).continuous).trans
        (qUpZeroPath.{uR, uM, uObj, uHom} R)).Homotopic
      ((qOriginalCounitHomotopy.{uR, uM, uObj, uHom} R).evalAt
        (OriginalQZeroComparison.zeroQVertex
          (C := liftedCategory.{uR, uM, uObj, uHom} R))) := by
  obtain ⟨H⟩ := qDownUpZeroPath_homotopic_counitEdge.{uR, uM, uObj, uHom} R
  exact ⟨_root_.Path.Homotopy.cast H rfl
    (qOriginalCounitHomotopy_zero.{uR, uM, uObj, uHom} R).symm⟩

/-- The actual projected Q map with its canonically derived zero-isomorphism root path. -/
public def qDownWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (OriginalQZeroComparison.zeroQVertex
        (C := liftedCategory.{uR, uM, uObj, uHom} R))
      (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R)) where
  hom := qRealizationDown.{uR, uM, uObj, uHom} R
  rootPath := qDownZeroPath.{uR, uM, uObj, uHom} R

/-- The actual included Q map with its canonically derived zero-isomorphism root path. -/
public def qUpWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))
      (OriginalQZeroComparison.zeroQVertex
        (C := liftedCategory.{uR, uM, uObj, uHom} R)) where
  hom := qRealizationUp.{uR, uM, uObj, uHom} R
  rootPath := qUpZeroPath.{uR, uM, uObj, uHom} R

/-- The original lifted-category realization in the independent native carrier universe. -/
public abbrev nativeRealization :=
  ULift.{uNative} (NQReal (liftedCategory.{uR, uM, uObj, uHom} R))

/-- The original chosen zero vertex, with the literal carrier inclusion. -/
public def nativeBasepoint : nativeRealization.{uR, uM, uObj, uHom, uNative} R :=
  ULift.up (OriginalQZeroComparison.zeroQVertex
    (C := liftedCategory.{uR, uM, uObj, uHom} R))

/-- Raw loops on the original realization in the actual native carrier. -/
public abbrev nativeRawLoopSpace :=
  LoopSpace (nativeRealization.{uR, uM, uObj, uHom, uNative} R)
    (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)

/-- The literal constant loop at the lifted original zero vertex. -/
public def nativeConstantLoop : nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R :=
  Path.refl (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)

/-- The native carrier projection applies ‘ULift.down’ to the original loop. -/
public def rawNativeCarrierDown :
    C(nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R,
      originalLoops.{uR, uM, uObj, uHom} R) :=
  ContinuousMap.strictLoopMap
    (Homeomorph.ulift : nativeRealization.{uR, uM, uObj, uHom, uNative} R ≃ₜ
      NQReal (liftedCategory.{uR, uM, uObj, uHom} R)).toHomotopyEquiv.toFun
    (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)

/-- The native carrier inclusion applies ‘ULift.up’ to the original loop. -/
public def rawNativeCarrierUp :
    C(originalLoops.{uR, uM, uObj, uHom} R,
      nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :=
  ContinuousMap.strictLoopMap
    (Homeomorph.ulift.symm : NQReal (liftedCategory.{uR, uM, uObj, uHom} R) ≃ₜ
      nativeRealization.{uR, uM, uObj, uHom, uNative} R).toHomotopyEquiv.toFun
    (OriginalQZeroComparison.zeroQVertex
      (C := liftedCategory.{uR, uM, uObj, uHom} R))

/-- Projection retains every actual original loop value. -/
public theorem rawNativeCarrierDown_apply
    (gamma : nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R)
    (t : unitInterval) :
    rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R gamma t = (gamma t).down := by
  let f : C(nativeRealization.{uR, uM, uObj, uHom, uNative} R,
      NQReal (liftedCategory.{uR, uM, uObj, uHom} R)) :=
    (Homeomorph.ulift : nativeRealization.{uR, uM, uObj, uHom, uNative} R ≃ₜ
      NQReal (liftedCategory.{uR, uM, uObj, uHom} R)).toHomotopyEquiv.toFun
  exact congrArg
    (fun p : LoopSpace (NQReal (liftedCategory.{uR, uM, uObj, uHom} R))
      (f (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)) => p t)
    (ContinuousMap.strictLoopMap_apply f
      (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R) gamma)

/-- Inclusion retains every actual original loop value. -/
public theorem rawNativeCarrierUp_apply
    (gamma : originalLoops.{uR, uM, uObj, uHom} R)
    (t : unitInterval) :
    rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R gamma t = ULift.up (gamma t) := by
  let f : C(NQReal (liftedCategory.{uR, uM, uObj, uHom} R),
      nativeRealization.{uR, uM, uObj, uHom, uNative} R) :=
    (Homeomorph.ulift.symm : NQReal (liftedCategory.{uR, uM, uObj, uHom} R) ≃ₜ
      nativeRealization.{uR, uM, uObj, uHom, uNative} R).toHomotopyEquiv.toFun
  exact congrArg
    (fun p : LoopSpace (nativeRealization.{uR, uM, uObj, uHom, uNative} R)
      (f (OriginalQZeroComparison.zeroQVertex
        (C := liftedCategory.{uR, uM, uObj, uHom} R))) => p t)
    (ContinuousMap.strictLoopMap_apply f
      (OriginalQZeroComparison.zeroQVertex
        (C := liftedCategory.{uR, uM, uObj, uHom} R)) gamma)

/-- The actual carrier projection preserves the original constant loop strictly. -/
public theorem rawNativeCarrierDown_constant :
    rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R
        (nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R) =
      originalConstantLoop.{uR, uM, uObj, uHom} R :=
  ContinuousMap.strictLoopMap_refl _ _

/-- The actual carrier inclusion preserves the native constant loop strictly. -/
public theorem rawNativeCarrierUp_constant :
    rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R
        (originalConstantLoop.{uR, uM, uObj, uHom} R) =
      nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R :=
  ContinuousMap.strictLoopMap_refl _ _

/-- Carrier inclusion after projection is the identity on the original native loop space. -/
public theorem rawNativeCarrierUp_comp_down :
    (rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R).comp
        (rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R) =
      ContinuousMap.id (nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) := by
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  funext t
  exact ULift.up_down (gamma t)

/-- Carrier projection after inclusion is the identity on the original chosen-zero loops. -/
public theorem rawNativeCarrierDown_comp_up :
    (rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
        (rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R) =
      ContinuousMap.id (originalLoops.{uR, uM, uObj, uHom} R) := by
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  rfl

/-- The native inverse family fixes the literal native constant loop for every time. -/
public def rawNativeCarrierLeftHomotopyRel :
    ContinuousMap.HomotopyRel
      ((rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R).comp
        (rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R))
      (ContinuousMap.id (nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R))
      {nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R} :=
  (ContinuousMap.HomotopyRel.refl
    (ContinuousMap.id (nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R))
    {nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R}).cast
      (rawNativeCarrierUp_comp_down.{uR, uM, uObj, uHom, uNative} R).symm rfl

/-- The original inverse family fixes the original chosen-zero constant loop for every time. -/
public def rawNativeCarrierRightHomotopyRel :
    ContinuousMap.HomotopyRel
      ((rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
        (rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R))
      (ContinuousMap.id (originalLoops.{uR, uM, uObj, uHom} R))
      {originalConstantLoop.{uR, uM, uObj, uHom} R} :=
  (ContinuousMap.HomotopyRel.refl
    (ContinuousMap.id (originalLoops.{uR, uM, uObj, uHom} R))
    {originalConstantLoop.{uR, uM, uObj, uHom} R}).cast
      (rawNativeCarrierDown_comp_up.{uR, uM, uObj, uHom, uNative} R).symm rfl

/-- The actual native carrier maps form an equivalence of the original loop carriers. -/
public def rawNativeCarrierHomotopyEquiv :
    nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R ≃ₕ
      originalLoops.{uR, uM, uObj, uHom} R where
  toFun := rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R
  invFun := rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R
  left_inv := ⟨(rawNativeCarrierLeftHomotopyRel.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩
  right_inv := ⟨(rawNativeCarrierRightHomotopyRel.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩

/-- The same original small-projective realization in the common native carrier. -/
public abbrev nativeCanonicalRealization :=
  ULift.{max (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)) uNative}
    (NQReal (canonicalCategory.{uR, uM} R))

/-- Its literal original zero vertex. -/
public def nativeCanonicalBasepoint :
    nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R :=
  ULift.up (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))

/-- The common native presentation of the actual unretuned Q projection. -/
public def nativeUnretunedRealizationEquiv :
    nativeRealization.{uR, uM, uObj, uHom, uNative} R ≃ₕ
      nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R :=
  (Homeomorph.ulift : nativeRealization.{uR, uM, uObj, uHom, uNative} R ≃ₜ
      NQReal (liftedCategory.{uR, uM, uObj, uHom} R)).toHomotopyEquiv.trans
    ((qRealizationHomotopyEquiv.{uR, uM, uObj, uHom} R).symm.trans
      (Homeomorph.ulift.symm : NQReal (canonicalCategory.{uR, uM} R) ≃ₜ
        nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R).toHomotopyEquiv)

/-- The original realized Q descent, before its zero path is retuned. -/
public def nativeUnretunedDown :
    TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R) ⟶
      TopCat.of (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) :=
  TopCat.ofHom (nativeUnretunedRealizationEquiv.{uR, uM, uObj, uHom, uNative} R).toFun

/-- The actual canonical Q-zero path in the common native carrier. -/
public def nativeDownZeroPath :
    Path
      (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R
        (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R))
      (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R) :=
  (qDownZeroPath.{uR, uM, uObj, uHom} R).map
    (show Continuous (fun x : NQReal (canonicalCategory.{uR, uM} R) =>
      (ULift.up x : nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R))
      from continuous_uliftUp)

/-- The original realized Q inclusion, before its own zero path is retuned. -/
public def nativeUnretunedUp :
    TopCat.of (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) ⟶
      TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R) :=
  TopCat.ofHom (nativeUnretunedRealizationEquiv.{uR, uM, uObj, uHom, uNative} R).invFun

/-- The actual inclusion's canonical Q-zero path in the original native carrier. -/
public def nativeUpZeroPath :
    Path
      (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R
        (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R))
      (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R) :=
  (qUpZeroPath.{uR, uM, uObj, uHom} R).map
    (show Continuous (fun x : NQReal (liftedCategory.{uR, uM, uObj, uHom} R) =>
      (ULift.up x : nativeRealization.{uR, uM, uObj, uHom, uNative} R))
      from continuous_uliftUp)

private theorem nativeDownZeroPathValueComputed (R : Type uR) [Ring R] (t : unitInterval) :
    nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R t =
      ULift.up (qDownZeroPath.{uR, uM, uObj, uHom} R t) := rfl

/-- Every original native downward zero-path time is the original Q root in its carrier. -/
public theorem nativeDownZeroPath_value (R : Type uR) [Ring R] (t : unitInterval) :
    nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R t =
      ULift.up (qDownZeroPath.{uR, uM, uObj, uHom} R t) :=
  nativeDownZeroPathValueComputed.{uR, uM, uObj, uHom, uNative} R t

private theorem nativeUpZeroPathValueComputed (R : Type uR) [Ring R] (t : unitInterval) :
    nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R t =
      ULift.up (qUpZeroPath.{uR, uM, uObj, uHom} R t) := rfl

/-- Every original native upward zero-path time retains its independently derived Q root. -/
public theorem nativeUpZeroPath_value (R : Type uR) [Ring R] (t : unitInterval) :
    nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R t =
      ULift.up (qUpZeroPath.{uR, uM, uObj, uHom} R t) :=
  nativeUpZeroPathValueComputed.{uR, uM, uObj, uHom, uNative} R t

private theorem nativeUnretunedDown_apply_computed
    (z : nativeRealization.{uR, uM, uObj, uHom, uNative} R) :
    nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R z =
      (ULift.up (qRealizationDown.{uR, uM, uObj, uHom} R z.down) :
        nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) := rfl

/-- The original native descent is exactly the realized category map on the old carrier. -/
public theorem nativeUnretunedDown_apply
    (z : nativeRealization.{uR, uM, uObj, uHom, uNative} R) :
    nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R z =
      (ULift.up (qRealizationDown.{uR, uM, uObj, uHom} R z.down) :
        nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) :=
  nativeUnretunedDown_apply_computed.{uR, uM, uObj, uHom, uNative} R z

private theorem nativeUnretunedUp_apply_computed
    (z : nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) :
    nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R z =
      (ULift.up (qRealizationUp.{uR, uM, uObj, uHom} R z.down) :
        nativeRealization.{uR, uM, uObj, uHom, uNative} R) := rfl

/-- The original native inclusion is exactly the realized category map on the old carrier. -/
public theorem nativeUnretunedUp_apply
    (z : nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) :
    nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R z =
      (ULift.up (qRealizationUp.{uR, uM, uObj, uHom} R z.down) :
        nativeRealization.{uR, uM, uObj, uHom, uNative} R) :=
  nativeUnretunedUp_apply_computed.{uR, uM, uObj, uHom, uNative} R z

private def nativeOriginalCounitHomotopy :
    ContinuousMap.Homotopy
      ((nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom.comp
        (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom)
      (ContinuousMap.id (nativeRealization.{uR, uM, uObj, uHom, uNative} R)) := by
  let X := NQReal (liftedCategory.{uR, uM, uObj, uHom} R)
  let A := nativeRealization.{uR, uM, uObj, uHom, uNative} R
  let D := (Homeomorph.ulift : A ≃ₜ X).toHomotopyEquiv.toFun
  let U := (Homeomorph.ulift.symm : X ≃ₜ A).toHomotopyEquiv.toFun
  let H := qOriginalCounitHomotopy.{uR, uM, uObj, uHom} R
  let K := (ContinuousMap.Homotopy.refl U).comp (H.compContinuousMap D)
  have hStart : U.comp
      (((qRealizationUp.{uR, uM, uObj, uHom} R).comp
        (qRealizationDown.{uR, uM, uObj, uHom} R)).comp D) =
      (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom.comp
        (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom := by
    apply ContinuousMap.ext
    intro z
    exact ((nativeUnretunedUp_apply.{uR, uM, uObj, uHom, uNative} R
        (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R z)).trans
      (congrArg (fun w : nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R =>
        (ULift.up (qRealizationUp.{uR, uM, uObj, uHom} R w.down) : A))
        (nativeUnretunedDown_apply.{uR, uM, uObj, uHom, uNative} R z))).symm
  have hEnd : U.comp ((ContinuousMap.id X).comp D) = ContinuousMap.id A := by
    apply ContinuousMap.ext
    intro z
    exact ULift.up_down z
  exact K.cast hStart hEnd

private def nativeOriginalUnitHomotopy :
    ContinuousMap.Homotopy
      ((nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom.comp
        (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom)
      (ContinuousMap.id (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R)) := by
  let X := NQReal (canonicalCategory.{uR, uM} R)
  let B := nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R
  let D := (Homeomorph.ulift : B ≃ₜ X).toHomotopyEquiv.toFun
  let U := (Homeomorph.ulift.symm : X ≃ₜ B).toHomotopyEquiv.toFun
  let H := qOriginalUnitHomotopy.{uR, uM, uObj, uHom} R
  let K := (ContinuousMap.Homotopy.refl U).comp (H.compContinuousMap D)
  have hStart : U.comp
      (((qRealizationDown.{uR, uM, uObj, uHom} R).comp
        (qRealizationUp.{uR, uM, uObj, uHom} R)).comp D) =
      (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom.comp
        (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom := by
    apply ContinuousMap.ext
    intro z
    exact ((nativeUnretunedDown_apply.{uR, uM, uObj, uHom, uNative} R
        (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R z)).trans
      (congrArg (fun w : nativeRealization.{uR, uM, uObj, uHom, uNative} R =>
        (ULift.up (qRealizationDown.{uR, uM, uObj, uHom} R w.down) : B))
        (nativeUnretunedUp_apply.{uR, uM, uObj, uHom, uNative} R z))).symm
  have hEnd : U.comp ((ContinuousMap.id X).comp D) = ContinuousMap.id B := by
    apply ContinuousMap.ext
    intro z
    exact ULift.up_down z
  exact K.cast hStart hEnd

private theorem nativeDownUpZeroPath_homotopic_counitTrace :
    (((nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R).map
        (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom.continuous).trans
        (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R)).Homotopic
      ((nativeOriginalCounitHomotopy.{uR, uM, uObj, uHom, uNative} R).evalAt
        (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)) := by
  let a := nativeBasepoint.{uR, uM, uObj, uHom, uNative} R
  let x := OriginalQZeroComparison.zeroQVertex
    (C := liftedCategory.{uR, uM, uObj, uHom} R)
  let U : C(NQReal (liftedCategory.{uR, uM, uObj, uHom} R),
      nativeRealization.{uR, uM, uObj, uHom, uNative} R) :=
    (Homeomorph.ulift.symm : NQReal (liftedCategory.{uR, uM, uObj, uHom} R) ≃ₜ
      nativeRealization.{uR, uM, uObj, uHom, uNative} R).toHomotopyEquiv.toFun
  have hSource :
      nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R
          (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R a) =
        U (qRealizationUp.{uR, uM, uObj, uHom} R
          (qRealizationDown.{uR, uM, uObj, uHom} R x)) :=
    (nativeUnretunedUp_apply.{uR, uM, uObj, uHom, uNative} R
      (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R a)).trans
      (congrArg (fun w : nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R =>
        U (qRealizationUp.{uR, uM, uObj, uHom} R w.down))
        (nativeUnretunedDown_apply.{uR, uM, uObj, uHom, uNative} R a))
  have h := (qDownUpZeroPath_homotopic_counitTrace.{uR, uM, uObj, uHom} R).map U
  let h' := h.pathCast hSource (rfl : a = U x)
  have hLeft :
      ((((qDownZeroPath.{uR, uM, uObj, uHom} R).map
          (qRealizationUp.{uR, uM, uObj, uHom} R).continuous).trans
          (qUpZeroPath.{uR, uM, uObj, uHom} R)).map U.continuous).cast hSource rfl =
        ((nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R).map
          (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom.continuous).trans
          (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R) := by
    apply _root_.Path.ext
    funext t
    change U ((((qDownZeroPath.{uR, uM, uObj, uHom} R).map
        (qRealizationUp.{uR, uM, uObj, uHom} R).continuous).trans
        (qUpZeroPath.{uR, uM, uObj, uHom} R)) t) =
      (((nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R).map
        (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom.continuous).trans
        (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R)) t
    rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
    split_ifs with ht
    · exact (nativeUnretunedUp_apply.{uR, uM, uObj, uHom, uNative} R _).symm
    · rfl
  have hRight :
      (((qOriginalCounitHomotopy.{uR, uM, uObj, uHom} R).evalAt x).map
        U.continuous).cast hSource rfl =
      (nativeOriginalCounitHomotopy.{uR, uM, uObj, uHom, uNative} R).evalAt a := by
    apply _root_.Path.ext
    funext t
    rfl
  obtain ⟨H⟩ := h'
  exact ⟨_root_.Path.Homotopy.cast H hLeft hRight⟩

private theorem nativeUpDownZeroPath_homotopic_unitTrace :
    (((nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R).map
        (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom.continuous).trans
        (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R)).Homotopic
      ((nativeOriginalUnitHomotopy.{uR, uM, uObj, uHom, uNative} R).evalAt
        (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)) := by
  let b := nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R
  let y := OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R)
  let U : C(NQReal (canonicalCategory.{uR, uM} R),
      nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) :=
    (Homeomorph.ulift.symm : NQReal (canonicalCategory.{uR, uM} R) ≃ₜ
      nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R).toHomotopyEquiv.toFun
  have hSource :
      nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R
          (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R b) =
        U (qRealizationDown.{uR, uM, uObj, uHom} R
          (qRealizationUp.{uR, uM, uObj, uHom} R y)) :=
    (nativeUnretunedDown_apply.{uR, uM, uObj, uHom, uNative} R
      (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R b)).trans
      (congrArg (fun w : nativeRealization.{uR, uM, uObj, uHom, uNative} R =>
        U (qRealizationDown.{uR, uM, uObj, uHom} R w.down))
        (nativeUnretunedUp_apply.{uR, uM, uObj, uHom, uNative} R b))
  have h := (qUpDownZeroPath_homotopic_unitTrace.{uR, uM, uObj, uHom} R).map U
  let h' := h.pathCast hSource (rfl : b = U y)
  have hLeft :
      ((((qUpZeroPath.{uR, uM, uObj, uHom} R).map
          (qRealizationDown.{uR, uM, uObj, uHom} R).continuous).trans
          (qDownZeroPath.{uR, uM, uObj, uHom} R)).map U.continuous).cast hSource rfl =
        ((nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R).map
          (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom.continuous).trans
          (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R) := by
    apply _root_.Path.ext
    funext t
    change U ((((qUpZeroPath.{uR, uM, uObj, uHom} R).map
        (qRealizationDown.{uR, uM, uObj, uHom} R).continuous).trans
        (qDownZeroPath.{uR, uM, uObj, uHom} R)) t) =
      (((nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R).map
        (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom.continuous).trans
        (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R)) t
    rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
    split_ifs with ht
    · exact (nativeUnretunedDown_apply.{uR, uM, uObj, uHom, uNative} R _).symm
    · rfl
  have hRight :
      (((qOriginalUnitHomotopy.{uR, uM, uObj, uHom} R).evalAt y).map
        U.continuous).cast hSource rfl =
      (nativeOriginalUnitHomotopy.{uR, uM, uObj, uHom, uNative} R).evalAt b := by
    apply _root_.Path.ext
    funext t
    rfl
  obtain ⟨H⟩ := h'
  exact ⟨_root_.Path.Homotopy.cast H hLeft hRight⟩

/-- Both maps are retuned independently from their original category-induced
maps. No inverse of a separately selected map is used in this package. -/
private structure NativeCanonicalRetunings where
  down : TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R) ⟶
    TopCat.of (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R)
  up : TopCat.of (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) ⟶
    TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R)
  downPoint : down (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R) =
    nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R
  upPoint : up (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R) =
    nativeBasepoint.{uR, uM, uObj, uHom, uNative} R
  downRetuning : TopCat.Homotopy
    (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R) down
  upRetuning : TopCat.Homotopy
    (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R) up
  downTrace : ∀ t : unitInterval,
    downRetuning (t, nativeBasepoint.{uR, uM, uObj, uHom, uNative} R) =
      nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R t
  upTrace : ∀ t : unitInterval,
    upRetuning (t, nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R) =
      nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R t

private theorem nativeCanonicalRetunings_nonempty :
    Nonempty (NativeCanonicalRetunings.{uR, uM, uObj, uHom, uNative} R) := by
  let A := TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R)
  let B := TopCat.of (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R)
  let a : A := nativeBasepoint.{uR, uM, uObj, uHom, uNative} R
  let b : B := nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R
  let J := TopCat.of PUnit.{max (max (max (max uR uM + 1) uObj)
    (max (max uR uM) uHom)) uNative + 1}
  let pA : J ⟶ A := TopCat.const a
  let pB : J ⟶ B := TopCat.const b
  letI : Cofibration pA :=
    liftedRealizedVertexCofibration
      (NQ (liftedCategory.{uR, uM, uObj, uHom} R))
      (NQ.zeroVertex (liftedCategory.{uR, uM, uObj, uHom} R))
  letI : Cofibration pB :=
    liftedRealizedVertexCofibration
      (NQ (canonicalCategory.{uR, uM} R))
      (NQ.zeroVertex (canonicalCategory.{uR, uM} R))
  let fd : A ⟶ B := nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R
  let fu : B ⟶ A := nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R
  let Kd : TopCat.Homotopy (pA ≫ fd) pB :=
    { toFun := fun z => nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R z.1
      continuous_toFun :=
        (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R).continuous.comp continuous_fst
      map_zero_left := fun _ =>
        (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R).source
      map_one_left := fun _ =>
        (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R).target }
  let Ku : TopCat.Homotopy (pB ≫ fu) pA :=
    { toFun := fun z => nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R z.1
      continuous_toFun :=
        (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R).continuous.comp continuous_fst
      map_zero_left := fun _ =>
        (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R).source
      map_one_left := fun _ =>
        (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R).target }
  obtain ⟨d, Hd, hd, hHd⟩ :=
    TopCat.exists_homotopyExtension_of_cofibration pA fd pB Kd
  obtain ⟨u, Hu, hu, hHu⟩ :=
    TopCat.exists_homotopyExtension_of_cofibration pB fu pA Ku
  exact ⟨
    { down := d
      up := u
      downPoint := ConcreteCategory.congr_hom hd PUnit.unit
      upPoint := ConcreteCategory.congr_hom hu PUnit.unit
      downRetuning := Hd
      upRetuning := Hu
      downTrace := fun t => hHd t PUnit.unit
      upTrace := fun t => hHu t PUnit.unit }⟩

/-- The internally constructed based realization maps and their original zero trace. -/
public structure NativeRealizationData where
  /-- The actual Q descent retuned along the derived canonical zero path. -/
  down : TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R) ⟶
    TopCat.of (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R)
  /-- The actual Q inclusion retuned along its independently derived canonical zero path. -/
  up : TopCat.of (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) ⟶
    TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R)
  /-- The descended map has the literal original target zero value. -/
  downPoint : down (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R) =
    nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R
  /-- The inverse has the literal original source zero value. -/
  upPoint : up (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R) =
    nativeBasepoint.{uR, uM, uObj, uHom, uNative} R
  /-- The original actual Q descent is homotopic to this same based map. -/
  retuning : TopCat.Homotopy (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R) down
  /-- The complete original zero trace is the derived canonical Q-zero path. -/
  retuningTrace : ∀ t : unitInterval,
    retuning (t, nativeBasepoint.{uR, uM, uObj, uHom, uNative} R) =
      nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R t
  /-- The original actual Q inclusion is homotopic to this same based map. -/
  upRetuning : TopCat.Homotopy (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R) up
  /-- The complete upward trace is its independently derived canonical Q-zero path. -/
  upRetuningTrace : ∀ t : unitInterval,
    upRetuning (t, nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R) =
      nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R t
  /-- The complete source inverse family fixes the literal original native zero vertex. -/
  leftHomotopy : ContinuousMap.HomotopyRel (down ≫ up).hom
    (TopCat.Hom.hom (𝟙 (TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R))))
    {nativeBasepoint.{uR, uM, uObj, uHom, uNative} R}
  /-- The complete target inverse family fixes the literal original native zero vertex. -/
  rightHomotopy : ContinuousMap.HomotopyRel (up ≫ down).hom
    (TopCat.Hom.hom (𝟙 (TopCat.of
      (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R))))
    {nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R}

private theorem nativeRealizationData_nonempty :
    Nonempty (NativeRealizationData.{uR, uM, uObj, uHom, uNative} R) := by
  let A := TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R)
  let B := TopCat.of (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R)
  let a : A := nativeBasepoint.{uR, uM, uObj, uHom, uNative} R
  let b : B := nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R
  letI : Cofibration (TopCat.const a :
      TopCat.of PUnit.{max (max (max (max uR uM + 1) uObj)
        (max (max uR uM) uHom)) uNative + 1} ⟶ A) :=
    liftedRealizedVertexCofibration
      (NQ (liftedCategory.{uR, uM, uObj, uHom} R))
      (NQ.zeroVertex (liftedCategory.{uR, uM, uObj, uHom} R))
  letI : Cofibration (TopCat.const b :
      TopCat.of PUnit.{max (max (max (max uR uM + 1) uObj)
        (max (max uR uM) uHom)) uNative + 1} ⟶ B) :=
    liftedRealizedVertexCofibration
      (NQ (canonicalCategory.{uR, uM} R))
      (NQ.zeroVertex (canonicalCategory.{uR, uM} R))
  obtain ⟨r⟩ := nativeCanonicalRetunings_nonempty.{uR, uM, uObj, uHom, uNative} R
  obtain ⟨HL, hNullL⟩ := retunedCompositionNullTrace a b
    (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom r.down.hom
    (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom r.up.hom
    r.downPoint r.upPoint
    (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R)
    (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R)
    r.downRetuning r.upRetuning r.downTrace r.upTrace
    (nativeOriginalCounitHomotopy.{uR, uM, uObj, uHom, uNative} R)
    (nativeDownUpZeroPath_homotopic_counitTrace.{uR, uM, uObj, uHom, uNative} R)
  obtain ⟨HR, hNullR⟩ := retunedCompositionNullTrace b a
    (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom r.up.hom
    (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom r.down.hom
    r.upPoint r.downPoint
    (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R)
    (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R)
    r.upRetuning r.downRetuning r.upTrace r.downTrace
    (nativeOriginalUnitHomotopy.{uR, uM, uObj, uHom, uNative} R)
    (nativeUpDownZeroPath_homotopic_unitTrace.{uR, uM, uObj, uHom, uNative} R)
  let fL : A ⟶ A := r.down ≫ r.up
  let gL : A ⟶ A := 𝟙 A
  let fR : B ⟶ B := r.up ≫ r.down
  let gR : B ⟶ B := 𝟙 B
  have hfL : fL a = a := (congrArg r.up r.downPoint).trans r.upPoint
  have hgL : gL a = a := rfl
  have hfR : fR b = b := (congrArg r.down r.upPoint).trans r.downPoint
  have hgR : gR b = b := rfl
  let HLC : TopCat.Homotopy fL gL := HL.cast
    (TopCat.hom_comp r.down r.up).symm
    (show (𝟙 A : A ⟶ A).hom = ContinuousMap.id A from TopCat.hom_id).symm
  let HRC : TopCat.Homotopy fR gR := HR.cast
    (TopCat.hom_comp r.up r.down).symm
    (show (𝟙 B : B ⟶ B).hom = ContinuousMap.id B from TopCat.hom_id).symm
  have hNullLC : ((HLC.evalAt a).cast hfL.symm hgL.symm).Homotopic
      (_root_.Path.refl a) := by
    obtain ⟨K⟩ := hNullL
    have hSame :
        (HLC.evalAt a).cast hfL.symm hgL.symm =
          (HL.evalAt a).cast
            ((congrArg r.up.hom r.downPoint).trans r.upPoint).symm rfl := by
      apply _root_.Path.ext
      funext t
      rfl
    exact ⟨_root_.Path.Homotopy.cast K hSame.symm rfl⟩
  have hNullRC : ((HRC.evalAt b).cast hfR.symm hgR.symm).Homotopic
      (_root_.Path.refl b) := by
    obtain ⟨K⟩ := hNullR
    have hSame :
        (HRC.evalAt b).cast hfR.symm hgR.symm =
          (HR.evalAt b).cast
            ((congrArg r.down.hom r.upPoint).trans r.downPoint).symm rfl := by
      apply _root_.Path.ext
      funext t
      rfl
    exact ⟨_root_.Path.Homotopy.cast K hSame.symm rfl⟩
  obtain ⟨L⟩ := TopCat.exists_pointRelativeHomotopy_of_null_trace
    fL gL a a hfL hgL HLC (Classical.choice hNullLC)
  obtain ⟨T⟩ := TopCat.exists_pointRelativeHomotopy_of_null_trace
    fR gR b b hfR hgR HRC (Classical.choice hNullRC)
  exact ⟨
    { down := r.down
      up := r.up
      downPoint := r.downPoint
      upPoint := r.upPoint
      retuning := r.downRetuning
      retuningTrace := r.downTrace
      upRetuning := r.upRetuning
      upRetuningTrace := r.upTrace
      leftHomotopy := L
      rightHomotopy := T }⟩

/-- The based maps are chosen only after their original construction and both inverse families. -/
public def nativeRealizationData : NativeRealizationData.{uR, uM, uObj, uHom, uNative} R :=
  Classical.choice (nativeRealizationData_nonempty.{uR, uM, uObj, uHom, uNative} R)

/-- The actual pointed native realization at the original lifted Q-zero vertex. -/
public def nativePointedRealization :=
  Under.mk (TopCat.const (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R) :
    TopCat.of PUnit.{max (max (max (max uR uM + 1) uObj)
      (max (max uR uM) uHom)) uNative + 1} ⟶
        TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R))

/-- The same original small-projective Q-zero vertex in the common native carrier. -/
public def nativeCanonicalPointedRealization :=
  Under.mk (TopCat.const (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R) :
    TopCat.of PUnit.{max (max (max (max uR uM + 1) uObj)
      (max (max uR uM) uHom)) uNative + 1} ⟶
        TopCat.of (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R))

/-- The constructed native descent has its genuine strict pointed square. -/
public def nativeDownPointed :
    nativePointedRealization.{uR, uM, uObj, uHom, uNative} R ⟶
      nativeCanonicalPointedRealization.{uR, uM, uObj, uHom, uNative} R :=
  Under.homMk (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).down (by
    apply TopCat.ext
    intro _
    exact (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).downPoint)

/-- The constructed native inverse has its genuine strict pointed square. -/
public def nativeUpPointed :
    nativeCanonicalPointedRealization.{uR, uM, uObj, uHom, uNative} R ⟶
      nativePointedRealization.{uR, uM, uObj, uHom, uNative} R :=
  Under.homMk (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).up (by
    apply TopCat.ext
    intro _
    exact (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).upPoint)

/-- Original small-projective loops in the common native carrier. -/
public abbrev nativeCanonicalLoopSpace :=
  LoopSpace (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R)
    (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)

/-- Their literal constant loop at the original small-projective zero. -/
public def nativeCanonicalConstantLoop :
    nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R :=
  Path.refl (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)

/-- The strict loop map of the actual based native Q descent. -/
public def nativeLoopDown :
    C(nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R,
      nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R) :=
  (PointedTopCat.loopSpaceMap (nativeDownPointed.{uR, uM, uObj, uHom, uNative} R)).right.hom

/-- The strict loop map of its actual based native inverse. -/
public def nativeLoopUp :
    C(nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R,
      nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :=
  (PointedTopCat.loopSpaceMap (nativeUpPointed.{uR, uM, uObj, uHom, uNative} R)).right.hom

/-- The original native descent, with its actual Q-zero root and no retuning. -/
public def nativeUnretunedDownWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)
      (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R) where
  hom := (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom
  rootPath := nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R

/-- The original native inclusion, with its own actual Q-zero root and no retuning. -/
public def nativeUnretunedUpWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)
      (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R) where
  hom := (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom
  rootPath := nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R

private theorem nativeUnretunedDownWeaklyPointedValueComputed (R : Type uR) [Ring R] :
    nativeUnretunedDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R =
      (⟨(nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom,
        nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R⟩ :
        ContinuousMap.WeaklyPointed
          (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)
          (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)) := rfl

/-- The actual native weak descent retains its whole original hom and zero path. -/
public theorem nativeUnretunedDownWeaklyPointed_value (R : Type uR) [Ring R] :
    nativeUnretunedDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R =
      (⟨(nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom,
        nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R⟩ :
        ContinuousMap.WeaklyPointed
          (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)
          (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)) :=
  nativeUnretunedDownWeaklyPointedValueComputed.{uR, uM, uObj, uHom, uNative} R

private theorem nativeUnretunedUpWeaklyPointedValueComputed (R : Type uR) [Ring R] :
    nativeUnretunedUpWeaklyPointed.{uR, uM, uObj, uHom, uNative} R =
      (⟨(nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom,
        nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R⟩ :
        ContinuousMap.WeaklyPointed
          (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)
          (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)) := rfl

/-- The actual native weak inclusion retains its independently chosen hom and zero path. -/
public theorem nativeUnretunedUpWeaklyPointed_value (R : Type uR) [Ring R] :
    nativeUnretunedUpWeaklyPointed.{uR, uM, uObj, uHom, uNative} R =
      (⟨(nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom,
        nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R⟩ :
        ContinuousMap.WeaklyPointed
          (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)
          (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)) :=
  nativeUnretunedUpWeaklyPointedValueComputed.{uR, uM, uObj, uHom, uNative} R

private theorem nativeLoopDown_apply_computed
    (gamma : nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R)
    (t : unitInterval) :
    nativeLoopDown.{uR, uM, uObj, uHom, uNative} R gamma t =
      (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).down (gamma t) :=
  PointedTopCat.loopSpaceMap_apply
    (nativeDownPointed.{uR, uM, uObj, uHom, uNative} R) gamma t

private theorem nativeLoopUp_apply_computed
    (gamma : nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R)
    (t : unitInterval) :
    nativeLoopUp.{uR, uM, uObj, uHom, uNative} R gamma t =
      (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).up (gamma t) :=
  PointedTopCat.loopSpaceMap_apply
    (nativeUpPointed.{uR, uM, uObj, uHom, uNative} R) gamma t

/-- The complete strict native descent is retuned from the actual weak Q map.
This is one jointly continuous family on the entire original loop space. -/
private def nativeLoopDownRetuningHomotopyAux :
    ContinuousMap.Homotopy
      (nativeUnretunedDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap
      (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R) :=
  loopRetuningHomotopy
    (nativeUnretunedDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R)
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).down.hom
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).downPoint
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).retuning
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).retuningTrace
    (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R)
    (nativeLoopDown_apply_computed.{uR, uM, uObj, uHom, uNative} R)

/-- The actual down retuning supplies a joint homotopy on the whole loop space. -/
public def nativeLoopDownRetuningHomotopy :
    ContinuousMap.Homotopy
      (nativeUnretunedDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap
      (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R) :=
  nativeLoopDownRetuningHomotopyAux.{uR, uM, uObj, uHom, uNative} R

/-- The complete strict native inclusion is retuned from the actual weak Q map.
The upward trace is retained independently of the descended map. -/
private def nativeLoopUpRetuningHomotopyAux :
    ContinuousMap.Homotopy
      (nativeUnretunedUpWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap
      (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R) :=
  loopRetuningHomotopy
    (nativeUnretunedUpWeaklyPointed.{uR, uM, uObj, uHom, uNative} R)
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).up.hom
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).upPoint
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).upRetuning
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).upRetuningTrace
    (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R)
    (nativeLoopUp_apply_computed.{uR, uM, uObj, uHom, uNative} R)

/-- The actual up retuning supplies a joint homotopy on the whole loop space. -/
public def nativeLoopUpRetuningHomotopy :
    ContinuousMap.Homotopy
      (nativeUnretunedUpWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap
      (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R) :=
  nativeLoopUpRetuningHomotopyAux.{uR, uM, uObj, uHom, uNative} R

private theorem nativeLoopDownRetuningHomotopyUnitValueComputed
    (R : Type uR) [Ring R] (t s : unitInterval) :
    (((nativeLoopDownRetuningHomotopy.{uR, uM, uObj, uHom, uNative} R).toContinuousMap.toFun
      (t, nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R)).toContinuousMap).toFun s =
      (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R).toContinuousMap.toFun
        (ContinuousMap.Homotopy.traceConjugationLoopHomotopy
          ContinuousMap.Homotopy.intervalCoordinateHomotopy (0 : unitInterval)
          (t, Path.refl (0 : unitInterval)) s) := by
  unfold nativeLoopDownRetuningHomotopy nativeLoopDownRetuningHomotopyAux nativeConstantLoop
  exact loopRetuningHomotopy_unit_value
    (nativeUnretunedDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R)
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).down.hom
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).downPoint
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).retuning
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).retuningTrace
    (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R)
    (nativeLoopDown_apply_computed.{uR, uM, uObj, uHom, uNative} R) t s

/-- Every original downward unit time and loop time retains its original zero-trace template. -/
public theorem nativeLoopDownRetuningHomotopy_unit_value
    (R : Type uR) [Ring R] (t s : unitInterval) :
    (((nativeLoopDownRetuningHomotopy.{uR, uM, uObj, uHom, uNative} R).toContinuousMap.toFun
      (t, nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R)).toContinuousMap).toFun s =
      (nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R).toContinuousMap.toFun
        (ContinuousMap.Homotopy.traceConjugationLoopHomotopy
          ContinuousMap.Homotopy.intervalCoordinateHomotopy (0 : unitInterval)
          (t, Path.refl (0 : unitInterval)) s) :=
  nativeLoopDownRetuningHomotopyUnitValueComputed.{uR, uM, uObj, uHom, uNative} R t s

private theorem nativeLoopUpRetuningHomotopyUnitValueComputed
    (R : Type uR) [Ring R] (t s : unitInterval) :
    (((nativeLoopUpRetuningHomotopy.{uR, uM, uObj, uHom, uNative} R).toContinuousMap.toFun
      (t, nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R)).toContinuousMap).toFun s =
      (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R).toContinuousMap.toFun
        (ContinuousMap.Homotopy.traceConjugationLoopHomotopy
          ContinuousMap.Homotopy.intervalCoordinateHomotopy (0 : unitInterval)
          (t, Path.refl (0 : unitInterval)) s) := by
  unfold nativeLoopUpRetuningHomotopy nativeLoopUpRetuningHomotopyAux nativeCanonicalConstantLoop
  exact loopRetuningHomotopy_unit_value
    (nativeUnretunedUpWeaklyPointed.{uR, uM, uObj, uHom, uNative} R)
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).up.hom
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).upPoint
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).upRetuning
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).upRetuningTrace
    (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R)
    (nativeLoopUp_apply_computed.{uR, uM, uObj, uHom, uNative} R) t s

/-- Every original upward unit time and loop time retains its independently derived zero trace. -/
public theorem nativeLoopUpRetuningHomotopy_unit_value
    (R : Type uR) [Ring R] (t s : unitInterval) :
    (((nativeLoopUpRetuningHomotopy.{uR, uM, uObj, uHom, uNative} R).toContinuousMap.toFun
      (t, nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R)).toContinuousMap).toFun s =
      (nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R).toContinuousMap.toFun
        (ContinuousMap.Homotopy.traceConjugationLoopHomotopy
          ContinuousMap.Homotopy.intervalCoordinateHomotopy (0 : unitInterval)
          (t, Path.refl (0 : unitInterval)) s) :=
  nativeLoopUpRetuningHomotopyUnitValueComputed.{uR, uM, uObj, uHom, uNative} R t s

/-- The actual native descent preserves the literal constant loop. -/
public theorem nativeLoopDown_constant :
    nativeLoopDown.{uR, uM, uObj, uHom, uNative} R
        (nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R) =
      nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R :=
  PointedTopCat.map_basepoint
    (PointedTopCat.loopSpaceMap (nativeDownPointed.{uR, uM, uObj, uHom, uNative} R))

/-- The actual native inverse preserves the literal constant loop. -/
public theorem nativeLoopUp_constant :
    nativeLoopUp.{uR, uM, uObj, uHom, uNative} R
        (nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R) =
      nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R :=
  PointedTopCat.map_basepoint
    (PointedTopCat.loopSpaceMap (nativeUpPointed.{uR, uM, uObj, uHom, uNative} R))

/-- The original source inverse family loops pointwise and fixes the constant loop. -/
public def nativeLoopLeftHomotopyRel :
    ContinuousMap.HomotopyRel
      ((nativeLoopUp.{uR, uM, uObj, uHom, uNative} R).comp
        (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R))
      (ContinuousMap.id (nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R))
      {nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R} := by
  let f := nativeDownPointed.{uR, uM, uObj, uHom, uNative} R
  let g := nativeUpPointed.{uR, uM, uObj, uHom, uNative} R
  let X := nativePointedRealization.{uR, uM, uObj, uHom, uNative} R
  let H := PointedTopCat.loopSpaceMapHomotopyRel
    (X := X) (Y := X) (f₀ := f ≫ g) (f₁ := 𝟙 X)
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).leftHomotopy
  have hstart : (PointedTopCat.loopSpaceMap (f ≫ g)).right.hom =
      (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R).comp
        (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R) := by
    rw [PointedTopCat.loopSpaceMap_comp]
    rfl
  have hend : (PointedTopCat.loopSpaceMap (𝟙 X)).right.hom =
      ContinuousMap.id (nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) := by
    rw [PointedTopCat.loopSpaceMap_id]
    rfl
  exact H.cast hstart hend

/-- The original target inverse family loops pointwise and fixes the constant loop. -/
public def nativeLoopRightHomotopyRel :
    ContinuousMap.HomotopyRel
      ((nativeLoopDown.{uR, uM, uObj, uHom, uNative} R).comp
        (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R))
      (ContinuousMap.id (nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R))
      {nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R} := by
  let f := nativeUpPointed.{uR, uM, uObj, uHom, uNative} R
  let g := nativeDownPointed.{uR, uM, uObj, uHom, uNative} R
  let X := nativeCanonicalPointedRealization.{uR, uM, uObj, uHom, uNative} R
  let H := PointedTopCat.loopSpaceMapHomotopyRel
    (X := X) (Y := X) (f₀ := f ≫ g) (f₁ := 𝟙 X)
    (nativeRealizationData.{uR, uM, uObj, uHom, uNative} R).rightHomotopy
  have hstart : (PointedTopCat.loopSpaceMap (f ≫ g)).right.hom =
      (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R).comp
        (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R) := by
    rw [PointedTopCat.loopSpaceMap_comp]
    rfl
  have hend : (PointedTopCat.loopSpaceMap (𝟙 X)).right.hom =
      ContinuousMap.id (nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R) := by
    rw [PointedTopCat.loopSpaceMap_id]
    rfl
  exact H.cast hstart hend

/-- The actual based native realization transport induces the actual loop equivalence. -/
public def nativeLoopHomotopyEquiv :
    nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R ≃ₕ
      nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R where
  toFun := nativeLoopDown.{uR, uM, uObj, uHom, uNative} R
  invFun := nativeLoopUp.{uR, uM, uObj, uHom, uNative} R
  left_inv := ⟨(nativeLoopLeftHomotopyRel.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩
  right_inv := ⟨(nativeLoopRightHomotopyRel.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩

/-- Project the common native small-projective loop carrier to its original carrier. -/
public def canonicalCarrierDown :
    C(nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R,
      canonicalLoops.{uR, uM} R) :=
  ContinuousMap.strictLoopMap
    (Homeomorph.ulift : nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R ≃ₜ
      NQReal (canonicalCategory.{uR, uM} R)).toHomotopyEquiv.toFun
    (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)

/-- Include the original small-projective loops in that same native carrier. -/
public def canonicalCarrierUp :
    C(canonicalLoops.{uR, uM} R,
      nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R) :=
  ContinuousMap.strictLoopMap
    (Homeomorph.ulift.symm : NQReal (canonicalCategory.{uR, uM} R) ≃ₜ
      nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R).toHomotopyEquiv.toFun
    (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))

private theorem canonicalCarrierDownApplyComputed (R : Type uR) [Ring R]
    (gamma : nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R) (t : unitInterval) :
    canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R gamma t = (gamma t).down := by
  let f : C(nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R,
      NQReal (canonicalCategory.{uR, uM} R)) :=
    (Homeomorph.ulift : nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R ≃ₜ
      NQReal (canonicalCategory.{uR, uM} R)).toHomotopyEquiv.toFun
  exact congrArg (fun p : LoopSpace (NQReal (canonicalCategory.{uR, uM} R))
      (f (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R)) => p t)
    (ContinuousMap.strictLoopMap_apply f
      (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R) gamma)

/-- The original canonical carrier projection retains every original loop value. -/
public theorem canonicalCarrierDown_apply (R : Type uR) [Ring R]
    (gamma : nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R) (t : unitInterval) :
    canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R gamma t = (gamma t).down :=
  canonicalCarrierDownApplyComputed.{uR, uM, uObj, uHom, uNative} R gamma t

private theorem canonicalCarrierUpApplyComputed (R : Type uR) [Ring R]
    (gamma : canonicalLoops.{uR, uM} R) (t : unitInterval) :
    canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R gamma t = ULift.up (gamma t) := by
  let f : C(NQReal (canonicalCategory.{uR, uM} R),
      nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R) :=
    (Homeomorph.ulift.symm : NQReal (canonicalCategory.{uR, uM} R) ≃ₜ
      nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R).toHomotopyEquiv.toFun
  exact congrArg (fun p : LoopSpace
      (nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R)
      (f (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))) => p t)
    (ContinuousMap.strictLoopMap_apply f
      (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R)) gamma)

/-- The original canonical carrier inclusion retains every original loop value. -/
public theorem canonicalCarrierUp_apply (R : Type uR) [Ring R]
    (gamma : canonicalLoops.{uR, uM} R) (t : unitInterval) :
    canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R gamma t = ULift.up (gamma t) :=
  canonicalCarrierUpApplyComputed.{uR, uM, uObj, uHom, uNative} R gamma t

/-- Canonical projection preserves the original literal constant loop. -/
public theorem canonicalCarrierDown_constant :
    canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R
        (nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R) =
      canonicalConstantLoop.{uR, uM} R := ContinuousMap.strictLoopMap_refl _ _

/-- Canonical inclusion preserves the same original literal constant loop. -/
public theorem canonicalCarrierUp_constant :
    canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R
        (canonicalConstantLoop.{uR, uM} R) =
      nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R :=
  ContinuousMap.strictLoopMap_refl _ _

/-- Canonical inclusion after projection is the actual native identity. -/
public theorem canonicalCarrierUp_comp_down :
    (canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R).comp
        (canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R) =
      ContinuousMap.id (nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R) := by
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  funext t
  exact ULift.up_down (gamma t)

/-- Canonical projection after inclusion is the actual original identity. -/
public theorem canonicalCarrierDown_comp_up :
    (canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
        (canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R) =
      ContinuousMap.id (canonicalLoops.{uR, uM} R) := by
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  rfl

private def canonicalCarrierLeftHomotopyRel :
    ContinuousMap.HomotopyRel
      ((canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R).comp
        (canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R))
      (ContinuousMap.id (nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R))
      {nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R} :=
  (ContinuousMap.HomotopyRel.refl
    (ContinuousMap.id (nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R))
    {nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R}).cast
      (canonicalCarrierUp_comp_down.{uR, uM, uObj, uHom, uNative} R).symm rfl

private def canonicalCarrierRightHomotopyRel :
    ContinuousMap.HomotopyRel
      ((canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
        (canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R))
      (ContinuousMap.id (canonicalLoops.{uR, uM} R)) {canonicalConstantLoop.{uR, uM} R} :=
  (ContinuousMap.HomotopyRel.refl
    (ContinuousMap.id (canonicalLoops.{uR, uM} R)) {canonicalConstantLoop.{uR, uM} R}).cast
      (canonicalCarrierDown_comp_up.{uR, uM, uObj, uHom, uNative} R).symm rfl

private def canonicalCarrierHomotopyEquiv :
    nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R ≃ₕ
      canonicalLoops.{uR, uM} R where
  toFun := canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R
  invFun := canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R
  left_inv := ⟨(canonicalCarrierLeftHomotopyRel.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩
  right_inv := ⟨(canonicalCarrierRightHomotopyRel.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩

/-- The actual native Q loop space is equivalent to the entire original small-projective loop space. -/
public def QloopHomotopyEquiv :
    nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R ≃ₕ canonicalLoops.{uR, uM} R :=
  (nativeLoopHomotopyEquiv.{uR, uM, uObj, uHom, uNative} R).trans
    (canonicalCarrierHomotopyEquiv.{uR, uM, uObj, uHom, uNative} R)

/-- Actual native Q descent to the entire original small-projective loop carrier. -/
public def Qdown :
    C(nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R, canonicalLoops.{uR, uM} R) :=
  (QloopHomotopyEquiv.{uR, uM, uObj, uHom, uNative} R).toFun

/-- Its actual continuous inverse on the entire original small-projective loop carrier. -/
public def Qup :
    C(canonicalLoops.{uR, uM} R, nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :=
  (QloopHomotopyEquiv.{uR, uM, uObj, uHom, uNative} R).invFun

/-- Native descent sends the original literal constant loop to the original constant loop. -/
public theorem Qdown_constant :
    Qdown.{uR, uM, uObj, uHom, uNative} R
        (nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R) =
      canonicalConstantLoop.{uR, uM} R :=
  (congrArg (canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R)
    (nativeLoopDown_constant.{uR, uM, uObj, uHom, uNative} R)).trans
      (canonicalCarrierDown_constant.{uR, uM, uObj, uHom, uNative} R)

/-- Native inclusion sends the same original constant loop to the literal native constant loop. -/
public theorem Qup_constant :
    Qup.{uR, uM, uObj, uHom, uNative} R (canonicalConstantLoop.{uR, uM} R) =
      nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R :=
  (congrArg (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R)
    (canonicalCarrierUp_constant.{uR, uM, uObj, uHom, uNative} R)).trans
      (nativeLoopUp_constant.{uR, uM, uObj, uHom, uNative} R)

/-- The complete original native inverse family fixes the literal native constant loop. -/
public def QleftHomotopyRel :
    ContinuousMap.HomotopyRel
      ((Qup.{uR, uM, uObj, uHom, uNative} R).comp
        (Qdown.{uR, uM, uObj, uHom, uNative} R))
      (ContinuousMap.id (nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R))
      {nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R} :=
  ContinuousMap.HomotopyEquiv.transLeftHomotopyRel
    (nativeLoopHomotopyEquiv.{uR, uM, uObj, uHom, uNative} R)
    (canonicalCarrierHomotopyEquiv.{uR, uM, uObj, uHom, uNative} R)
    (nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R)
    (nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R)
    (nativeLoopDown_constant.{uR, uM, uObj, uHom, uNative} R)
    (nativeLoopLeftHomotopyRel.{uR, uM, uObj, uHom, uNative} R)
    (canonicalCarrierLeftHomotopyRel.{uR, uM, uObj, uHom, uNative} R)

/-- The complete original target inverse family fixes the literal original constant loop. -/
public def QrightHomotopyRel :
    ContinuousMap.HomotopyRel
      ((Qdown.{uR, uM, uObj, uHom, uNative} R).comp
        (Qup.{uR, uM, uObj, uHom, uNative} R))
      (ContinuousMap.id (canonicalLoops.{uR, uM} R)) {canonicalConstantLoop.{uR, uM} R} :=
  ContinuousMap.HomotopyEquiv.transRightHomotopyRel
    (nativeLoopHomotopyEquiv.{uR, uM, uObj, uHom, uNative} R)
    (canonicalCarrierHomotopyEquiv.{uR, uM, uObj, uHom, uNative} R)
    (nativeCanonicalConstantLoop.{uR, uM, uObj, uHom, uNative} R)
    (canonicalConstantLoop.{uR, uM} R)
    (canonicalCarrierUp_constant.{uR, uM, uObj, uHom, uNative} R)
    (nativeLoopRightHomotopyRel.{uR, uM, uObj, uHom, uNative} R)
    (canonicalCarrierRightHomotopyRel.{uR, uM, uObj, uHom, uNative} R)

private theorem canonicalCarrierDown_nativeWeakLoop :
    (canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
        (nativeUnretunedDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap =
      (qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap.comp
        (rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R) := by
  let p := qDownZeroPath.{uR, uM, uObj, uHom} R
  let pN := nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R
  let f := qRealizationDown.{uR, uM, uObj, uHom} R
  let fN := (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom
  apply ContinuousMap.ext
  intro gamma
  apply _root_.Path.ext
  funext t
  change ((pN.symm.trans ((gamma.map fN.continuous).trans pN)) t).down =
    (p.symm.trans
      (((rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R gamma).map
        f.continuous).trans p)) t
  rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
  split_ifs with ht
  · rfl
  · rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
    split_ifs with hs
    · exact congrArg ULift.down
        (nativeUnretunedDown_apply.{uR, uM, uObj, uHom, uNative} R _)
    · rfl

private theorem nativeWeakLoopUp_canonicalCarrierUp :
    (nativeUnretunedUpWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap.comp
        (canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R) =
      (rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R).comp
        (qUpWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap := by
  let p := qUpZeroPath.{uR, uM, uObj, uHom} R
  let pN := nativeUpZeroPath.{uR, uM, uObj, uHom, uNative} R
  let f := qRealizationUp.{uR, uM, uObj, uHom} R
  let fN := (nativeUnretunedUp.{uR, uM, uObj, uHom, uNative} R).hom
  apply ContinuousMap.ext
  intro gamma
  apply _root_.Path.ext
  funext t
  change (pN.symm.trans
      ((((canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R) gamma).map
        fN.continuous).trans pN)) t =
    ULift.up ((p.symm.trans ((gamma.map f.continuous).trans p)) t)
  rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
  split_ifs with ht
  · rfl
  · rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
    split_ifs with hs
    · exact nativeUnretunedUp_apply.{uR, uM, uObj, uHom, uNative} R _
    · rfl

private theorem Qdown_map_computed :
    (canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
        (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R) =
      Qdown.{uR, uM, uObj, uHom, uNative} R := rfl

private theorem Qup_map_computed :
    (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R).comp
        (canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R) =
      Qup.{uR, uM, uObj, uHom, uNative} R := rfl

/-- The whole original Q descent uses the same native loop map and carrier projection. -/
public theorem Qdown_value :
    Qdown.{uR, uM, uObj, uHom, uNative} R =
      (canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
        (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R) :=
  (Qdown_map_computed.{uR, uM, uObj, uHom, uNative} R).symm

/-- The whole original Q inclusion retains its independently chosen native loop inverse. -/
public theorem Qup_value :
    Qup.{uR, uM, uObj, uHom, uNative} R =
      (nativeLoopUp.{uR, uM, uObj, uHom, uNative} R).comp
        (canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R) :=
  (Qup_map_computed.{uR, uM, uObj, uHom, uNative} R).symm

/-- The whole strict native descent is canonically retuned from the original
category-induced Q-down loop map, with its actual chosen-zero root path. -/
private def QdownRetuningHomotopyAux :
    ContinuousMap.Homotopy (Qdown.{uR, uM, uObj, uHom, uNative} R)
      ((qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap.comp
        (rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R)) := by
  let K := (ContinuousMap.Homotopy.refl
    (canonicalCarrierDown.{uR, uM, uObj, uHom, uNative} R)).comp
      (nativeLoopDownRetuningHomotopy.{uR, uM, uObj, uHom, uNative} R).symm
  exact K.cast (Qdown_map_computed.{uR, uM, uObj, uHom, uNative} R)
    (canonicalCarrierDown_nativeWeakLoop.{uR, uM, uObj, uHom, uNative} R)

/-- Descent has a joint homotopy to the exact original weak Q-down loop map. -/
public def QdownRetuningHomotopy :
    ContinuousMap.Homotopy (Qdown.{uR, uM, uObj, uHom, uNative} R)
      ((qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap.comp
        (rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R)) :=
  QdownRetuningHomotopyAux.{uR, uM, uObj, uHom, uNative} R

/-- The whole strict native inclusion is canonically retuned from the original
category-induced Q-up loop map, with its independently retained zero root.
This family is built from the actual up retuning, not an arbitrary based inverse. -/
private def QupRetuningHomotopyAux :
    ContinuousMap.Homotopy (Qup.{uR, uM, uObj, uHom, uNative} R)
      ((rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R).comp
        (qUpWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap) := by
  let K := ((nativeLoopUpRetuningHomotopy.{uR, uM, uObj, uHom, uNative} R).symm).compContinuousMap
    (canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R)
  exact K.cast (Qup_map_computed.{uR, uM, uObj, uHom, uNative} R)
    (nativeWeakLoopUp_canonicalCarrierUp.{uR, uM, uObj, uHom, uNative} R)

/-- Inclusion has a joint homotopy to the exact original weak Q-up loop map. -/
public def QupRetuningHomotopy :
    ContinuousMap.Homotopy (Qup.{uR, uM, uObj, uHom, uNative} R)
      ((rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R).comp
        (qUpWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap) :=
  QupRetuningHomotopyAux.{uR, uM, uObj, uHom, uNative} R

private def nativeDownWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R)
      (nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R) where
  hom := (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom
  rootPath := nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R

private theorem nativeLoopDown_homotopic_unretuned
    (gamma : nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    Path.Homotopic (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R gamma)
      ((nativeDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap gamma) := by
  let A := nativeRealization.{uR, uM, uObj, uHom, uNative} R
  let B := nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R
  let a : A := nativeBasepoint.{uR, uM, uObj, uHom, uNative} R
  let b : B := nativeCanonicalBasepoint.{uR, uM, uObj, uHom, uNative} R
  let d := nativeRealizationData.{uR, uM, uObj, uHom, uNative} R
  let f : C(A, B) := (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom
  let p : Path (f a) b := nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R
  let q : FundamentalGroup A a := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)
  let qf : FundamentalGroup B (f a) := FundamentalGroup.mapOfEq f rfl q
  let pp : Path.Homotopic.Quotient (f a) b := Path.Homotopic.Quotient.mk p
  let alpha : FundamentalGroupoid.mk (f a) ≅ FundamentalGroupoid.mk b :=
    (Groupoid.isoEquivHom (FundamentalGroupoid.mk (f a)) (FundamentalGroupoid.mk b)).symm pp
  have htrace : (d.retuning.evalAt a).cast rfl d.downPoint.symm = p := by
    apply Path.ext
    funext t
    exact d.retuningTrace t
  have hn := FundamentalGroup.mapOfEq_homotopy_naturality d.retuning a
    (rfl : f a = f a) d.downPoint q
  rw [htrace] at hn
  have hq := congrArg (fun r : FundamentalGroup B b => r.asHom) hn
  have hMapped : qf.asHom = Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk gamma) f := by
    have h := congrArg (fun r : FundamentalGroup B (f a) => r.asHom)
      (FundamentalGroup.mapOfEq_apply f (rfl : f a = f a) q)
    simpa only [Path.Homotopic.Quotient.cast_rfl_rfl] using h
  have hConj : (FundamentalGroup.fundamentalGroupMulEquivOfPath p qf).asHom =
      pp.symm.trans (qf.asHom.trans pp) :=
    Iso.conj_apply_asHom alpha qf
  have hLeft : (FundamentalGroup.fundamentalGroupMulEquivOfPath p qf).asHom =
      pp.symm.trans
        ((Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk gamma) f).trans pp) :=
    hConj.trans
      (congrArg (fun r : Path.Homotopic.Quotient (f a) (f a) => pp.symm.trans (r.trans pp))
        hMapped)
  have hRight : (FundamentalGroup.mapOfEq d.down.hom d.downPoint q).asHom =
      (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk gamma) d.down.hom).cast
        d.downPoint.symm d.downPoint.symm :=
    congrArg (fun r : FundamentalGroup B b => r.asHom)
      (FundamentalGroup.mapOfEq_apply d.down.hom d.downPoint q)
  have hClass : pp.symm.trans
      ((Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk gamma) f).trans pp) =
        (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk gamma) d.down.hom).cast
          d.downPoint.symm d.downPoint.symm :=
    hLeft.symm.trans (hq.trans hRight)
  have hdown : nativeLoopDown.{uR, uM, uObj, uHom, uNative} R gamma =
      (gamma.map d.down.hom.continuous).cast d.downPoint.symm d.downPoint.symm := by
    apply Path.ext
    rfl
  have hdownClass :
      Path.Homotopic.Quotient.mk (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R gamma) =
        (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk gamma) d.down.hom).cast
          d.downPoint.symm d.downPoint.symm := by
    rw [hdown, Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_map]
  have hweakClass : Path.Homotopic.Quotient.mk
      ((nativeDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap gamma) =
        pp.symm.trans
          ((Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk gamma) f).trans pp) := by
    let W : ContinuousMap.WeaklyPointed a b := { hom := f, rootPath := p }
    have hRecord : nativeDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R = W := rfl
    have hLoop :
        (nativeDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap gamma =
          W.loopMap gamma :=
      congrArg (fun w : ContinuousMap.WeaklyPointed a b => w.loopMap gamma) hRecord
    have hFormula : W.loopMap gamma = p.symm.trans ((gamma.map f.continuous).trans p) :=
      ContinuousMap.WeaklyPointed.loopMap_apply W gamma
    have hRecipeClass : Path.Homotopic.Quotient.mk (W.loopMap gamma) =
        pp.symm.trans
          ((Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk gamma) f).trans pp) := by
      calc
        Path.Homotopic.Quotient.mk (W.loopMap gamma) =
            Path.Homotopic.Quotient.mk (p.symm.trans ((gamma.map f.continuous).trans p)) :=
          congrArg (fun q : Path b b => Path.Homotopic.Quotient.mk q) hFormula
        _ = pp.symm.trans
            ((Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk gamma) f).trans pp) := by
          rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
            Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_map]
    exact (congrArg (fun q : Path b b => Path.Homotopic.Quotient.mk q) hLoop).trans hRecipeClass
  exact Path.Homotopic.Quotient.eq.mp
    (hdownClass.trans (hClass.symm.trans hweakClass.symm))

/-- Every original loop is descended by the actual Q map and its canonical zero path.
The strict retuning keeps this original component action; no evaluator is
defined through the chosen homotopy equivalence. -/
public theorem Qdown_homotopic_weaklyPointed
    (gamma : nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    Path.Homotopic (Qdown.{uR, uM, uObj, uHom, uNative} R gamma)
      ((qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap
        (rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R gamma)) := by
  let A0 := NQReal (liftedCategory.{uR, uM, uObj, uHom} R)
  let B0 := NQReal (canonicalCategory.{uR, uM} R)
  let a0 : A0 := OriginalQZeroComparison.zeroQVertex
    (C := liftedCategory.{uR, uM, uObj, uHom} R)
  let b0 : B0 := OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R)
  let fd : C(A0, B0) := qRealizationDown.{uR, uM, uObj, uHom} R
  let c : C(nativeCanonicalRealization.{uR, uM, uObj, uHom, uNative} R, B0) :=
    Homeomorph.ulift.toHomotopyEquiv.toFun
  let pN := nativeDownZeroPath.{uR, uM, uObj, uHom, uNative} R
  let p0 : Path (fd a0) b0 := qDownZeroPath.{uR, uM, uObj, uHom} R
  let gamma0 : LoopSpace A0 a0 := rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R gamma
  let fN := (nativeUnretunedDown.{uR, uM, uObj, uHom, uNative} R).hom
  have h := (nativeLoopDown_homotopic_unretuned.{uR, uM, uObj, uHom, uNative} R gamma).map c
  have hleft : (nativeLoopDown.{uR, uM, uObj, uHom, uNative} R gamma).map c.continuous =
      Qdown.{uR, uM, uObj, uHom, uNative} R gamma := by
    apply Path.ext
    rfl
  have hroot : pN.map c.continuous = p0 := by
    apply Path.ext
    rfl
  have hmap : (gamma.map fN.continuous).map c.continuous = gamma0.map fd.continuous := by
    apply Path.ext
    rfl
  have hNative : (nativeDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap gamma =
      pN.symm.trans ((gamma.map fN.continuous).trans pN) :=
    ContinuousMap.WeaklyPointed.loopMap_apply _ _
  have hOriginal : (qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap gamma0 =
      p0.symm.trans ((gamma0.map fd.continuous).trans p0) :=
    ContinuousMap.WeaklyPointed.loopMap_apply _ _
  have hMapped : (pN.symm.trans ((gamma.map fN.continuous).trans pN)).map c.continuous =
      (pN.map c.continuous).symm.trans
        (((gamma.map fN.continuous).map c.continuous).trans (pN.map c.continuous)) := by
    rw [Path.map_trans, Path.map_trans, Path.map_symm]
  have hTarget := congrArg₂
    (fun (p : Path (fd a0) b0) (q : Path (fd a0) (fd a0)) => p.symm.trans (q.trans p))
    hroot hmap
  have hright :
      ((nativeDownWeaklyPointed.{uR, uM, uObj, uHom, uNative} R).loopMap gamma).map c.continuous =
        (qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap gamma0 :=
    (congrArg (fun p : nativeCanonicalLoopSpace.{uR, uM, uObj, uHom, uNative} R =>
      p.map c.continuous) hNative).trans (hMapped.trans (hTarget.trans hOriginal.symm))
  obtain ⟨H⟩ := h
  exact ⟨Path.Homotopy.cast H hleft hright⟩

/-- The actual native Q descent has exactly the original canonical component action
at every loop, including every component represented by a non-generator loop. -/
public theorem Qdown_components
    (gamma : nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    ZerothHomotopy.mk (Qdown.{uR, uM, uObj, uHom, uNative} R gamma) =
      ZerothHomotopy.mk ((qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap
        (rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R gamma)) := by
  apply (loopComponentsEquivFundamentalGroup
    (NQReal (canonicalCategory.{uR, uM} R))
    (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))).injective
  rw [loopComponentsEquivFundamentalGroup_mk, loopComponentsEquivFundamentalGroup_mk]
  apply CategoryTheory.End.ext
  exact Path.Homotopic.Quotient.eq.mpr
    (Qdown_homotopic_weaklyPointed.{uR, uM, uObj, uHom, uNative} R gamma)

private theorem generatorConjugationCancellation {Y : Type*} [TopologicalSpace Y]
    {a b c : Y} (p : Path a b) (u v : Path b c) :
    (p.symm.trans (((p.trans u).trans (p.trans v).symm).trans p)).Homotopic
      (u.trans v.symm) := by
  apply Path.Homotopic.Quotient.eq.mp
  simp only [Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  simp only [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

private theorem generatorFromMappedEdges {Y : Type*} [TopologicalSpace Y]
    {a b c : Y} (p : Path a b) (m e : Path a c) (u v : Path b c)
    (hm : m.Homotopic (p.trans u)) (he : e.Homotopic (p.trans v)) :
    (p.symm.trans ((m.trans e.symm).trans p)).Homotopic (u.trans v.symm) := by
  exact ((Path.Homotopic.refl p.symm).hcomp
    ((hm.hcomp he.symm₂).hcomp (Path.Homotopic.refl p))).trans
      (generatorConjugationCancellation p u v)

/-- The actual Q descent preserves the original mono-forward/epi-reversed
generator loop after its canonically derived chosen-zero path. -/
public theorem qDownWeaklyPointed_generator (R : Type uR) [Ring R]
    (X : liftedCategory.{uR, uM, uObj, uHom} R) :
    Path.Homotopic
      ((qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap (generatorLoop X))
      (generatorLoop
        ((FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj X)) := by
  let E := qCategoryEquivalence.{uR, uM, uObj, uHom} R
  let F := qDownFunctor.{uR, uM, uObj, uHom} R
  let f := qRealizationDown.{uR, uM, uObj, uHom} R
  let A := (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj X
  have hFunctor : E.inverse = F := rfl
  have hReal : f = (CategoryTheory.realizedNerveEquivalence E).invFun := by
    change (qRealizationHomotopyEquiv.{uR, uM, uObj, uHom} R).invFun =
      (CategoryTheory.realizedNerveEquivalence E).invFun
    rfl
  have hObject : F.obj
      (⟨X⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)) =
        (⟨A⟩ : QuillenQ (canonicalCategory.{uR, uM} R)) :=
    qDownFunctor_obj.{uR, uM, uObj, uHom} R X
  let p := qDownZeroPath.{uR, uM, uObj, uHom} R
  let m := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (ExtensionCategory.zeroMonoHom X)))
  let e := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (ExtensionCategory.zeroEpiHom X)))
  let mp := m.map f.continuous
  let ep := e.map f.continuous
  let md := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (ExtensionCategory.zeroMonoHom A)))
  let ed := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (ExtensionCategory.zeroEpiHom A)))
  have h0 := qRealizationDown_vertex.{uR, uM, uObj, uHom} R
    (⟨0⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R))
  have hXBase := qRealizationDown_vertex.{uR, uM, uObj, uHom} R
    (⟨X⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R))
  have hVertexObject :
      SSet.realizedVertex (X := NQ (canonicalCategory.{uR, uM} R))
          ((nerveEquiv (C := QuillenQ (canonicalCategory.{uR, uM} R))).symm
            (F.obj (⟨X⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)))) =
        SSet.realizedVertex (X := NQ (canonicalCategory.{uR, uM} R))
          ((nerveEquiv (C := QuillenQ (canonicalCategory.{uR, uM} R))).symm
            (⟨A⟩ : QuillenQ (canonicalCategory.{uR, uM} R))) :=
    congrArg (fun Y : QuillenQ (canonicalCategory.{uR, uM} R) =>
      SSet.realizedVertex (X := NQ (canonicalCategory.{uR, uM} R))
        ((nerveEquiv (C := QuillenQ (canonicalCategory.{uR, uM} R))).symm Y)) hObject
  have hX : f (SSet.realizedVertex (ComposableArrows.mk₀
        (⟨X⟩ : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)))) =
      SSet.realizedVertex (ComposableArrows.mk₀
        (⟨A⟩ : QuillenQ (canonicalCategory.{uR, uM} R))) :=
    hXBase.trans hVertexObject
  let u := md.cast rfl hX
  let v := ed.cast rfl hX
  have hFunctorEdgeCast
      (G G' : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R) ⥤
        QuillenQ (canonicalCategory.{uR, uM} R))
      (h : G = G') {x y : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)}
      (g : x ⟶ y) :
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := QuillenQ (canonicalCategory.{uR, uM} R))
          (x := G.obj x) (y := G.obj y) (G.map g)))).cast
        (congrArg (fun Z : QuillenQ (canonicalCategory.{uR, uM} R) =>
          SSet.realizedVertex (X := NQ (canonicalCategory.{uR, uM} R))
            ((nerveEquiv (C := QuillenQ (canonicalCategory.{uR, uM} R))).symm Z))
          (Functor.congr_obj h x)).symm
        (congrArg (fun Z : QuillenQ (canonicalCategory.{uR, uM} R) =>
          SSet.realizedVertex (X := NQ (canonicalCategory.{uR, uM} R))
            ((nerveEquiv (C := QuillenQ (canonicalCategory.{uR, uM} R))).symm Z))
          (Functor.congr_obj h y)).symm) =
        TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (C := QuillenQ (canonicalCategory.{uR, uM} R))
            (x := G'.obj x) (y := G'.obj y) (G'.map g))) := by
    cases h
    rfl
  have hMappedEdge {x y : QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)}
      (g : x ⟶ y)
      (hx : f (SSet.realizedVertex (X := NQ (liftedCategory.{uR, uM, uObj, uHom} R))
        ((nerveEquiv (C := QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R))).symm x)) =
          SSet.realizedVertex (X := NQ (canonicalCategory.{uR, uM} R))
            ((nerveEquiv (C := QuillenQ (canonicalCategory.{uR, uM} R))).symm
              (F.obj x)))
      (hy : f (SSet.realizedVertex (X := NQ (liftedCategory.{uR, uM, uObj, uHom} R))
        ((nerveEquiv (C := QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R))).symm y)) =
          SSet.realizedVertex (X := NQ (canonicalCategory.{uR, uM} R))
            ((nerveEquiv (C := QuillenQ (canonicalCategory.{uR, uM} R))).symm
              (F.obj y))) :
      (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R))
          (x := x) (y := y) g))).map f.continuous).cast hx.symm hy.symm).Homotopic
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (C := QuillenQ (canonicalCategory.{uR, uM} R))
            (x := F.obj x) (y := F.obj y) (F.map g)))) := by
    have hSourceFunctor := congrArg
      (fun Z : QuillenQ (canonicalCategory.{uR, uM} R) =>
        SSet.realizedVertex (X := NQ (canonicalCategory.{uR, uM} R))
          ((nerveEquiv (C := QuillenQ (canonicalCategory.{uR, uM} R))).symm Z))
      (Functor.congr_obj hFunctor x)
    have hTargetFunctor := congrArg
      (fun Z : QuillenQ (canonicalCategory.{uR, uM} R) =>
        SSet.realizedVertex (X := NQ (canonicalCategory.{uR, uM} R))
          ((nerveEquiv (C := QuillenQ (canonicalCategory.{uR, uM} R))).symm Z))
      (Functor.congr_obj hFunctor y)
    obtain ⟨H⟩ := CategoryTheory.realizedNerveEquivalence_inv_edge_homotopic E g
    let H' := H.pathCast hSourceFunctor.symm hTargetFunctor.symm
    refine ⟨Path.Homotopy.cast H' ?_ (hFunctorEdgeCast E.inverse F hFunctor g)⟩
    apply Path.ext
    funext t
    change (CategoryTheory.realizedNerveEquivalence E).invFun
        ((TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (C := QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R))
            (x := x) (y := y) g))) t) =
      f ((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R))
          (x := x) (y := y) g))) t)
    exact congrArg
      (fun k : C(NQReal (liftedCategory.{uR, uM, uObj, uHom} R),
          NQReal (canonicalCategory.{uR, uM} R)) =>
        k ((TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (C := QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R))
            (x := x) (y := y) g))) t)) hReal.symm

  have hm : mp.Homotopic (p.trans u) := by
    have hMapTyped : (mp.cast h0.symm hXBase.symm).Homotopic
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (F.map (ExtensionCategory.zeroMonoHom X))))) :=
      hMappedEdge (ExtensionCategory.zeroMonoHom X) h0 hXBase
    have hMapTarget := hMapTyped.pathCast rfl hVertexObject.symm
    have hRemove := SSet.realizedCompEqToHom
      (F.map (ExtensionCategory.zeroMonoHom X)) hObject
    rw [qDownFunctor_zeroMono] at hRemove
    obtain ⟨hc⟩ := (nerve.nonempty_compStruct_iff
      (qDownZeroIso.{uR, uM, uObj, uHom} R).hom
      (ExtensionCategory.zeroMonoHom A)
      ((qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroMonoHom A)).mpr rfl
    have hImage := hMapTarget.trans
      (hRemove.symm.trans (SSet.realizedCompStructHomotopic hc))
    obtain ⟨H⟩ := hImage
    let H' := H.pathCast h0 hX
    have hLeft :
        (((mp.cast h0.symm hXBase.symm).cast rfl hVertexObject.symm).cast h0 hX) = mp := by
      apply Path.ext
      funext t
      rfl
    have hRight :
        (((TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (qDownZeroIso.{uR, uM, uObj, uHom} R).hom))).trans md).cast h0 hX) =
          p.trans u := by
      exact Path.cast_trans _ _ h0 rfl hX
    exact ⟨Path.Homotopy.cast H' hLeft hRight⟩
  have he : ep.Homotopic (p.trans v) := by
    have hMapTyped : (ep.cast h0.symm hXBase.symm).Homotopic
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (F.map (ExtensionCategory.zeroEpiHom X))))) :=
      hMappedEdge (ExtensionCategory.zeroEpiHom X) h0 hXBase
    have hMapTarget := hMapTyped.pathCast rfl hVertexObject.symm
    have hRemove := SSet.realizedCompEqToHom
      (F.map (ExtensionCategory.zeroEpiHom X)) hObject
    rw [qDownFunctor_zeroEpi] at hRemove
    obtain ⟨hc⟩ := (nerve.nonempty_compStruct_iff
      (qDownZeroIso.{uR, uM, uObj, uHom} R).hom
      (ExtensionCategory.zeroEpiHom A)
      ((qDownZeroIso.{uR, uM, uObj, uHom} R).hom ≫
        ExtensionCategory.zeroEpiHom A)).mpr rfl
    have hImage := hMapTarget.trans
      (hRemove.symm.trans (SSet.realizedCompStructHomotopic hc))
    obtain ⟨H⟩ := hImage
    let H' := H.pathCast h0 hX
    have hLeft :
        (((ep.cast h0.symm hXBase.symm).cast rfl hVertexObject.symm).cast h0 hX) = ep := by
      apply Path.ext
      funext t
      rfl
    have hRight :
        (((TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (qDownZeroIso.{uR, uM, uObj, uHom} R).hom))).trans ed).cast h0 hX) =
          p.trans v := by
      exact Path.cast_trans _ _ h0 rfl hX
    exact ⟨Path.Homotopy.cast H' hLeft hRight⟩
  have hLoop :
      (qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap (generatorLoop X) =
        p.symm.trans ((mp.trans ep.symm).trans p) := by
    change p.symm.trans (((m.trans e.symm).map f.continuous).trans p) = _
    rw [Path.map_trans, Path.map_symm]
  have hTarget : u.trans v.symm = generatorLoop A := by
    apply Path.ext
    funext t
    rfl
  obtain ⟨H⟩ := generatorFromMappedEdges p mp ep u v hm he
  exact ⟨Path.Homotopy.cast H hLoop.symm hTarget⟩


end AlgebraicKTheory.QuillenUniverseLift

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.uliftCategory

namespace AlgebraicKTheory.QuillenUniverseLift

private theorem qRealizationUpValueComputed.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    qRealizationUp.{uR, uM, uObj, uHom} R =
      (CategoryTheory.realizedNerveEquivalence
        (qCategoryEquivalence.{uR, uM, uObj, uHom} R)).toFun := by
  rfl

/-- The SAME whole original Q inclusion is the original realized equivalence forward field. -/
public theorem qRealizationUp_value.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    qRealizationUp.{uR, uM, uObj, uHom} R =
      (CategoryTheory.realizedNerveEquivalence
        (qCategoryEquivalence.{uR, uM, uObj, uHom} R)).toFun :=
  qRealizationUpValueComputed R

private theorem qRealizationDownValueComputed.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    qRealizationDown.{uR, uM, uObj, uHom} R =
      (CategoryTheory.realizedNerveEquivalence
        (qCategoryEquivalence.{uR, uM, uObj, uHom} R)).invFun := by
  rfl

/-- The SAME whole original Q descent is the actual original inverse field, without E.symm. -/
public theorem qRealizationDown_value.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    qRealizationDown.{uR, uM, uObj, uHom} R =
      (CategoryTheory.realizedNerveEquivalence
        (qCategoryEquivalence.{uR, uM, uObj, uHom} R)).invFun :=
  qRealizationDownValueComputed R

private theorem qCategoryEquivalenceForwardValueComputed.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    (qCategoryEquivalence.{uR, uM, uObj, uHom} R).functor =
      QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R) := by
  exact qUpFunctor_eq_map.{uR, uM, uObj, uHom} R

/-- The original Q equivalence forward functor has its SAME coefficient-lift value. -/
public theorem qCategoryEquivalence_forward_value.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    (qCategoryEquivalence.{uR, uM, uObj, uHom} R).functor =
      QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R) :=
  qCategoryEquivalenceForwardValueComputed R

private theorem qCategoryEquivalenceInverseValueComputed.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    (qCategoryEquivalence.{uR, uM, uObj, uHom} R).inverse =
      QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R) := by
  exact qDownFunctor_eq_map.{uR, uM, uObj, uHom} R

/-- The original Q equivalence inverse functor has its SAME coefficient-descent value. -/
public theorem qCategoryEquivalence_inverse_value.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    (qCategoryEquivalence.{uR, uM, uObj, uHom} R).inverse =
      QuillenQ.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R) :=
  qCategoryEquivalenceInverseValueComputed R

private theorem qUpWeaklyPointedValueComputed.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    qUpWeaklyPointed.{uR, uM, uObj, uHom} R =
      (⟨qRealizationUp.{uR, uM, uObj, uHom} R, qUpZeroPath.{uR, uM, uObj, uHom} R⟩ :
        ContinuousMap.WeaklyPointed
          (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))
          (OriginalQZeroComparison.zeroQVertex (C := liftedCategory.{uR, uM, uObj, uHom} R))) := by
  rfl

/-- The original weak Q inclusion retains its entire actual map and chosen zero-root record. -/
public theorem qUpWeaklyPointed_value.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    qUpWeaklyPointed.{uR, uM, uObj, uHom} R =
      (⟨qRealizationUp.{uR, uM, uObj, uHom} R, qUpZeroPath.{uR, uM, uObj, uHom} R⟩ :
        ContinuousMap.WeaklyPointed
          (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))
          (OriginalQZeroComparison.zeroQVertex (C := liftedCategory.{uR, uM, uObj, uHom} R))) :=
  qUpWeaklyPointedValueComputed R

private theorem qDownWeaklyPointedValueComputed.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    qDownWeaklyPointed.{uR, uM, uObj, uHom} R =
      (⟨qRealizationDown.{uR, uM, uObj, uHom} R, qDownZeroPath.{uR, uM, uObj, uHom} R⟩ :
        ContinuousMap.WeaklyPointed
          (OriginalQZeroComparison.zeroQVertex (C := liftedCategory.{uR, uM, uObj, uHom} R))
          (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))) := by
  rfl

/-- The original weak Q descent retains its entire actual map and chosen zero-root record. -/
public theorem qDownWeaklyPointed_value.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] :
    qDownWeaklyPointed.{uR, uM, uObj, uHom} R =
      (⟨qRealizationDown.{uR, uM, uObj, uHom} R, qDownZeroPath.{uR, uM, uObj, uHom} R⟩ :
        ContinuousMap.WeaklyPointed
          (OriginalQZeroComparison.zeroQVertex (C := liftedCategory.{uR, uM, uObj, uHom} R))
          (OriginalQZeroComparison.zeroQVertex (C := canonicalCategory.{uR, uM} R))) :=
  qDownWeaklyPointedValueComputed R

private theorem qUpZeroPathValueComputed.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] (t : unitInterval) :
    qUpZeroPath.{uR, uM, uObj, uHom} R t =
      TopCat.pathEquiv (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (qUpZeroIso.{uR, uM, uObj, uHom} R).hom)) t := by
  rfl

/-- Every original Up root time has its SAME chosen-zero edge value with actual casts retained. -/
public theorem qUpZeroPath_value.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] (t : unitInterval) :
    qUpZeroPath.{uR, uM, uObj, uHom} R t =
      TopCat.pathEquiv (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (qUpZeroIso.{uR, uM, uObj, uHom} R).hom)) t :=
  qUpZeroPathValueComputed R t

private theorem qDownZeroPathValueComputed.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] (t : unitInterval) :
    qDownZeroPath.{uR, uM, uObj, uHom} R t =
      TopCat.pathEquiv (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (qDownZeroIso.{uR, uM, uObj, uHom} R).hom)) t := by
  rfl

/-- Every original Down root time has its SAME chosen-zero edge value with actual casts retained. -/
public theorem qDownZeroPath_value.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] (t : unitInterval) :
    qDownZeroPath.{uR, uM, uObj, uHom} R t =
      TopCat.pathEquiv (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (qDownZeroIso.{uR, uM, uObj, uHom} R).hom)) t :=
  qDownZeroPathValueComputed R t

end AlgebraicKTheory.QuillenUniverseLift

end
