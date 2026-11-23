/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveZeroScalarMap
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ProjectiveZeroPlusNormalization
public import MathlibExt.KTheory.Ring.StableGeneralLinear.BGLScalarStableRowSourceComparison
public import MathlibExt.Topology.Category.TopCat.CofibrantPointTraceRetuning

/-!
# Foundations of the original six-role normalized source comparison

The original normalization records and all ten complete family values are
retained. The source and target module functors are compared by the actual
universe counits. Private rooted-family pasting records whole homotopies and
endpoint-fixed root compatibility. Canonical Pair zero comparison uses only
coordinate Iso uniqueness into the actual target zero object.

The eight-piece normalized source family and relative null-trace retuning
are constructed here. The exported comparison retains the complete family,
its original BGL root and the every-time root-value readout.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial unitInterval

attribute [local instance] CategoryTheory.uliftCategory

universe uX uY uZ uC vC uD vD uR uS uMR uMS uNR uNS

open scoped ZeroObject

namespace AlgebraicKTheory.StableGL

private theorem normalizedRootPathHomotopicOfEq
    {X : Type uX} [TopologicalSpace X] {a b : X} {p q : Path a b}
    (h : p = q) : p.Homotopic q := by
  cases h
  exact Path.Homotopic.refl p

private theorem normalizedRootEvalAtTrans
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {f g h : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (K : ContinuousMap.Homotopy g h) (x : X) :
    (H.trans K).evalAt x = (H.evalAt x).trans (K.evalAt x) := by
  apply Path.ext
  funext t
  rfl

private theorem normalizedRootEvalAtSymm
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X) :
    H.symm.evalAt x = (H.evalAt x).symm := by
  apply Path.ext
  funext t
  rfl

private structure NormalizedRootedFamily
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    (x : X) (y : Y) (f g : C(X, Y)) (p : Path (f x) y) (q : Path (g x) y) where
  /-- The entire actual family between the two specified original maps. -/
  homotopy : ContinuousMap.Homotopy f g
  /-- The actual endpoint-fixed root compatibility of that entire family. -/
  root : p.Homotopic ((homotopy.evalAt x).trans q)

private def normalizedRootedTrans
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {x : X} {y : Y} {f g h : C(X, Y)}
    {p : Path (f x) y} {q : Path (g x) y} {r : Path (h x) y}
    (H : NormalizedRootedFamily x y f g p q)
    (K : NormalizedRootedFamily x y g h q r) :
    NormalizedRootedFamily x y f h p r where
  homotopy := H.homotopy.trans K.homotopy
  root := by
    have hRoot := H.root.trans
      ((Path.Homotopic.refl (H.homotopy.evalAt x)).hcomp K.root)
    have hAssoc := (Path.Homotopic.trans_assoc
      (H.homotopy.evalAt x) (K.homotopy.evalAt x) r).symm
    exact (hRoot.trans hAssoc).trans (normalizedRootPathHomotopicOfEq
      (congrArg (fun t : Path (f x) (h x) => t.trans r)
        (normalizedRootEvalAtTrans H.homotopy K.homotopy x).symm))

private def normalizedRootedSymm
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {x : X} {y : Y} {f g : C(X, Y)} {p : Path (f x) y} {q : Path (g x) y}
    (H : NormalizedRootedFamily x y f g p q) :
    NormalizedRootedFamily x y g f q p where
  homotopy := H.homotopy.symm
  root := by
    let a := H.homotopy.evalAt x
    have h := ((Path.Homotopic.refl a.symm).hcomp H.root).trans
      ((Path.Homotopic.trans_assoc a.symm a q).symm.trans
        ((Path.Homotopic.symm_trans a).hcomp (Path.Homotopic.refl q)))
    have h' := h.trans (Path.Homotopic.refl_trans q)
    exact h'.symm.trans (normalizedRootPathHomotopicOfEq
      (congrArg (fun t : Path (g x) (f x) => t.trans p)
        (normalizedRootEvalAtSymm H.homotopy x).symm))

private def normalizedRootedChangePaths
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {x : X} {y : Y} {f g : C(X, Y)}
    {p p' : Path (f x) y} {q q' : Path (g x) y}
    (H : NormalizedRootedFamily x y f g p q)
    (hp : p'.Homotopic p) (hq : q.Homotopic q') :
    NormalizedRootedFamily x y f g p' q' where
  homotopy := H.homotopy
  root := (hp.trans H.root).trans
    ((Path.Homotopic.refl (H.homotopy.evalAt x)).hcomp hq)

private def normalizedRootedPostWeak
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {Z : Type uZ} [TopologicalSpace Z] {x : X} {y : Y} {z : Z}
    {f g : C(X, Y)} {p : Path (f x) y} {q : Path (g x) y}
    (H : NormalizedRootedFamily x y f g p q) (k : C(Y, Z)) (r : Path (k y) z) :
    NormalizedRootedFamily x z (k.comp f) (k.comp g)
      ((p.map k.continuous).trans r) ((q.map k.continuous).trans r) where
  homotopy := (ContinuousMap.Homotopy.refl k).comp H.homotopy
  root := by
    have h := (H.root.map k).hcomp (Path.Homotopic.refl r)
    rw [Path.map_trans] at h
    have hAssoc := Path.Homotopic.trans_assoc
      ((H.homotopy.evalAt x).map k.continuous) (q.map k.continuous) r
    have hValue : (((ContinuousMap.Homotopy.refl k).comp H.homotopy).evalAt x) =
        (H.homotopy.evalAt x).map k.continuous := by
      apply Path.ext
      funext t
      rfl
    exact (h.trans hAssoc).trans (normalizedRootPathHomotopicOfEq
      (congrArg (fun t : Path ((k.comp f) x) ((k.comp g) x) =>
        t.trans ((q.map k.continuous).trans r)) hValue.symm))

private def normalizedRootedFromTrace
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {x : X} {y : Y} {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (hg : g x = y) (p : Path (f x) y)
    (hTrace : ∀ t : unitInterval, H (t, x) = p t) :
    NormalizedRootedFamily x y f g p ((Path.refl y).cast hg rfl) where
  homotopy := H
  root := by
    have hPath : (H.evalAt x).cast rfl hg.symm = p := by
      apply Path.ext
      funext t
      exact hTrace t
    have hAppend : (H.evalAt x).trans ((Path.refl y).cast hg rfl) =
        ((H.evalAt x).cast rfl hg.symm).trans (Path.refl y) := by
      apply Path.ext
      funext t
      rfl
    rw [hPath] at hAppend
    exact (Path.Homotopic.trans_refl p).symm.trans
      (normalizedRootPathHomotopicOfEq hAppend.symm)

private theorem normalizedPairNatIsoZeroCoherence
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (alpha : F ≅ G) :
    (SInverseS.pairFunctorNatIso F G alpha).app (⟨0, 0⟩ : SInverseS.Pair C) ≪≫
      SInverseS.zeroPairIso G = SInverseS.zeroPairIso F := by
  let J := SInverseS.corePairInclusion (C := D)
  let a := (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨G.obj (0 : C)⟩)
    (alpha.app (0 : C))).prod
    (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨G.obj (0 : C)⟩) (alpha.app (0 : C)))
  let b := (Core.isoMk (x := ⟨G.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) G.mapZeroObject).prod
    (Core.isoMk (x := ⟨G.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) G.mapZeroObject)
  let c := (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject).prod
    (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject)
  have hNat : (SInverseS.pairFunctorNatIso F G alpha).app
      (⟨0, 0⟩ : SInverseS.Pair C) = J.mapIso a :=
    (SInverseS.pairFunctor_characteristic F G alpha (𝟭 D)).2.2.2.2.2.2.2.2.1 ⟨0, 0⟩
  have hZeroG : SInverseS.zeroPairIso G = J.mapIso b :=
    (SInverseS.coreTranslation_characteristic G).2.2.2.2.2.2.2.2.1
  have hZeroF : SInverseS.zeroPairIso F = J.mapIso c :=
    (SInverseS.coreTranslation_characteristic F).2.2.2.2.2.2.2.2.1
  have hCoordinate : alpha.app (0 : C) ≪≫ G.mapZeroObject = F.mapZeroObject :=
    Subsingleton.elim _ _
  have hCore : a.hom ≫ b.hom = c.hom := by
    apply Prod.ext <;> apply Core.hom_ext <;> exact congrArg Iso.hom hCoordinate
  rw [hNat, hZeroG, hZeroF]
  apply Iso.ext
  exact (J.map_comp a.hom b.hom).symm.trans (congrArg J.map hCore)

/-- The literal original R/S normalization records retain every original
model, independent plus target, point law and complete family value. -/
public def nativeProjectiveZeroScalarOriginalNormalizationRecords
    (R : Type uR) (S : Type uS) [Ring R] [Ring S] :
    NativeProjectiveZeroPlusNormalization.{uR, uMR, uNR} R ×
      NativeProjectiveZeroPlusNormalization.{uS, uMS, uNS} S :=
  (nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R,
    nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S)

private theorem normalizedOriginalRecordPairValueComputed
    (R : Type uR) (S : Type uS) [Ring R] [Ring S] :
    nativeProjectiveZeroScalarOriginalNormalizationRecords.{uR, uS, uMR, uMS, uNR, uNS} R S =
      (nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R,
        nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S) := by
  rfl

/-- The whole pair has its exact jointly selected original values. -/
public theorem nativeProjectiveZeroScalarOriginalNormalizationRecords_value
    (R : Type uR) (S : Type uS) [Ring R] [Ring S] :
    nativeProjectiveZeroScalarOriginalNormalizationRecords.{uR, uS, uMR, uMS, uNR, uNS} R S =
      (nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R,
        nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S) :=
  normalizedOriginalRecordPairValueComputed R S

private abbrev normalizedModuleModel.{uModelRing, uModelCarrier}
    (R : Type uModelRing) [Ring R] :=
  (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
    (FGProjectiveCat.universeEquivalence.{uModelRing, uModelCarrier} R).inverse

private abbrev normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier}
    (S : Type uTargetRing) [Ring S] :=
  (FGProjectiveCat.universeEquivalence.{uTargetRing, uSourceCarrier} S).functor ⋙
    (FGProjectiveCat.universeEquivalence.{uTargetRing, uTargetCarrier} S).inverse

private def normalizedModuleSourceIsoComputed
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedModuleModel.{uR, uMR} R ⋙
        nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ≅
      ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f) ⋙
        normalizedModuleResize.{uR, uS, uMS} S := by
  let P := (FGProjectiveCat.IdempotentModel.equivalence R).functor
  let E := FGProjectiveCat.universeEquivalence.{uR, uMR} R
  let T := FGProjectiveCat.scalarExtension.{uR, uS, uR} f ⋙
    normalizedModuleResize.{uR, uS, uMS} S
  exact Functor.associator P E.inverse (E.functor ⋙ T) ≪≫
    Functor.isoWhiskerLeft P (Functor.associator E.inverse E.functor T).symm ≪≫
      Functor.isoWhiskerLeft P (Functor.isoWhiskerRight E.counitIso T) ≪≫
        Functor.isoWhiskerLeft P (Functor.leftUnitor T) ≪≫
          (Functor.associator P (FGProjectiveCat.scalarExtension.{uR, uS, uR} f)
            (normalizedModuleResize.{uR, uS, uMS} S)).symm

/-- The actual R universe counit compares the SAME original module source
recipe with its original scalar/target-resize recipe. -/
public def nativeProjectiveZeroScalarOriginalModuleSourceIso
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uR, uMR} R).inverse) ⋙
        nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ≅
      ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f) ⋙
        ((FGProjectiveCat.universeEquivalence.{uS, uR} S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uMS} S).inverse) :=
  normalizedModuleSourceIsoComputed f

private def normalizedModuleTargetIsoComputed.{uSourceCarrier, uTargetRing, uTargetCarrier}
    (S : Type uTargetRing) [Ring S] :
    ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uTargetRing, uSourceCarrier} S).inverse) ⋙
      normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S ≅
      normalizedModuleModel.{uTargetRing, uTargetCarrier} S := by
  let P := (FGProjectiveCat.IdempotentModel.equivalence S).functor
  let E := FGProjectiveCat.universeEquivalence.{uTargetRing, uSourceCarrier} S
  let L := (FGProjectiveCat.universeEquivalence.{uTargetRing, uTargetCarrier} S).inverse
  exact Functor.associator P E.inverse (E.functor ⋙ L) ≪≫
    Functor.isoWhiskerLeft P (Functor.associator E.inverse E.functor L).symm ≪≫
      Functor.isoWhiskerLeft P (Functor.isoWhiskerRight E.counitIso L) ≪≫
        Functor.isoWhiskerLeft P (Functor.leftUnitor L)

/-- The actual S universe counit compares the SAME original target-resize
recipe with the independently sized original S model. -/
public def nativeProjectiveZeroScalarOriginalModuleTargetIso.{
    uSourceCarrier, uTargetRing, uTargetCarrier}
    (S : Type uTargetRing) [Ring S] :
    ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uTargetRing, uSourceCarrier} S).inverse) ⋙
        ((FGProjectiveCat.universeEquivalence.{uTargetRing, uSourceCarrier} S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uTargetRing, uTargetCarrier} S).inverse) ≅
      (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{uTargetRing, uTargetCarrier} S).inverse :=
  normalizedModuleTargetIsoComputed.{uSourceCarrier, uTargetRing, uTargetCarrier} S

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uE vE uA vA uB vB

open scoped ZeroObject

universe uC vC uD vD

namespace AlgebraicKTheory.StableGL

private theorem normalizedEqWhiskerLeftApp
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {E : Type uE} [Category.{vE} E] (J : A ⥤ B) {F G : B ⥤ E}
    (h : F = G) (X : A) :
    (Functor.isoWhiskerLeft J (eqToIso h)).app X =
      eqToIso (congrArg (fun q : B ⥤ E => q.obj (J.obj X)) h) := by
  cases h
  rfl

section ZeroLiftData

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

private structure NormalizedZeroLiftData (F : C ⥤ D) [F.Additive]
    (G : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D)) where
  /-- The actual whole Pair inclusion comparison of the specified zero functor. -/
  inclusion : G ⋙ (SInverseS.zeroComponentProperty (C := D)).ι ≅
    (SInverseS.zeroComponentProperty (C := C)).ι ⋙ SInverseS.pairFunctor F
  /-- The actual specified canonical zero-root Iso of that SAME functor. -/
  root : G.obj (SInverseS.zeroComponentBaseObject (C := C)) ≅
    SInverseS.zeroComponentBaseObject (C := D)
  /-- Its whole inclusion follows the SAME canonical Pair zero comparison. -/
  root_inclusion : (SInverseS.zeroComponentProperty (C := D)).ι.mapIso root =
    inclusion.app (SInverseS.zeroComponentBaseObject (C := C)) ≪≫ SInverseS.zeroPairIso F

private def normalizedCanonicalZeroLift (F : C ⥤ D) [F.Additive] :
    NormalizedZeroLiftData F (SInverseS.zeroComponentFunctor F) where
  inclusion := SInverseS.zeroComponentFunctorInclusionIso F
  root := (SInverseS.zeroComponentProperty (C := D)).isoMk
    (eqToIso (SInverseS.zeroComponentFunctor_obj_obj F
      (SInverseS.zeroComponentBaseObject (C := C))) ≪≫ SInverseS.zeroPairIso F)
  root_inclusion := by
    rw [SInverseS.zeroComponentFunctorInclusionIso_app_value]
    apply Iso.ext
    rfl

private def normalizedModelZeroLift (E : C ≌ D) [E.functor.Additive] :
    NormalizedZeroLiftData E.functor (SInverseS.zeroComponentEquivalence E).functor where
  inclusion := SInverseS.zeroComponentEquivalenceInclusionIso E ≪≫
    Functor.isoWhiskerLeft (SInverseS.zeroComponentProperty (C := C)).ι
      (eqToIso (SInverseS.pairEquivalence_characteristic E).1)
  root := SInverseS.zeroComponentEquivalencePointIso E
  root_inclusion := by
    let z := SInverseS.zeroComponentBaseObject (C := C)
    let hPair := (SInverseS.pairEquivalence_characteristic E).1
    have hWhisker := normalizedEqWhiskerLeftApp
      (SInverseS.zeroComponentProperty (C := C)).ι hPair z
    have hApp :
        ((SInverseS.zeroComponentEquivalenceInclusionIso E) ≪≫
          Functor.isoWhiskerLeft (SInverseS.zeroComponentProperty (C := C)).ι
            (eqToIso hPair)).app z =
        eqToIso (SInverseS.zeroComponentEquivalence_functor_obj_obj E z) ≪≫
          eqToIso (congrArg (fun q : SInverseS.Pair C ⥤ SInverseS.Pair D => q.obj z.obj)
            hPair) := by
      change (SInverseS.zeroComponentEquivalenceInclusionIso E).app z ≪≫
        (Functor.isoWhiskerLeft (SInverseS.zeroComponentProperty (C := C)).ι
          (eqToIso hPair)).app z = _
      rw [SInverseS.zeroComponentEquivalenceInclusionIso_app_value, hWhisker]
    rw [hApp]
    exact (SInverseS.zeroComponentEquivalencePointIso_inclusion_value E).trans
      (Iso.trans_assoc _ _ _).symm

private def normalizedZeroLiftNatIso
    (F H : C ⥤ D) [F.Additive] [H.Additive]
    (G K : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (A : NormalizedZeroLiftData F G) (B : NormalizedZeroLiftData H K)
    (alpha : F ≅ H) : G ≅ K :=
  SInverseS.liftZeroComponentNatIso G K
    (A.inclusion ≪≫
      Functor.isoWhiskerLeft (SInverseS.zeroComponentProperty (C := C)).ι
        (SInverseS.pairFunctorNatIso F H alpha) ≪≫ B.inclusion.symm)

private theorem normalizedZeroLiftNatIsoInclusionApp
    (F H : C ⥤ D) [F.Additive] [H.Additive]
    (G K : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (A : NormalizedZeroLiftData F G) (B : NormalizedZeroLiftData H K)
    (alpha : F ≅ H) (X : SInverseS.ZeroComponent (C := C)) :
    (SInverseS.zeroComponentProperty (C := D)).ι.mapIso
        ((normalizedZeroLiftNatIso F H G K A B alpha).app X) =
      A.inclusion.app X ≪≫ (SInverseS.pairFunctorNatIso F H alpha).app X.obj ≪≫
        (B.inclusion.app X).symm := by
  let e := A.inclusion ≪≫
    Functor.isoWhiskerLeft (SInverseS.zeroComponentProperty (C := C)).ι
      (SInverseS.pairFunctorNatIso F H alpha) ≪≫ B.inclusion.symm
  have h := SInverseS.liftZeroComponentNatIso_inclusion_app G K e X
  have hApp : e.app X =
      A.inclusion.app X ≪≫ (SInverseS.pairFunctorNatIso F H alpha).app X.obj ≪≫
        (B.inclusion.app X).symm := by
    rfl
  exact h.trans hApp

private theorem normalizedZeroLiftNatIsoRoot
    (F H : C ⥤ D) [F.Additive] [H.Additive]
    (G K : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (A : NormalizedZeroLiftData F G) (B : NormalizedZeroLiftData H K)
    (alpha : F ≅ H) :
    (normalizedZeroLiftNatIso F H G K A B alpha).app
        (SInverseS.zeroComponentBaseObject (C := C)) ≪≫ B.root = A.root := by
  let z := SInverseS.zeroComponentBaseObject (C := C)
  let J := (SInverseS.zeroComponentProperty (C := D)).ι
  let a := (normalizedZeroLiftNatIso F H G K A B alpha).app z
  let i := A.inclusion.app z
  let n := (SInverseS.pairFunctorNatIso F H alpha).app z.obj
  let j := B.inclusion.app z
  let r := SInverseS.zeroPairIso H
  have hObj : z.obj = (⟨0, 0⟩ : SInverseS.Pair C) :=
    (SInverseS.ComponentTranslation.componentDecompositionIsoCat_obj 0 z).symm.trans
      (SInverseS.ComponentTranslation.componentDecompositionIsoCat_zero (C := C))
  have hScalar : n ≪≫ r = SInverseS.zeroPairIso F := by
    let N := SInverseS.pairFunctorNatIso F H alpha
    have hApp : HEq ((N.app z.obj).hom)
        ((N.app (⟨0, 0⟩ : SInverseS.Pair C)).hom) :=
      congr_arg_heq (fun X : SInverseS.Pair C => (N.app X).hom) hObj
    have hComp : HEq ((N.app z.obj).hom ≫ r.hom)
        ((N.app (⟨0, 0⟩ : SInverseS.Pair C)).hom ≫ r.hom) :=
      CategoryTheory.heq_comp (C := SInverseS.Pair D)
        (congrArg (SInverseS.pairFunctor F).obj hObj)
        (congrArg (SInverseS.pairFunctor H).obj hObj) rfl hApp (HEq.rfl)
    have hZero := congrArg Iso.hom (normalizedPairNatIsoZeroCoherence F H alpha)
    apply Iso.ext
    exact eq_of_heq (hComp.trans (heq_of_eq hZero))
  have hCancel : (i ≪≫ n ≪≫ j.symm) ≪≫ (j ≪≫ r) = i ≪≫ n ≪≫ r :=
    (Iso.trans_assoc i (n ≪≫ j.symm) (j ≪≫ r)).trans
      (congrArg (Iso.trans i)
        ((Iso.trans_assoc n j.symm (j ≪≫ r)).trans
          (congrArg (Iso.trans n)
            ((Iso.trans_assoc j.symm j r).symm.trans
              ((congrArg (fun e => e ≪≫ r) (Iso.symm_self_id j)).trans
                (Iso.refl_trans r))))))
  have hMap : J.mapIso (a ≪≫ B.root) = J.mapIso a ≪≫ J.mapIso B.root := by
    apply Iso.ext
    exact J.map_comp a.hom B.root.hom
  have hApp := normalizedZeroLiftNatIsoInclusionApp F H G K A B alpha z
  have hValues : J.mapIso a ≪≫ J.mapIso B.root =
      (i ≪≫ n ≪≫ j.symm) ≪≫ (j ≪≫ r) :=
    congrArg₂ Iso.trans hApp B.root_inclusion
  have hEq : J.mapIso (a ≪≫ B.root) = J.mapIso A.root :=
    hMap.trans (hValues.trans (hCancel.trans
      ((congrArg (Iso.trans i) hScalar).trans A.root_inclusion.symm)))
  apply Iso.ext
  apply J.map_injective
  exact congrArg Iso.hom hEq

end ZeroLiftData

private theorem normalizedMixedFunctorComposition
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {E : Type uE} [Category.{vE} E] (F : A ⥤ B) (G : B ⥤ E) :
    CategoryTheory.realizedNerveFunctorMap (F ⋙ G) =
      (CategoryTheory.realizedNerveFunctorMap G).comp
        (CategoryTheory.realizedNerveFunctorMap F) := by
  rw [CategoryTheory.realizedNerveFunctorMap_larger_recipe.{uA, vA, uE, vE, max uB vB}
      (F ⋙ G),
    CategoryTheory.realizedNerveFunctorMap_larger_recipe.{uB, vB, uE, vE, max uA vA} G,
    CategoryTheory.realizedNerveFunctorMap_larger_recipe.{uA, vA, uB, vB, max uE vE} F]
  apply ContinuousMap.ext
  intro x
  let HA := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uB vB uE vE} A
  let HB := SSet.realizedNerveLiftHomeomorph.{uB, vB, max uA vA uB vB uE vE} B
  let HE := SSet.realizedNerveLiftHomeomorph.{uE, vE, max uA vA uB vB uE vE} E
  let LF :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
      max uA vA uB vB uE vE, vA, uA} A).inverse ⋙ F ⋙
      (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
        max uA vA uB vB uE vE, vB, uB} B).functor
  let LG :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
      max uA vA uB vB uE vE, vB, uB} B).inverse ⋙ G ⋙
      (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
        max uA vA uB vB uE vE, vE, uE} E).functor
  let LFG :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
      max uA vA uB vB uE vE, vA, uA} A).inverse ⋙ (F ⋙ G) ⋙
      (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
        max uA vA uB vB uE vE, vE, uE} E).functor
  let z := HA.symm x
  have hFunctor : LFG = LF ⋙ LG := by
    exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
      change LFG.map f = eqToHom (rfl : LFG.obj i = LFG.obj i) ≫ LFG.map f ≫
        eqToHom (rfl : LFG.obj j = LFG.obj j)
      exact CategoryTheory.eq_conj_eqToHom (LFG.map f))
  have hNerve : nerveMap LFG = nerveMap LF ≫ nerveMap LG :=
    (congrArg nerveMap hFunctor).trans (nerveMap_comp LF LG).symm
  have hTop : SSet.toTop.map (nerveMap LFG) =
      SSet.toTop.map (nerveMap LF) ≫ SSet.toTop.map (nerveMap LG) :=
    (SSet.toTop.congr_map hNerve).trans (SSet.toTop.map_comp _ _)
  have hStep : HE (SSet.toTop.map (nerveMap LFG) z) =
      HE (SSet.toTop.map (nerveMap LG) (SSet.toTop.map (nerveMap LF) z)) :=
    congrArg HE ((ConcreteCategory.congr_hom hTop z).trans (TopCat.comp_app _ _ z))
  change HE (SSet.toTop.map (nerveMap LFG) z) =
    HE (SSet.toTop.map (nerveMap LG)
      (HB.symm (HB (SSet.toTop.map (nerveMap LF) z))))
  exact hStep.trans
    ((congrArg (fun y => HE (SSet.toTop.map (nerveMap LG) y))
      (HB.symm_apply_apply (SSet.toTop.map (nerveMap LF) z))).symm)

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uC vC uD vD uE vE

namespace AlgebraicKTheory.StableGL

private theorem normalizedFunctorMapIsoTrans
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) {X Y Z : C} (a : X ≅ Y) (b : Y ≅ Z) :
    F.mapIso (a ≪≫ b) = F.mapIso a ≪≫ F.mapIso b := by
  apply Iso.ext
  exact F.map_comp a.hom b.hom

section CompositeZeroLifts

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E]

private theorem normalizedPairCompositeZeroCoherence
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive] :
    (SInverseS.pairFunctorComposite F H).app (⟨0, 0⟩ : SInverseS.Pair C) ≪≫
      (SInverseS.pairFunctor H).mapIso (SInverseS.zeroPairIso F) ≪≫
        SInverseS.zeroPairIso H = SInverseS.zeroPairIso (F ⋙ H) := by
  let JD := SInverseS.corePairInclusion (C := D)
  let JE := SInverseS.corePairInclusion (C := E)
  let a := (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject).prod
    (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject)
  let b := (Core.isoMk (x := ⟨H.obj (0 : D)⟩) (y := ⟨(0 : E)⟩) H.mapZeroObject).prod
    (Core.isoMk (x := ⟨H.obj (0 : D)⟩) (y := ⟨(0 : E)⟩) H.mapZeroObject)
  let c := (Core.isoMk (x := ⟨(F ⋙ H).obj (0 : C)⟩) (y := ⟨(0 : E)⟩)
    (F ⋙ H).mapZeroObject).prod
    (Core.isoMk (x := ⟨(F ⋙ H).obj (0 : C)⟩) (y := ⟨(0 : E)⟩)
      (F ⋙ H).mapZeroObject)
  let ma := (H.core.prod H.core).mapIso a
  have hF : SInverseS.zeroPairIso F = JD.mapIso a :=
    (SInverseS.coreTranslation_characteristic F).2.2.2.2.2.2.2.2.1
  have hH : SInverseS.zeroPairIso H = JE.mapIso b :=
    (SInverseS.coreTranslation_characteristic H).2.2.2.2.2.2.2.2.1
  have hFH : SInverseS.zeroPairIso (F ⋙ H) = JE.mapIso c :=
    (SInverseS.coreTranslation_characteristic (F ⋙ H)).2.2.2.2.2.2.2.2.1
  have hComp : (SInverseS.pairFunctorComposite F H).app
      (⟨0, 0⟩ : SInverseS.Pair C) =
      Iso.refl ((SInverseS.pairFunctor (F ⋙ H)).obj ⟨0, 0⟩) :=
    (SInverseS.pairFunctor_characteristic F F (Iso.refl F) H).2.2.2.2.2.2.2.2.2.2.1 ⟨0, 0⟩
  have hMap : (SInverseS.pairFunctor H).mapIso (JD.mapIso a) = JE.mapIso ma := by
    apply Iso.ext
    exact (SInverseS.coreTranslation_characteristic H).1 a.hom
  have hCoordinate : H.mapIso F.mapZeroObject ≪≫ H.mapZeroObject =
      (F ⋙ H).mapZeroObject := Subsingleton.elim _ _
  have hCore : ma.hom ≫ b.hom = c.hom := by
    apply Prod.ext <;> apply Core.hom_ext <;> exact congrArg Iso.hom hCoordinate
  have hMapped : (SInverseS.pairFunctor H).mapIso (SInverseS.zeroPairIso F) =
      JE.mapIso ma :=
    (congrArg (SInverseS.pairFunctor H).mapIso hF).trans hMap
  have hCoreMap : JE.mapIso ma ≪≫ JE.mapIso b = JE.mapIso c := by
    apply Iso.ext
    exact (JE.map_comp ma.hom b.hom).symm.trans (congrArg JE.map hCore)
  have hRoot : (SInverseS.pairFunctor H).mapIso (SInverseS.zeroPairIso F) ≪≫
      SInverseS.zeroPairIso H = SInverseS.zeroPairIso (F ⋙ H) :=
    (congrArg₂ Iso.trans hMapped hH).trans (hCoreMap.trans hFH.symm)
  exact (congrArg₂ Iso.trans hComp hRoot).trans
    (Iso.refl_trans (SInverseS.zeroPairIso (F ⋙ H)))

private theorem normalizedPairCompositeZeroFactor
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive] :
    (SInverseS.pairFunctor H).mapIso (SInverseS.zeroPairIso F) ≪≫
        SInverseS.zeroPairIso H =
      ((SInverseS.pairFunctorComposite F H).app (⟨0, 0⟩ : SInverseS.Pair C)).symm ≪≫
        SInverseS.zeroPairIso (F ⋙ H) := by
  apply Iso.ext
  apply (cancel_epi
    ((SInverseS.pairFunctorComposite F H).app (⟨0, 0⟩ : SInverseS.Pair C)).hom).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg Iso.hom (normalizedPairCompositeZeroCoherence F H)

private def normalizedZeroLiftCompositeInclusion
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive]
    (G : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (K : SInverseS.ZeroComponent (C := D) ⥤ SInverseS.ZeroComponent (C := E))
    (A : NormalizedZeroLiftData F G) (B : NormalizedZeroLiftData H K) :
    (G ⋙ K) ⋙ (SInverseS.zeroComponentProperty (C := E)).ι ≅
      (SInverseS.zeroComponentProperty (C := C)).ι ⋙ SInverseS.pairFunctor (F ⋙ H) :=
  Functor.associator G K (SInverseS.zeroComponentProperty (C := E)).ι ≪≫
    Functor.isoWhiskerLeft G B.inclusion ≪≫
      (Functor.associator G (SInverseS.zeroComponentProperty (C := D)).ι
        (SInverseS.pairFunctor H)).symm ≪≫
        Functor.isoWhiskerRight A.inclusion (SInverseS.pairFunctor H) ≪≫
          Functor.associator (SInverseS.zeroComponentProperty (C := C)).ι
            (SInverseS.pairFunctor F) (SInverseS.pairFunctor H) ≪≫
            Functor.isoWhiskerLeft (SInverseS.zeroComponentProperty (C := C)).ι
              (SInverseS.pairFunctorComposite F H).symm

private theorem normalizedZeroLiftCompositeInclusionApp
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive]
    (G : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (K : SInverseS.ZeroComponent (C := D) ⥤ SInverseS.ZeroComponent (C := E))
    (A : NormalizedZeroLiftData F G) (B : NormalizedZeroLiftData H K)
    (X : SInverseS.ZeroComponent (C := C)) :
    (normalizedZeroLiftCompositeInclusion F H G K A B).app X =
      B.inclusion.app (G.obj X) ≪≫ (SInverseS.pairFunctor H).mapIso (A.inclusion.app X) ≪≫
        ((SInverseS.pairFunctorComposite F H).app X.obj).symm := by
  apply Iso.ext
  change 𝟙 _ ≫ B.inclusion.hom.app (G.obj X) ≫ 𝟙 _ ≫
    (SInverseS.pairFunctor H).map (A.inclusion.hom.app X) ≫ 𝟙 _ ≫
      (SInverseS.pairFunctorComposite F H).inv.app X.obj = _
  simp only [Category.id_comp, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]

private theorem normalizedZeroLiftCompositeRootInclusion
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive]
    (G : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (K : SInverseS.ZeroComponent (C := D) ⥤ SInverseS.ZeroComponent (C := E))
    (A : NormalizedZeroLiftData F G) (B : NormalizedZeroLiftData H K) :
    (SInverseS.zeroComponentProperty (C := E)).ι.mapIso (K.mapIso A.root ≪≫ B.root) =
      (normalizedZeroLiftCompositeInclusion F H G K A B).app
        (SInverseS.zeroComponentBaseObject (C := C)) ≪≫ SInverseS.zeroPairIso (F ⋙ H) := by
  let zC := SInverseS.zeroComponentBaseObject (C := C)
  let zD := SInverseS.zeroComponentBaseObject (C := D)
  let JD := (SInverseS.zeroComponentProperty (C := D)).ι
  let JE := (SInverseS.zeroComponentProperty (C := E)).ι
  let PH := SInverseS.pairFunctor H
  have hNat : JE.mapIso (K.mapIso A.root) ≪≫ B.inclusion.app zD =
      B.inclusion.app (G.obj zC) ≪≫ PH.mapIso (JD.mapIso A.root) := by
    apply Iso.ext
    exact B.inclusion.hom.naturality A.root.hom
  let b := B.inclusion.app (G.obj zC)
  let a := A.inclusion.app zC
  let rF := SInverseS.zeroPairIso F
  let rH := SInverseS.zeroPairIso H
  let rFH := SInverseS.zeroPairIso (F ⋙ H)
  let c := ((SInverseS.pairFunctorComposite F H).app zC.obj).symm
  have hObj : zC.obj = (⟨0, 0⟩ : SInverseS.Pair C) :=
    (SInverseS.ComponentTranslation.componentDecompositionIsoCat_obj 0 zC).symm.trans
      (SInverseS.ComponentTranslation.componentDecompositionIsoCat_zero (C := C))
  have hFactor : PH.mapIso rF ≪≫ rH = c ≪≫ rFH := by
    let M := SInverseS.pairFunctorComposite F H
    have hApp : HEq ((M.app zC.obj).inv)
        ((M.app (⟨0, 0⟩ : SInverseS.Pair C)).inv) :=
      congr_arg_heq (fun X : SInverseS.Pair C => (M.app X).inv) hObj
    have hComp : HEq ((M.app zC.obj).inv ≫ rFH.hom)
        ((M.app (⟨0, 0⟩ : SInverseS.Pair C)).inv ≫ rFH.hom) :=
      CategoryTheory.heq_comp (C := SInverseS.Pair E)
        (congrArg (SInverseS.pairFunctor F ⋙ SInverseS.pairFunctor H).obj hObj)
        (congrArg (SInverseS.pairFunctor (F ⋙ H)).obj hObj) rfl hApp (HEq.rfl)
    have hZero := congrArg Iso.hom (normalizedPairCompositeZeroFactor F H)
    apply Iso.ext
    exact eq_of_heq ((heq_of_eq hZero).trans hComp.symm)
  have h1 : JE.mapIso (K.mapIso A.root ≪≫ B.root) =
      JE.mapIso (K.mapIso A.root) ≪≫ JE.mapIso B.root :=
    normalizedFunctorMapIsoTrans JE _ _
  have h2 : JE.mapIso (K.mapIso A.root) ≪≫ JE.mapIso B.root =
      JE.mapIso (K.mapIso A.root) ≪≫ (B.inclusion.app zD ≪≫ rH) :=
    congrArg (Iso.trans (JE.mapIso (K.mapIso A.root))) B.root_inclusion
  have h3 : JE.mapIso (K.mapIso A.root) ≪≫ (B.inclusion.app zD ≪≫ rH) =
      (JE.mapIso (K.mapIso A.root) ≪≫ B.inclusion.app zD) ≪≫ rH :=
    (Iso.trans_assoc _ _ _).symm
  have h4 : (JE.mapIso (K.mapIso A.root) ≪≫ B.inclusion.app zD) ≪≫ rH =
      (b ≪≫ PH.mapIso (JD.mapIso A.root)) ≪≫ rH :=
    congrArg (fun e => e ≪≫ rH) hNat
  have h5 : (b ≪≫ PH.mapIso (JD.mapIso A.root)) ≪≫ rH =
      (b ≪≫ PH.mapIso (a ≪≫ rF)) ≪≫ rH :=
    congrArg (fun e => (b ≪≫ PH.mapIso e) ≪≫ rH) A.root_inclusion
  have h6 : (b ≪≫ PH.mapIso (a ≪≫ rF)) ≪≫ rH =
      (b ≪≫ (PH.mapIso a ≪≫ PH.mapIso rF)) ≪≫ rH :=
    congrArg (fun e => (b ≪≫ e) ≪≫ rH) (normalizedFunctorMapIsoTrans PH a rF)
  have h7 : (b ≪≫ (PH.mapIso a ≪≫ PH.mapIso rF)) ≪≫ rH =
      (b ≪≫ PH.mapIso a) ≪≫ (PH.mapIso rF ≪≫ rH) :=
    (Iso.trans_assoc b (PH.mapIso a ≪≫ PH.mapIso rF) rH).trans
      ((congrArg (Iso.trans b) (Iso.trans_assoc (PH.mapIso a) (PH.mapIso rF) rH)).trans
        (Iso.trans_assoc b (PH.mapIso a) (PH.mapIso rF ≪≫ rH)).symm)
  have h8 : (b ≪≫ PH.mapIso a) ≪≫ (PH.mapIso rF ≪≫ rH) =
      (b ≪≫ PH.mapIso a) ≪≫ (c ≪≫ rFH) :=
    congrArg (Iso.trans (b ≪≫ PH.mapIso a)) hFactor
  have h9 : (b ≪≫ PH.mapIso a) ≪≫ (c ≪≫ rFH) =
      ((b ≪≫ PH.mapIso a) ≪≫ c) ≪≫ rFH :=
    (Iso.trans_assoc _ _ _).symm
  have h10 : ((b ≪≫ PH.mapIso a) ≪≫ c) ≪≫ rFH =
      (b ≪≫ PH.mapIso a ≪≫ c) ≪≫ rFH :=
    congrArg (fun e => e ≪≫ rFH) (Iso.trans_assoc b (PH.mapIso a) c)
  have h11 : (b ≪≫ PH.mapIso a ≪≫ c) ≪≫ rFH =
      (normalizedZeroLiftCompositeInclusion F H G K A B).app zC ≪≫ rFH :=
    congrArg (fun e => e ≪≫ rFH)
      (normalizedZeroLiftCompositeInclusionApp F H G K A B zC).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans
    (h7.trans (h8.trans (h9.trans (h10.trans h11)))))))))

private def normalizedZeroLiftComposite
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive]
    (G : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (K : SInverseS.ZeroComponent (C := D) ⥤ SInverseS.ZeroComponent (C := E))
    (A : NormalizedZeroLiftData F G) (B : NormalizedZeroLiftData H K) :
    NormalizedZeroLiftData (F ⋙ H) (G ⋙ K) where
  inclusion := normalizedZeroLiftCompositeInclusion F H G K A B
  root := K.mapIso A.root ≪≫ B.root
  root_inclusion := normalizedZeroLiftCompositeRootInclusion F H G K A B

end CompositeZeroLifts

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uE vE uA vA uB vB uR uS uMR uMS

namespace AlgebraicKTheory.StableGL

private theorem normalizedEqWhiskerRightApp
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {E : Type uE} [Category.{vE} E] {F G : A ⥤ B} (h : F = G) (J : B ⥤ E) (X : A) :
    (Functor.isoWhiskerRight (eqToIso h) J).app X =
      J.mapIso (eqToIso (congrArg (fun q : A ⥤ B => q.obj X) h)) := by
  cases h
  rfl

private def normalizedOriginalModelLift.{uModelRing, uModelCarrier}
    (R : Type uModelRing) [Ring R] :
    NormalizedZeroLiftData (normalizedModuleModel.{uModelRing, uModelCarrier} R)
      (finiteFreeRowProjectiveUniverseZeroEquivalence.{uModelRing, uModelCarrier} R).functor := by
  let E := (FGProjectiveCat.IdempotentModel.equivalence R).trans
    (FGProjectiveCat.universeEquivalence.{uModelRing, uModelCarrier} R).symm
  let z := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)
  let J := (SInverseS.zeroComponentProperty
    (C := FGProjectiveCat.{max uModelRing uModelCarrier} R)).ι
  let A := normalizedModelZeroLift E
  let h := congrArg
    (fun e : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ≌
      SInverseS.ZeroComponent (C := FGProjectiveCat.{max uModelRing uModelCarrier} R) =>
        e.functor)
    (finiteFreeRowProjectiveUniverseZeroEquivalence_value.{uModelRing, uModelCarrier} R)
  refine
    { inclusion := Functor.isoWhiskerRight (eqToIso h) J ≪≫ A.inclusion
      root := finiteFreeRowProjectiveUniverseZeroPointIso.{uModelRing, uModelCarrier} R
      root_inclusion := ?_ }
  have hInc : (Functor.isoWhiskerRight (eqToIso h) J ≪≫ A.inclusion).app z =
      J.mapIso (eqToIso (congrArg (fun q :
        SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ⥤
          SInverseS.ZeroComponent (C := FGProjectiveCat.{max uModelRing uModelCarrier} R) =>
        q.obj z) h)) ≪≫ A.inclusion.app z := by
    change (Functor.isoWhiskerRight (eqToIso h) J).app z ≪≫ A.inclusion.app z = _
    rw [normalizedEqWhiskerRightApp]
  rw [finiteFreeRowProjectiveUniverseZeroPointIso_value, normalizedFunctorMapIsoTrans]
  change J.mapIso (eqToIso (congrArg (fun q :
        SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ⥤
          SInverseS.ZeroComponent (C := FGProjectiveCat.{max uModelRing uModelCarrier} R) =>
        q.obj z) h)) ≪≫ J.mapIso A.root = _
  rw [A.root_inclusion, hInc]
  exact (Iso.trans_assoc _ _ _).symm

private def normalizedIntrinsicZeroLift
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedZeroLiftData (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
      (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f) where
  inclusion := SInverseS.zeroComponentFunctorInclusionIso
    (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  root := nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f
  root_inclusion := by
    rw [SInverseS.zeroComponentFunctorInclusionIso_app_value]
    exact nativeProjectiveZeroScalarZeroPointIso_inclusion_value.{uR, uS, uMR, uMS} f

private abbrev normalizedLegacySourceModule
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
    FGProjectiveCat.scalarExtension.{uR, uS, uR} f

private abbrev normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing}
    (S : Type uTargetRing) [Ring S] :=
  (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
    (FGProjectiveCat.universeEquivalence.{uTargetRing, uSourceCarrier} S).inverse

private def normalizedActualSourceZeroIso
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor ⋙
        nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f ≅
      SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f) ⋙
        SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S) := by
  let P := normalizedModuleModel.{uR, uMR} R
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let Q := normalizedLegacySourceModule f
  let U := normalizedModuleResize.{uR, uS, uMS} S
  let M := (finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor
  let GF := nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f
  let GQ := SInverseS.zeroComponentFunctor Q
  let GU := SInverseS.zeroComponentFunctor U
  let L := normalizedZeroLiftComposite P F M GF
    (normalizedOriginalModelLift.{uR, uMR} R) (normalizedIntrinsicZeroLift.{uR, uS, uMR, uMS} f)
  let R' := normalizedZeroLiftComposite Q U GQ GU
    (normalizedCanonicalZeroLift Q) (normalizedCanonicalZeroLift U)
  exact normalizedZeroLiftNatIso (P ⋙ F) (Q ⋙ U) (M ⋙ GF) (GQ ⋙ GU) L R'
    (nativeProjectiveZeroScalarOriginalModuleSourceIso f)

private theorem normalizedActualSourceZeroRootTriangle
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (normalizedActualSourceZeroIso.{uR, uS, uMR, uMS} f).app
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) ≪≫
      (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S)).mapIso
        (normalizedCanonicalZeroLift (normalizedLegacySourceModule f)).root ≪≫
          (normalizedCanonicalZeroLift (normalizedModuleResize.{uR, uS, uMS} S)).root =
      (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).mapIso
        (finiteFreeRowProjectiveUniverseZeroPointIso.{uR, uMR} R) ≪≫
          nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f := by
  let P := normalizedModuleModel.{uR, uMR} R
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let Q := normalizedLegacySourceModule f
  let U := normalizedModuleResize.{uR, uS, uMS} S
  let M := (finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor
  let GF := nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f
  let GQ := SInverseS.zeroComponentFunctor Q
  let GU := SInverseS.zeroComponentFunctor U
  let L := normalizedZeroLiftComposite P F M GF
    (normalizedOriginalModelLift.{uR, uMR} R) (normalizedIntrinsicZeroLift.{uR, uS, uMR, uMS} f)
  let R' := normalizedZeroLiftComposite Q U GQ GU
    (normalizedCanonicalZeroLift Q) (normalizedCanonicalZeroLift U)
  have hIso : normalizedActualSourceZeroIso.{uR, uS, uMR, uMS} f =
      normalizedZeroLiftNatIso (P ⋙ F) (Q ⋙ U) (M ⋙ GF) (GQ ⋙ GU) L R'
        (nativeProjectiveZeroScalarOriginalModuleSourceIso f) := by
    rfl
  have hLeft : L.root = GF.mapIso
      (finiteFreeRowProjectiveUniverseZeroPointIso.{uR, uMR} R) ≪≫
        nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f := by
    rfl
  have hRight : R'.root = GU.mapIso (normalizedCanonicalZeroLift Q).root ≪≫
      (normalizedCanonicalZeroLift U).root := by
    rfl
  have h := normalizedZeroLiftNatIsoRoot (P ⋙ F) (Q ⋙ U) (M ⋙ GF) (GQ ⋙ GU) L R'
    (nativeProjectiveZeroScalarOriginalModuleSourceIso f)
  rw [← hIso, hLeft, hRight] at h
  exact h

private def normalizedActualTargetZeroIso.{uSourceCarrier, uTargetRing, uTargetCarrier}
    (S : Type uTargetRing) [Ring S] :
    SInverseS.zeroComponentFunctor
        (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S) ⋙
        SInverseS.zeroComponentFunctor
          (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S) ≅
      (finiteFreeRowProjectiveUniverseZeroEquivalence.{uTargetRing, uTargetCarrier} S).functor := by
  let P := normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S
  let U := normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S
  let Q := normalizedModuleModel.{uTargetRing, uTargetCarrier} S
  let GP := SInverseS.zeroComponentFunctor P
  let GU := SInverseS.zeroComponentFunctor U
  let M := (finiteFreeRowProjectiveUniverseZeroEquivalence.{uTargetRing, uTargetCarrier} S).functor
  let L := normalizedZeroLiftComposite P U GP GU
    (normalizedCanonicalZeroLift P) (normalizedCanonicalZeroLift U)
  let R' := normalizedOriginalModelLift.{uTargetRing, uTargetCarrier} S
  exact normalizedZeroLiftNatIso (P ⋙ U) Q (GP ⋙ GU) M L R'
    (nativeProjectiveZeroScalarOriginalModuleTargetIso.{
      uSourceCarrier, uTargetRing, uTargetCarrier} S)

private theorem normalizedActualTargetZeroRootTriangle.{
    uSourceCarrier, uTargetRing, uTargetCarrier} (S : Type uTargetRing) [Ring S] :
    (normalizedActualTargetZeroIso.{uSourceCarrier, uTargetRing, uTargetCarrier} S).app
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel S)) ≪≫
      finiteFreeRowProjectiveUniverseZeroPointIso.{uTargetRing, uTargetCarrier} S =
      (SInverseS.zeroComponentFunctor
        (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).mapIso
        (normalizedCanonicalZeroLift
          (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S)).root ≪≫
          (normalizedCanonicalZeroLift
            (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).root := by
  let P := normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S
  let U := normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S
  let Q := normalizedModuleModel.{uTargetRing, uTargetCarrier} S
  let GP := SInverseS.zeroComponentFunctor P
  let GU := SInverseS.zeroComponentFunctor U
  let M := (finiteFreeRowProjectiveUniverseZeroEquivalence.{uTargetRing, uTargetCarrier} S).functor
  let L := normalizedZeroLiftComposite P U GP GU
    (normalizedCanonicalZeroLift P) (normalizedCanonicalZeroLift U)
  let R' := normalizedOriginalModelLift.{uTargetRing, uTargetCarrier} S
  have hIso : normalizedActualTargetZeroIso.{uSourceCarrier, uTargetRing, uTargetCarrier} S =
      normalizedZeroLiftNatIso (P ⋙ U) Q (GP ⋙ GU) M L R'
        (nativeProjectiveZeroScalarOriginalModuleTargetIso.{
          uSourceCarrier, uTargetRing, uTargetCarrier} S) := by
    rfl
  have hLeft : L.root = GU.mapIso (normalizedCanonicalZeroLift P).root ≪≫
      (normalizedCanonicalZeroLift U).root := by
    rfl
  have hRight : R'.root =
      finiteFreeRowProjectiveUniverseZeroPointIso.{uTargetRing, uTargetCarrier} S := by
    rfl
  have h := normalizedZeroLiftNatIsoRoot (P ⋙ U) Q (GP ⋙ GU) M L R'
    (nativeProjectiveZeroScalarOriginalModuleTargetIso.{
      uSourceCarrier, uTargetRing, uTargetCarrier} S)
  rw [← hIso, hLeft, hRight] at h
  exact h

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uX uY uZ uC vC uD vD

namespace AlgebraicKTheory.StableGL

private def normalizedRootedPreBased
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {Z : Type uZ} [TopologicalSpace Z] {x : X} {y : Y} {z : Z}
    {f g : C(X, Y)} {p : Path (f x) y} {q : Path (g x) y}
    (H : NormalizedRootedFamily x y f g p q) (j : C(Z, X)) (hj : j z = x) :
    NormalizedRootedFamily z y (f.comp j) (g.comp j)
      (p.cast (congrArg f hj) rfl) (q.cast (congrArg g hj) rfl) where
  homotopy := H.homotopy.compContinuousMap j
  root := by
    have h := H.root.pathCast (congrArg f hj) rfl
    rw [Path.cast_trans (H.homotopy.evalAt x) q (congrArg f hj) (congrArg g hj) rfl] at h
    have hEval : (H.homotopy.compContinuousMap j).evalAt z =
        (H.homotopy.evalAt x).cast (congrArg f hj) (congrArg g hj) := by
      apply Path.ext
      funext t
      exact congrArg (fun a => H.homotopy (t, a)) hj
    rw [← hEval] at h
    exact h

private def normalizedRootedPostBased
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {Z : Type uZ} [TopologicalSpace Z] {x : X} {y : Y} {z : Z}
    {f g : C(X, Y)} {p : Path (f x) y} {q : Path (g x) y}
    (H : NormalizedRootedFamily x y f g p q) (k : C(Y, Z)) (hk : k y = z) :
    NormalizedRootedFamily x z (k.comp f) (k.comp g)
      ((p.map k.continuous).cast rfl hk.symm)
      ((q.map k.continuous).cast rfl hk.symm) where
  homotopy := (ContinuousMap.Homotopy.refl k).comp H.homotopy
  root := by
    have h := (H.root.map k).pathCast rfl hk.symm
    rw [Path.map_trans,
      Path.cast_trans ((H.homotopy.evalAt x).map k.continuous)
        (q.map k.continuous) rfl rfl hk.symm] at h
    have hEval : ((ContinuousMap.Homotopy.refl k).comp H.homotopy).evalAt x =
        (H.homotopy.evalAt x).map k.continuous := by
      apply Path.ext
      funext t
      rfl
    rw [← hEval] at h
    exact h

private def normalizedRootedCastMaps
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {x : X} {y : Y} {f g f' g' : C(X, Y)} {p : Path (f x) y} {q : Path (g x) y}
    (H : NormalizedRootedFamily x y f g p q) (hf : f = f') (hg : g = g') :
    NormalizedRootedFamily x y f' g'
      (p.cast (congrArg (fun a : C(X, Y) => a x) hf).symm rfl)
      (q.cast (congrArg (fun a : C(X, Y) => a x) hg).symm rfl) where
  homotopy := H.homotopy.cast hf hg
  root := by
    let hs := (congrArg (fun a : C(X, Y) => a x) hf).symm
    let ht := (congrArg (fun a : C(X, Y) => a x) hg).symm
    have h := H.root.pathCast hs rfl
    rw [Path.cast_trans (H.homotopy.evalAt x) q hs ht rfl] at h
    have hEval : (H.homotopy.cast hf hg).evalAt x =
        (H.homotopy.evalAt x).cast hs ht := by
      apply Path.ext
      funext t
      rfl
    rw [← hEval] at h
    exact h

private abbrev normalizedObjectVertex
    (C : Type uC) [Category.{vC} C] (x : C) : SSet.toTop.obj (nerve C) :=
  SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ x)

private abbrev normalizedEdgePath
    {C : Type uC} [Category.{vC} C] {x y : C} (a : x ⟶ y) :
    Path (normalizedObjectVertex C x) (normalizedObjectVertex C y) :=
  TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk a))

private theorem normalizedEdgeIsoTriangle
    {C : Type uC} [Category.{vC} C] {x y z : C}
    (a : x ≅ y) (p : x ≅ z) (q : y ≅ z) (h : a ≪≫ q = p) :
    (normalizedEdgePath p.hom).Homotopic
      ((normalizedEdgePath a.hom).trans (normalizedEdgePath q.hom)) := by
  have hc : a.hom ≫ q.hom = p.hom := congrArg Iso.hom h
  have ht := (nerve.nonempty_compStruct_iff a.hom q.hom p.hom).2 hc
  exact SSet.realizedCompStructHomotopic ht.some

private def normalizedRootedFunctorNatIso
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F G : C ⥤ D) (alpha : F ≅ G) (x : C) (z : D)
    (p : F.obj x ≅ z) (q : G.obj x ≅ z) (h : alpha.app x ≪≫ q = p) :
    NormalizedRootedFamily (normalizedObjectVertex C x) (normalizedObjectVertex D z)
      (CategoryTheory.realizedNerveFunctorMap F) (CategoryTheory.realizedNerveFunctorMap G)
      ((normalizedEdgePath p.hom).cast (CategoryTheory.realizedNerveFunctorMap_vertex F x) rfl)
      ((normalizedEdgePath q.hom).cast (CategoryTheory.realizedNerveFunctorMap_vertex G x) rfl)
          where
  homotopy := CategoryTheory.realizedNerveFunctorMapHomotopy alpha.hom
  root := by
    let HF := CategoryTheory.realizedNerveFunctorMap_vertex F x
    let HG := CategoryTheory.realizedNerveFunctorMap_vertex G x
    let H := CategoryTheory.realizedNerveFunctorMapHomotopy alpha.hom
    have hTri := (normalizedEdgeIsoTriangle (alpha.app x) p q h).pathCast HF rfl
    rw [Path.cast_trans (normalizedEdgePath (alpha.app x).hom)
      (normalizedEdgePath q.hom) HF HG rfl] at hTri
    have hTrace := (CategoryTheory.realizedNerveFunctorMapHomotopy_vertex alpha.hom x).pathCast HF
        HG
    have hCast : (((H.evalAt (normalizedObjectVertex C x)).cast HF.symm HG.symm).cast HF HG) =
        H.evalAt (normalizedObjectVertex C x) := by
      apply Path.ext
      funext t
      rfl
    rw [hCast] at hTrace
    exact hTri.trans (hTrace.symm.hcomp
      (Path.Homotopic.refl ((normalizedEdgePath q.hom).cast HG rfl)))

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uR uS uMR uMS uNR uNS

namespace AlgebraicKTheory.StableGL

private abbrev normalizedOriginalNorm.{uNormRing, uNormCarrier, uNormNative}
    (R : Type uNormRing) [Ring R] :=
  nativeProjectiveZeroPlusNormalizationOfRing.{uNormRing, uNormCarrier, uNormNative} R

private def normalizedOriginalModelTrace.{uNormRing, uNormCarrier, uNormNative}
    (R : Type uNormRing) [Ring R] :
    ContinuousMap.Homotopy
      (finiteFreeRowProjectiveZeroHomotopyEquiv.{uNormRing, uNormCarrier} R).toFun
      (normalizedOriginalNorm.{uNormRing, uNormCarrier, uNormNative} R).model.toFun :=
  Classical.choose (normalizedOriginalNorm.{uNormRing, uNormCarrier, uNormNative} R).modelTrace

private theorem normalizedOriginalModelTraceRoot.{uNormRing, uNormCarrier, uNormNative}
    (R : Type uNormRing) [Ring R] (t : unitInterval) :
    normalizedOriginalModelTrace.{uNormRing, uNormCarrier, uNormNative} R
        (t, SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R))
            =
      finiteFreeRowProjectiveZeroUnitPath.{uNormRing, uNormCarrier} R t :=
  Classical.choose_spec (normalizedOriginalNorm.{uNormRing, uNormCarrier, uNormNative} R).modelTrace
      t

private def normalizedOriginalModelRooted.{uNormRing, uNormCarrier, uNormNative}
    (R : Type uNormRing) [Ring R] :
    NormalizedRootedFamily
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R))
      (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.{max uNormRing uNormCarrier} R))
      (finiteFreeRowProjectiveZeroHomotopyEquiv.{uNormRing, uNormCarrier} R).toFun
      (normalizedOriginalNorm.{uNormRing, uNormCarrier, uNormNative} R).model.toFun
      (finiteFreeRowProjectiveZeroUnitPath.{uNormRing, uNormCarrier} R)
      ((Path.refl (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.{max uNormRing uNormCarrier} R))).cast
          (normalizedOriginalNorm.{uNormRing, uNormCarrier, uNormNative} R).modelPoint rfl) :=
  normalizedRootedFromTrace (normalizedOriginalModelTrace.{uNormRing, uNormCarrier, uNormNative} R)
    (normalizedOriginalNorm.{uNormRing, uNormCarrier, uNormNative} R).modelPoint
    (finiteFreeRowProjectiveZeroUnitPath.{uNormRing, uNormCarrier} R)
    (normalizedOriginalModelTraceRoot.{uNormRing, uNormCarrier, uNormNative} R)

private def normalizedOriginalRowRooted.{uRowRing} (R : Type uRowRing) [Ring R] :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R))
      (finiteFreeRowStableZeroComparison R).hom (finiteFreeRowBasedZeroComparison R).hom
      (finiteFreeRowStableZeroComparisonUnitPath R)
      ((Path.refl (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.IdempotentModel R))).cast
          (finiteFreeRowBasedZeroComparison_basepoint R) rfl) :=
  normalizedRootedFromTrace (finiteFreeRowBasedZeroComparisonHomotopy R)
    (finiteFreeRowBasedZeroComparison_basepoint R) (finiteFreeRowStableZeroComparisonUnitPath R)
    (finiteFreeRowBasedZeroComparison_homotopy_basepoint R)

private theorem normalizedIntrinsicRetuningRootClock
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f
        (t, RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f t :=
  (congrArg
    (fun H : C(unitInterval × RingK0.projectiveZeroSpace.{uR, uMR, uNR} R,
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) =>
      H (t, RingK0.projectiveZeroPoint.{uR, uMR, uNR} R))
    (nativeProjectiveZeroScalarRetuning_toContinuousMap.{uR, uS, uMR, uMS, uNR, uNS} f)).trans
      (nativeProjectiveZeroScalarRetuningFamily_root_value.{uR, uS, uMR, uMS, uNR, uNS} f t)

private def normalizedIntrinsicRooted
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f)
      ((Path.refl (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)).cast
        (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f) rfl) :=
  normalizedRootedFromTrace
    (nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f)
    (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f)
    (nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f)
    (normalizedIntrinsicRetuningRootClock f)

private abbrev normalizedRowZeroObject.{uRowRing} (R : Type uRowRing) [Ring R] :=
  (finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _)

private def normalizedRowCoreZeroIso.{uRowRing} (R : Type uRowRing) [Ring R] :=
  (Core.isoMk
    (x := ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)⟩)
    (y := ⟨(0 : FGProjectiveCat.IdempotentModel R)⟩)
    (FGProjectiveCat.IdempotentModel.freeZeroIso R)).prod
      (Core.isoMk
        (x := ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)⟩)
        (y := ⟨(0 : FGProjectiveCat.IdempotentModel R)⟩)
        (FGProjectiveCat.IdempotentModel.freeZeroIso R))

private def normalizedRowZeroIso.{uRowRing} (R : Type uRowRing) [Ring R] :
    normalizedRowZeroObject R ≅
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R) :=
  (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι.preimageIso
    (eqToIso (finiteFreeRowZeroComponentFunctor_obj R 0 (SingleObj.star _)) ≪≫
      (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).mapIso
        (normalizedRowCoreZeroIso R))

private theorem normalizedRowZeroIsoHom.{uRowRing} (R : Type uRowRing) [Ring R] :
    (normalizedRowZeroIso R).hom = finiteFreeRowStageZeroToBase R := by
  let J := (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι
  let a := eqToIso (finiteFreeRowZeroComponentFunctor_obj R 0 (SingleObj.star _)) ≪≫
    (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).mapIso
      (normalizedRowCoreZeroIso R)
  apply J.map_injective
  change J.map (J.preimage (X := normalizedRowZeroObject R)
    (Y := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) a.hom) =
      J.map (finiteFreeRowStageZeroToBase R)
  have hValue : a.hom = J.map (finiteFreeRowStageZeroToBase R) := by
    exact (finiteFreeRowStageZeroToBase_inclusion_value R).symm
  exact (J.map_preimage (X := normalizedRowZeroObject R)
    (Y := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))
    a.hom).trans hValue

private theorem normalizedRowZeroIsoInclusion.{uRowRing} (R : Type uRowRing) [Ring R] :
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι.mapIso
        (normalizedRowZeroIso R) =
      eqToIso (finiteFreeRowZeroComponentFunctor_obj R 0 (SingleObj.star _)) ≪≫
        (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).mapIso
          (normalizedRowCoreZeroIso R) := by
  let J := (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι
  let a := eqToIso (finiteFreeRowZeroComponentFunctor_obj R 0 (SingleObj.star _)) ≪≫
    (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).mapIso
      (normalizedRowCoreZeroIso R)
  apply Iso.ext
  change J.map (J.preimage (X := normalizedRowZeroObject R)
    (Y := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) a.hom) = a.hom
  exact J.map_preimage (X := normalizedRowZeroObject R)
    (Y := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) a.hom

private abbrev normalizedBGLScalarSource
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))).comp
      (finiteFreeRowStableZeroComparison R).hom

private abbrev normalizedBGLScalarTarget
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S))).comp
      ((finiteFreeRowStableZeroComparison S).hom.comp (ordinaryBGLScalarMap f))

private def normalizedBGLScalarSourceRoot
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedBGLScalarSource f (ordinaryBGLBasepoint R))
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max uS uR} S)) :=
  (normalizedEdgePath (finiteBGLTelescopeScalarSourceRootZeroIso f).hom).cast
    ((ordinaryBGLScalarOriginalStableRow_source_point f).trans
      (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f))
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max uS uR} S))

private def normalizedBGLScalarTargetRoot
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedBGLScalarTarget f (ordinaryBGLBasepoint R))
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max uS uR} S)) :=
  (normalizedEdgePath (finiteBGLTelescopeScalarTargetRootZeroIso f).hom).cast
    ((ordinaryBGLScalarOriginalStableRow_target_point f).trans
      (ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f))
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max uS uR} S))

private def normalizedOriginalBGLScalarRooted
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max uS uR} S))
      (normalizedBGLScalarSource f) (normalizedBGLScalarTarget f)
      (normalizedBGLScalarSourceRoot f) (normalizedBGLScalarTargetRoot f) where
  homotopy := ordinaryBGLScalarOriginalStableRowHomotopy f
  root := by
    let hs := (ordinaryBGLScalarOriginalStableRow_source_point f).trans
      (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f)
    let hz := SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max uS uR} S)
    have h := (ordinaryBGLScalarOriginalStableRow_original_root_trace f).pathCast hs hz
    exact h.trans (normalizedRootPathHomotopicOfEq (by
      apply Path.ext
      funext t
      rfl))

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uR uS uMR uMS

namespace AlgebraicKTheory.StableGL

private theorem normalizedOriginalModelZeroVertex.{uModelRing, uModelCarrier}
    (R : Type uModelRing) [Ring R] :
    (finiteFreeRowProjectiveZeroHomotopyEquiv.{uModelRing, uModelCarrier} R).toFun
        (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)) =
      normalizedObjectVertex (SInverseS.ZeroComponent
        (C := FGProjectiveCat.{max uModelRing uModelCarrier} R))
        ((finiteFreeRowProjectiveUniverseZeroEquivalence.{uModelRing, uModelCarrier} R).functor.obj
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))) := by
  rw [finiteFreeRowProjectiveZeroHomotopyEquiv_value]
  let E := finiteFreeRowProjectiveUniverseZeroEquivalence.{uModelRing, uModelCarrier} R
  exact (congrArg (CategoryTheory.realizedNerveEquivalence E).toFun
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.IdempotentModel R))).trans
        (CategoryTheory.realizedNerveEquivalence_vertex E
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)))

private theorem normalizedOriginalModelUnitEdge.{uModelRing, uModelCarrier}
    (R : Type uModelRing) [Ring R] :
    finiteFreeRowProjectiveZeroUnitPath.{uModelRing, uModelCarrier} R =
      (normalizedEdgePath
        (finiteFreeRowProjectiveUniverseZeroPointIso.{uModelRing, uModelCarrier} R).hom).cast
        (normalizedOriginalModelZeroVertex.{uModelRing, uModelCarrier} R)
        (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
          (C := FGProjectiveCat.{max uModelRing uModelCarrier} R)) := by
  apply Path.ext
  funext t
  exact finiteFreeRowProjectiveZeroUnitPath_value.{uModelRing, uModelCarrier} R t

private theorem normalizedOriginalRowUnitEdge.{uRowRing} (R : Type uRowRing) [Ring R] :
    finiteFreeRowStableZeroComparisonUnitPath R =
      (normalizedEdgePath (normalizedRowZeroIso R).hom).cast
        (finiteFreeRowStableZeroComparison_basepoint R)
        (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
          (C := FGProjectiveCat.IdempotentModel R)) := by
  apply Path.ext
  funext t
  rw [normalizedRowZeroIsoHom]
  exact finiteFreeRowStableZeroComparisonUnitPath_value R t

private def normalizedRowFunctorRoot.{uRowRing, uTargetObj, uTargetHom}
    (R : Type uRowRing) [Ring R]
    {D : Type uTargetObj} [Category.{uTargetHom} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D]
    (G : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ⥤
      SInverseS.ZeroComponent (C := D))
    (r : G.obj (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) ≅
      SInverseS.zeroComponentBaseObject (C := D)) :
    G.obj (normalizedRowZeroObject R) ≅ SInverseS.zeroComponentBaseObject (C := D) :=
  G.mapIso (normalizedRowZeroIso R) ≪≫ r

private theorem normalizedRowNatIsoRootTriangle.{uRowRing, uTargetObj, uTargetHom}
    (R : Type uRowRing) [Ring R]
    {D : Type uTargetObj} [Category.{uTargetHom} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D]
    (G K : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ⥤
      SInverseS.ZeroComponent (C := D)) (a : G ≅ K)
    (r : G.obj (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) ≅
      SInverseS.zeroComponentBaseObject (C := D))
    (s : K.obj (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) ≅
      SInverseS.zeroComponentBaseObject (C := D))
    (h : a.app (SInverseS.zeroComponentBaseObject
      (C := FGProjectiveCat.IdempotentModel R)) ≪≫ s = r) :
    a.app (normalizedRowZeroObject R) ≪≫ normalizedRowFunctorRoot R K s =
      normalizedRowFunctorRoot R G r := by
  apply Iso.ext
  change (a.app (normalizedRowZeroObject R)).hom ≫
      K.map (normalizedRowZeroIso R).hom ≫ s.hom =
    G.map (normalizedRowZeroIso R).hom ≫ r.hom
  have hNaturality := congrArg (fun k => k ≫ s.hom)
    (a.hom.naturality (normalizedRowZeroIso R).hom).symm
  have hRoot : (a.app (SInverseS.zeroComponentBaseObject
      (C := FGProjectiveCat.IdempotentModel R))).hom ≫ s.hom = r.hom :=
    congrArg Iso.hom h
  have hTypedNaturality : (a.app (normalizedRowZeroObject R)).hom ≫
      K.map (normalizedRowZeroIso R).hom ≫ s.hom =
        G.map (normalizedRowZeroIso R).hom ≫
          (a.app (SInverseS.zeroComponentBaseObject
            (C := FGProjectiveCat.IdempotentModel R))).hom ≫ s.hom := by
    simpa only [Category.assoc, Iso.app_hom] using hNaturality
  exact hTypedNaturality.trans
    (congrArg (fun k => G.map (normalizedRowZeroIso R).hom ≫ k) hRoot)

private def normalizedActualSourceZeroRooted
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  normalizedRootedFunctorNatIso
    ((finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor ⋙
      nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)
    (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f) ⋙
      SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))
    (normalizedActualSourceZeroIso.{uR, uS, uMR, uMS} f)
    (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))
    (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uMS} S))
    ((nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).mapIso
      (finiteFreeRowProjectiveUniverseZeroPointIso.{uR, uMR} R) ≪≫
      nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f)
    ((SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S)).mapIso
      (normalizedCanonicalZeroLift (normalizedLegacySourceModule f)).root ≪≫
      (normalizedCanonicalZeroLift (normalizedModuleResize.{uR, uS, uMS} S)).root)
    (normalizedActualSourceZeroRootTriangle f)

private def normalizedActualTargetRowRooted.{uSourceCarrier, uTargetRing, uTargetCarrier}
    (S : Type uTargetRing) [Ring S] :=
  let leftZeroFunctor := SInverseS.zeroComponentFunctor
      (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S) ⋙
      SInverseS.zeroComponentFunctor
        (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)
  let rightZeroFunctor :=
    (finiteFreeRowProjectiveUniverseZeroEquivalence.{uTargetRing, uTargetCarrier} S).functor
  let a := normalizedActualTargetZeroIso.{uSourceCarrier, uTargetRing, uTargetCarrier} S
  let r := (SInverseS.zeroComponentFunctor
    (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).mapIso
      (normalizedCanonicalZeroLift
        (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S)).root ≪≫
      (normalizedCanonicalZeroLift
        (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).root
  let s := finiteFreeRowProjectiveUniverseZeroPointIso.{uTargetRing, uTargetCarrier} S
  normalizedRootedFunctorNatIso
    (C := SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel S))
    (D := SInverseS.ZeroComponent
      (C := FGProjectiveCat.{max uTargetRing uTargetCarrier} S))
    leftZeroFunctor rightZeroFunctor a (normalizedRowZeroObject S)
    (SInverseS.zeroComponentBaseObject
      (C := FGProjectiveCat.{max uTargetRing uTargetCarrier} S))
    (normalizedRowFunctorRoot
      (D := FGProjectiveCat.{max uTargetRing uTargetCarrier} S)
      S leftZeroFunctor r)
    (normalizedRowFunctorRoot
      (D := FGProjectiveCat.{max uTargetRing uTargetCarrier} S)
      S rightZeroFunctor s)
    (normalizedRowNatIsoRootTriangle
      (D := FGProjectiveCat.{max uTargetRing uTargetCarrier} S) S leftZeroFunctor rightZeroFunctor
        a r s
      (normalizedActualTargetZeroRootTriangle.{uSourceCarrier, uTargetRing, uTargetCarrier} S))

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uC vC uD vD

namespace AlgebraicKTheory.StableGL

private theorem normalizedFunctorMapEqToHom
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) {X Y : C} (h : X = Y) :
    F.map (eqToHom h) = eqToHom (congrArg F.obj h) := by
  cases h
  exact F.map_id X

private theorem normalizedEqToHomTrans
    {C : Type uC} [Category.{vC} C] {X Y Z : C} (h : X = Y) (k : Y = Z) :
    eqToHom (h.trans k) = eqToHom h ≫ eqToHom k := by
  cases h
  cases k
  exact (Category.id_comp _).symm

private theorem normalizedCanonicalCoordinateRootRoute
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (X0 : C) (e0 : X0 ≅ (0 : C))
    (X : SInverseS.ZeroComponent (C := C))
    (hX : X.obj = (⟨X0, X0⟩ : SInverseS.Pair C))
    (u : X ⟶ SInverseS.zeroComponentBaseObject (C := C))
    (hU : (SInverseS.zeroComponentProperty (C := C)).ι.map u =
      eqToHom hX ≫ (SInverseS.corePairInclusion (C := C)).map
        ((Core.isoMk (x := ⟨X0⟩) (y := ⟨(0 : C)⟩) e0).prod
          (Core.isoMk (x := ⟨X0⟩) (y := ⟨(0 : C)⟩) e0)).hom) :
    let hs := (SInverseS.zeroComponentFunctor_obj_obj F X).trans
      ((congrArg (SInverseS.pairFunctor F).obj hX).trans
        ((SInverseS.pairFunctor_characteristic F F (Iso.refl F) (𝟭 D)).1 ⟨X0, X0⟩))
    (SInverseS.zeroComponentProperty (C := D)).ι.map
      ((SInverseS.zeroComponentFunctor F).map u ≫ (normalizedCanonicalZeroLift F).root.hom) =
      eqToHom hs ≫ (SInverseS.corePairInclusion (C := D)).map
        ((Core.isoMk (x := ⟨F.obj X0⟩) (y := ⟨(0 : D)⟩)
          (F.mapIso e0 ≪≫ F.mapZeroObject)).prod
          (Core.isoMk (x := ⟨F.obj X0⟩) (y := ⟨(0 : D)⟩)
            (F.mapIso e0 ≪≫ F.mapZeroObject))).hom := by
  rcases X with ⟨X, hProperty⟩
  cases hX
  let x : SInverseS.ZeroComponent (C := C) := ⟨(⟨X0, X0⟩ : SInverseS.Pair C), hProperty⟩
  let z := SInverseS.zeroComponentBaseObject (C := C)
  let JC := (SInverseS.zeroComponentProperty (C := C)).ι
  let JD := (SInverseS.zeroComponentProperty (C := D)).ι
  let KC := SInverseS.corePairInclusion (C := C)
  let KD := SInverseS.corePairInclusion (C := D)
  let GF := SInverseS.zeroComponentFunctor F
  let PF := SInverseS.pairFunctor F
  let i := SInverseS.zeroComponentFunctorInclusionIso F
  let r := (normalizedCanonicalZeroLift F).root
  let a := (Core.isoMk (x := ⟨X0⟩) (y := ⟨(0 : C)⟩) e0).prod
    (Core.isoMk (x := ⟨X0⟩) (y := ⟨(0 : C)⟩) e0)
  let b := (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject).prod
    (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject)
  let c := (Core.isoMk (x := ⟨F.obj X0⟩) (y := ⟨(0 : D)⟩)
    (F.mapIso e0 ≪≫ F.mapZeroObject)).prod
    (Core.isoMk (x := ⟨F.obj X0⟩) (y := ⟨(0 : D)⟩)
      (F.mapIso e0 ≪≫ F.mapZeroObject))
  let ma := (F.core.prod F.core).map a.hom
  have hCore : ma ≫ b.hom = c.hom := by
    apply Prod.ext <;> apply Core.hom_ext <;> rfl
  have hu : JC.map u = KC.map a.hom := by
    simpa only [eqToHom_refl, Category.id_comp] using hU
  have hMapped : PF.map (JC.map u) = KD.map ma :=
    (congrArg PF.map hu).trans ((SInverseS.coreTranslation_characteristic F).1 a.hom)
  have hZero : (SInverseS.zeroPairIso F).hom = KD.map b.hom :=
    congrArg Iso.hom ((SInverseS.coreTranslation_characteristic F).2.2.2.2.2.2.2.2.1)
  have hr : JD.map r.hom = (i.app z).hom ≫ (SInverseS.zeroPairIso F).hom :=
    congrArg Iso.hom (normalizedCanonicalZeroLift F).root_inclusion
  have hn : JD.map (GF.map u) ≫ (i.app z).hom =
      (i.app x).hom ≫ PF.map (JC.map u) := i.hom.naturality u
  have hi : (i.app x).hom = eqToHom (SInverseS.zeroComponentFunctor_obj_obj F x) :=
    congrArg Iso.hom (SInverseS.zeroComponentFunctorInclusionIso_app_value F x)
  change JD.map (GF.map u ≫ r.hom) =
    eqToHom (SInverseS.zeroComponentFunctor_obj_obj F x) ≫ KD.map c.hom
  have h1 := JD.map_comp (GF.map u) r.hom
  have h2 : JD.map (GF.map u) ≫ JD.map r.hom =
      JD.map (GF.map u) ≫ ((i.app z).hom ≫ (SInverseS.zeroPairIso F).hom) :=
    congrArg (fun k => JD.map (GF.map u) ≫ k) hr
  have h3 : JD.map (GF.map u) ≫ ((i.app z).hom ≫ (SInverseS.zeroPairIso F).hom) =
      (i.app x).hom ≫ PF.map (JC.map u) ≫ (SInverseS.zeroPairIso F).hom :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (SInverseS.zeroPairIso F).hom) hn)).trans
        (Category.assoc _ _ _)
  have h4 : (i.app x).hom ≫ PF.map (JC.map u) ≫ (SInverseS.zeroPairIso F).hom =
      eqToHom (SInverseS.zeroComponentFunctor_obj_obj F x) ≫ KD.map ma ≫ KD.map b.hom :=
    congrArg₂ (fun p q => p ≫ q) hi
      (congrArg₂ (fun p q => p ≫ q) hMapped hZero)
  have h5 : eqToHom (SInverseS.zeroComponentFunctor_obj_obj F x) ≫ KD.map ma ≫ KD.map b.hom =
      eqToHom (SInverseS.zeroComponentFunctor_obj_obj F x) ≫ KD.map c.hom :=
    congrArg (fun k => eqToHom (SInverseS.zeroComponentFunctor_obj_obj F x) ≫ k)
      ((KD.map_comp ma b.hom).symm.trans (congrArg KD.map hCore))
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uR uS

namespace AlgebraicKTheory.StableGL

private theorem normalizedOriginalRowArrowTransport.{uRowRing}
    (R : Type uRowRing) [Ring R]
    (X : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
    (hBase : X = normalizedRowZeroObject R) :
    let hX := (congrArg
      (fun Y : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) => Y.obj)
      hBase).trans (finiteFreeRowZeroComponentFunctor_obj R 0 (SingleObj.star _))
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι.map
      (eqToHom hBase ≫ finiteFreeRowStageZeroToBase R) =
      eqToHom hX ≫ (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).map
        (normalizedRowCoreZeroIso R).hom := by
  cases hBase
  change (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι.map
    (𝟙 _ ≫ finiteFreeRowStageZeroToBase R) =
    eqToHom (finiteFreeRowZeroComponentFunctor_obj R 0 (SingleObj.star _)) ≫
      (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).map
        (normalizedRowCoreZeroIso R).hom
  simpa only [Category.id_comp, normalizedRowCoreZeroIso] using
    finiteFreeRowStageZeroToBase_inclusion_value R

private theorem normalizedOriginalGammaSourceUnitIso
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    finiteBGLTelescopeScalarSourceRootZeroIso f =
      eqToIso (congrArg (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)).obj
        (finiteBGLTelescopeToRowZeroComponent_base R)) ≪≫
        normalizedRowFunctorRoot R
          (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
          (normalizedCanonicalZeroLift (normalizedLegacySourceModule f)).root := by
  let Q := normalizedLegacySourceModule f
  let G := SInverseS.zeroComponentFunctor Q
  let X := (finiteBGLTelescopeToRowZeroComponent R).obj (finiteBGLTelescopeBaseObject R)
  let hBase := finiteBGLTelescopeToRowZeroComponent_base R
  let hX := (congrArg
    (fun Y : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) => Y.obj)
    hBase).trans (finiteFreeRowZeroComponentFunctor_obj R 0 (SingleObj.star _))
  let u : X ⟶ SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R) :=
    eqToHom hBase ≫ finiteFreeRowStageZeroToBase R
  let JD := (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι
  have hRoute := normalizedCanonicalCoordinateRootRoute Q
    ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ))
    (FGProjectiveCat.IdempotentModel.freeZeroIso R) X hX u
    (normalizedOriginalRowArrowTransport R X hBase)
  let KD := SInverseS.corePairInclusion (C := FGProjectiveCat.{max uS uR} S)
  let c := (Core.isoMk
    (x := ⟨Q.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ))⟩)
    (y := ⟨(0 : FGProjectiveCat.{max uS uR} S)⟩)
    (Q.mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso R) ≪≫ Q.mapZeroObject)).prod
      (Core.isoMk
        (x := ⟨Q.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ))⟩)
        (y := ⟨(0 : FGProjectiveCat.{max uS uR} S)⟩)
        (Q.mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso R) ≪≫ Q.mapZeroObject))
  let h01 := SInverseS.zeroComponentFunctor_obj_obj Q X
  let h12 := finiteBGLTelescopeRowScalar_source_obj f (finiteBGLTelescopeBaseObject R)
  let hs := h01.trans
    ((congrArg (SInverseS.pairFunctor Q).obj hX).trans
      ((SInverseS.pairFunctor_characteristic Q Q (Iso.refl Q) (𝟭 _)).1
        ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ),
          (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)⟩))
  have hWhole : JD.mapIso (finiteBGLTelescopeScalarSourceRootZeroIso f) =
      eqToIso h01 ≪≫ eqToIso h12 ≪≫ KD.mapIso c :=
    (finiteBGLTelescopeScalarSourceRootZeroIso_inclusion f).trans
      (congrArg₂ Iso.trans
        (finiteBGLTelescopeScalarSourceZeroInclusionIso_app_value f
          (finiteBGLTelescopeBaseObject R))
        (finiteBGLTelescopeScalarSourceRootIso_value f))
  have hGiven : JD.map (finiteBGLTelescopeScalarSourceRootZeroIso f).hom =
      eqToHom h01 ≫ eqToHom h12 ≫ KD.map c.hom :=
    congrArg Iso.hom hWhole
  have hCast : eqToHom h01 ≫ eqToHom h12 = eqToHom hs :=
    (normalizedEqToHomTrans h01 h12).symm
  have hCollapsed : eqToHom h01 ≫ eqToHom h12 ≫ KD.map c.hom =
      eqToHom hs ≫ KD.map c.hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ KD.map c.hom) hCast)
  have hGamma : JD.map (finiteBGLTelescopeScalarSourceRootZeroIso f).hom =
      JD.map (G.map u ≫ (normalizedCanonicalZeroLift Q).root.hom) :=
    hGiven.trans (hCollapsed.trans hRoute.symm)
  have hArrow : G.map u ≫ (normalizedCanonicalZeroLift Q).root.hom =
      eqToHom (congrArg G.obj hBase) ≫
        (normalizedRowFunctorRoot R G (normalizedCanonicalZeroLift Q).root).hom := by
    change G.map (eqToHom hBase ≫ finiteFreeRowStageZeroToBase R) ≫
      (normalizedCanonicalZeroLift Q).root.hom =
      eqToHom (congrArg G.obj hBase) ≫ G.map (normalizedRowZeroIso R).hom ≫
        (normalizedCanonicalZeroLift Q).root.hom
    rw [G.map_comp, normalizedFunctorMapEqToHom, normalizedRowZeroIsoHom, Category.assoc]
  apply Iso.ext
  apply JD.map_injective
  exact hGamma.trans (congrArg JD.map hArrow)

private theorem normalizedOriginalGammaTargetUnitIso
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    let hBase := (congrArg (finiteBGLTelescopeToRowZeroComponent S).obj
      (finiteBGLTelescopeScalarFunctor_baseObject f)).trans
      (finiteBGLTelescopeToRowZeroComponent_base S)
    finiteBGLTelescopeScalarTargetRootZeroIso f =
      eqToIso (congrArg
        (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S)).obj hBase) ≪≫
        normalizedRowFunctorRoot S
          (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S))
          (normalizedCanonicalZeroLift (normalizedLegacyTargetModule.{uR, uS} S)).root := by
  let Q := normalizedLegacyTargetModule.{uR, uS} S
  let G := SInverseS.zeroComponentFunctor Q
  let X := (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S).obj
    (finiteBGLTelescopeBaseObject R)
  let hBase := (congrArg (finiteBGLTelescopeToRowZeroComponent S).obj
    (finiteBGLTelescopeScalarFunctor_baseObject f)).trans
    (finiteBGLTelescopeToRowZeroComponent_base S)
  let hX := (congrArg
    (fun Y : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel S) => Y.obj)
    hBase).trans (finiteFreeRowZeroComponentFunctor_obj S 0 (SingleObj.star _))
  let u : X ⟶ SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel S) :=
    eqToHom hBase ≫ finiteFreeRowStageZeroToBase S
  let JD := (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι
  have hRoute := normalizedCanonicalCoordinateRootRoute Q
    ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ))
    (FGProjectiveCat.IdempotentModel.freeZeroIso S) X hX u
    (normalizedOriginalRowArrowTransport S X hBase)
  let KD := SInverseS.corePairInclusion (C := FGProjectiveCat.{max uS uR} S)
  let c := (Core.isoMk
    (x := ⟨Q.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ))⟩)
    (y := ⟨(0 : FGProjectiveCat.{max uS uR} S)⟩)
    (Q.mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso S) ≪≫ Q.mapZeroObject)).prod
      (Core.isoMk
        (x := ⟨Q.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ))⟩)
        (y := ⟨(0 : FGProjectiveCat.{max uS uR} S)⟩)
        (Q.mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso S) ≪≫ Q.mapZeroObject))
  let h01 := SInverseS.zeroComponentFunctor_obj_obj Q X
  let h12 := finiteBGLTelescopeRowScalar_target_obj f (finiteBGLTelescopeBaseObject R)
  let hs := h01.trans
    ((congrArg (SInverseS.pairFunctor Q).obj hX).trans
      ((SInverseS.pairFunctor_characteristic Q Q (Iso.refl Q) (𝟭 _)).1
        ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ),
          (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ)⟩))
  have hWhole : JD.mapIso (finiteBGLTelescopeScalarTargetRootZeroIso f) =
      eqToIso h01 ≪≫ eqToIso h12 ≪≫ KD.mapIso c :=
    (finiteBGLTelescopeScalarTargetRootZeroIso_inclusion f).trans
      (congrArg₂ Iso.trans
        (finiteBGLTelescopeScalarTargetZeroInclusionIso_app_value f
          (finiteBGLTelescopeBaseObject R))
        (finiteBGLTelescopeScalarTargetRootIso_value f))
  have hGiven : JD.map (finiteBGLTelescopeScalarTargetRootZeroIso f).hom =
      eqToHom h01 ≫ eqToHom h12 ≫ KD.map c.hom :=
    congrArg Iso.hom hWhole
  have hCast : eqToHom h01 ≫ eqToHom h12 = eqToHom hs :=
    (normalizedEqToHomTrans h01 h12).symm
  have hCollapsed : eqToHom h01 ≫ eqToHom h12 ≫ KD.map c.hom =
      eqToHom hs ≫ KD.map c.hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ KD.map c.hom) hCast)
  have hGamma : JD.map (finiteBGLTelescopeScalarTargetRootZeroIso f).hom =
      JD.map (G.map u ≫ (normalizedCanonicalZeroLift Q).root.hom) :=
    hGiven.trans (hCollapsed.trans hRoute.symm)
  have hArrow : G.map u ≫ (normalizedCanonicalZeroLift Q).root.hom =
      eqToHom (congrArg G.obj hBase) ≫
        (normalizedRowFunctorRoot S G (normalizedCanonicalZeroLift Q).root).hom := by
    change G.map (eqToHom hBase ≫ finiteFreeRowStageZeroToBase S) ≫
      (normalizedCanonicalZeroLift Q).root.hom =
      eqToHom (congrArg G.obj hBase) ≫ G.map (normalizedRowZeroIso S).hom ≫
        (normalizedCanonicalZeroLift Q).root.hom
    rw [G.map_comp, normalizedFunctorMapEqToHom, normalizedRowZeroIsoHom, Category.assoc]
  apply Iso.ext
  apply JD.map_injective
  exact hGamma.trans (congrArg JD.map hArrow)

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uR uS uMR uMS uNR uNS

namespace AlgebraicKTheory.StableGL

private abbrev normalizedNativeChart.{uChartRing, uChartCarrier, uChartNative}
    (R : Type uChartRing) [Ring R] :
    RingK0.projectiveZeroSpace.{uChartRing, uChartCarrier, uChartNative} R ≅
      SInverseS.ComponentTranslation.zeroSpace
        (C := FGProjectiveCat.{max uChartRing uChartCarrier} R) :=
  SInverseS.ComponentTranslation.nativeZeroRealizationIso.{
    (max uChartRing uChartCarrier) + 1, max uChartRing uChartCarrier, uChartNative}
    (C := FGProjectiveCat.{max uChartRing uChartCarrier} R)

private theorem normalizedNativeChartPoint.{uChartRing, uChartCarrier, uChartNative}
    (R : Type uChartRing) [Ring R] :
    (normalizedNativeChart.{uChartRing, uChartCarrier, uChartNative} R).hom
        (RingK0.projectiveZeroPoint.{uChartRing, uChartCarrier, uChartNative} R) =
      SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.{max uChartRing uChartCarrier} R) :=
  (congrArg (normalizedNativeChart.{uChartRing, uChartCarrier, uChartNative} R).hom
    (RingK0.projectiveZeroPoint_eq_native.{uChartRing, uChartCarrier, uChartNative} R)).trans
    (SInverseS.ComponentTranslation.nativeZeroRealizationIso_point.{
      (max uChartRing uChartCarrier) + 1, max uChartRing uChartCarrier, uChartNative}
      (C := FGProjectiveCat.{max uChartRing uChartCarrier} R))

private theorem normalizedNativeChartInvPoint.{uChartRing, uChartCarrier, uChartNative}
    (R : Type uChartRing) [Ring R] :
    (normalizedNativeChart.{uChartRing, uChartCarrier, uChartNative} R).inv
        (SInverseS.ComponentTranslation.zeroSpacePoint
          (C := FGProjectiveCat.{max uChartRing uChartCarrier} R)) =
      RingK0.projectiveZeroPoint.{uChartRing, uChartCarrier, uChartNative} R :=
  (SInverseS.ComponentTranslation.nativeZeroRealizationIso_inv_point.{
    (max uChartRing uChartCarrier) + 1, max uChartRing uChartCarrier, uChartNative}
    (C := FGProjectiveCat.{max uChartRing uChartCarrier} R)).trans
    (RingK0.projectiveZeroPoint_eq_native.{uChartRing, uChartCarrier, uChartNative} R).symm

private theorem normalizedIntrinsicRawOrdinaryVertex
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (normalizedNativeChart.{uS, uMS, uNS} S).hom
        (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
          (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)) =
      normalizedObjectVertex
        (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))
        ((nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).obj
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R))) := by
  let nativeR := normalizedNativeChart.{uR, uMR, uNR} R
  let nativeS := normalizedNativeChart.{uS, uMS, uNS} S
  let GF := nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f
  let FM := CategoryTheory.realizedNerveFunctorMap GF
  let r := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R
  have hRaw := congrArg
    (fun q : C(RingK0.projectiveZeroSpace.{uR, uMR, uNR} R,
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) => q r)
    (nativeProjectiveZeroScalarRawMap_value.{uR, uS, uMR, uMS, uNR, uNS} f)
  calc
    nativeS.hom (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f r) =
        nativeS.hom (nativeS.inv (FM (nativeR.hom r))) := congrArg nativeS.hom hRaw
    _ = FM (nativeR.hom r) := TopCat.inv_hom_id_apply nativeS _
    _ = FM (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.{max uR uMR} R)) :=
      congrArg FM (normalizedNativeChartPoint.{uR, uMR, uNR} R)
    _ = FM (normalizedObjectVertex
        (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R))
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R))) :=
      congrArg FM (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
        (C := FGProjectiveCat.{max uR uMR} R))
    _ = _ := CategoryTheory.realizedNerveFunctorMap_vertex GF _

private theorem normalizedIntrinsicTargetOrdinaryVertex
    (S : Type uS) [Ring S] :
    (normalizedNativeChart.{uS, uMS, uNS} S).hom
        (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) =
      normalizedObjectVertex
        (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uMS} S)) :=
  (normalizedNativeChartPoint.{uS, uMS, uNS} S).trans
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max uS uMS} S))

private theorem normalizedIntrinsicRootOrdinaryEdge
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (((nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).map
      (normalizedNativeChart.{uS, uMS, uNS} S).hom.hom.continuous).cast
        (normalizedIntrinsicRawOrdinaryVertex f).symm
        (normalizedIntrinsicTargetOrdinaryVertex S).symm).Homotopic
      (normalizedEdgePath (nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f).hom) := by
  let D := SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S)
  let zR := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R)
  let x := (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).obj zR
  let y := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uMS} S)
  let e := nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f
  let HD := SSet.realizedNerveLiftHomeomorph.{((max uS uMS) + 1), ((max uS uMS) + 1), max ((max uR
      uMR) + 1) ((max uS uMS) + 1) uNR uNS} D
  let p := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (C := ULiftHom.{max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS} (ULift.{max
        ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS} D))
      (x := ULiftHom.objUp (ULift.up x)) (y := ULiftHom.objUp (ULift.up y))
      (ULiftHom.up.map (ULift.upFunctor.map e.hom))))
  have hEdge := SSet.realizedNerveLiftHomeomorph_edge_homotopic.{
    ((max uS uMS) + 1), ((max uS uMS) + 1), max ((max uR uMR) + 1) ((max uS uMS) + 1) uNR uNS} D
        e.hom
  have hValue :
      (((nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).map
        (normalizedNativeChart.{uS, uMS, uNS} S).hom.hom.continuous).cast
          (normalizedIntrinsicRawOrdinaryVertex f).symm
          (normalizedIntrinsicTargetOrdinaryVertex S).symm) =
      ((p.map HD.continuous_toFun).cast
        (SSet.realizedNerveLiftHomeomorph_vertex.{((max uS uMS) + 1), ((max uS uMS) + 1), max ((max
            uR uMR) + 1) ((max uS uMS) + 1) uNR uNS} D x).symm
        (SSet.realizedNerveLiftHomeomorph_vertex.{((max uS uMS) + 1), ((max uS uMS) + 1), max ((max
            uR uMR) + 1) ((max uS uMS) + 1) uNR uNS} D y).symm) := by
    apply Path.ext
    funext t
    change (normalizedNativeChart.{uS, uMS, uNS} S).hom
      (nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f t) = HD (p t)
    rw [nativeProjectiveZeroScalarRawRootPath_value]
    exact TopCat.inv_hom_id_apply (normalizedNativeChart.{uS, uMS, uNS} S) _
  exact (normalizedRootPathHomotopicOfEq hValue).trans hEdge

private theorem normalizedIntrinsicRawNativeVertex
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
        (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv
        (normalizedObjectVertex
          (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))
          ((nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f).obj
            (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R)))) :=
  (TopCat.hom_inv_id_apply (normalizedNativeChart.{uS, uMS, uNS} S)
    (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R))).symm.trans
    (congrArg (normalizedNativeChart.{uS, uMS, uNS} S).inv
      (normalizedIntrinsicRawOrdinaryVertex f))

private theorem normalizedIntrinsicTargetNativeVertex
    (S : Type uS) [Ring S] :
    RingK0.projectiveZeroPoint.{uS, uMS, uNS} S =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv
        (normalizedObjectVertex
          (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uMS} S))) :=
  (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm.trans
    (congrArg (normalizedNativeChart.{uS, uMS, uNS} S).inv
      (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
        (C := FGProjectiveCat.{max uS uMS} S)))

private theorem normalizedIntrinsicRootNativeEdge
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).Homotopic
      (((normalizedEdgePath
        (nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f).hom).map
          (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous).cast
            (normalizedIntrinsicRawNativeVertex.{uR, uS, uMR, uMS, uNR, uNS} f)
              (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)) := by
  let nativeS := normalizedNativeChart.{uS, uMS, uNS} S
  let theta := nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f
  have h := ((normalizedIntrinsicRootOrdinaryEdge f).map nativeS.inv.hom).pathCast
    (normalizedIntrinsicRawNativeVertex.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)
  have hLeft :
      (((theta.map nativeS.hom.hom.continuous).cast
        (normalizedIntrinsicRawOrdinaryVertex f).symm
        (normalizedIntrinsicTargetOrdinaryVertex S).symm).map nativeS.inv.hom.continuous).cast
          (normalizedIntrinsicRawNativeVertex.{uR, uS, uMR, uMS, uNR, uNS} f)
            (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S) =
        theta := by
    apply Path.ext
    funext t
    exact TopCat.hom_inv_id_apply nativeS (theta t)
  rw [hLeft] at h
  exact h

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uR uS uMR uMS uNR uNS

namespace AlgebraicKTheory.StableGL

private theorem normalizedOriginalModelForwardMap.{uModelRing, uModelCarrier}
    (R : Type uModelRing) [Ring R] :
    (finiteFreeRowProjectiveZeroHomotopyEquiv.{uModelRing, uModelCarrier} R).toFun =
      CategoryTheory.realizedNerveFunctorMap
        (finiteFreeRowProjectiveUniverseZeroEquivalence.{uModelRing, uModelCarrier} R).functor := by
  rw [finiteFreeRowProjectiveZeroHomotopyEquiv_value]
  let E := finiteFreeRowProjectiveUniverseZeroEquivalence.{uModelRing, uModelCarrier} R
  have hE := CategoryTheory.realizedNerveEquivalence_toFun_recipe E
  have hF := CategoryTheory.realizedNerveFunctorMap_larger_recipe.{
    uModelRing, uModelRing, (max uModelRing uModelCarrier) + 1,
      (max uModelRing uModelCarrier) + 1, 0} E.functor
  exact hE.trans hF.symm

private theorem normalizedRawScalarPreSourceChart
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
        (normalizedNativeChart.{uR, uMR, uNR} R).inv.hom =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
        (CategoryTheory.realizedNerveFunctorMap
          (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)) := by
  rw [nativeProjectiveZeroScalarRawMap_value]
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun a => (normalizedNativeChart.{uS, uMS, uNS} S).inv
    (CategoryTheory.realizedNerveFunctorMap
      (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f) a))
    (TopCat.inv_hom_id_apply (normalizedNativeChart.{uR, uMR, uNR} R) x)

private abbrev normalizedSourceStage0
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
    (normalizedOriginalNorm.{uR, uMR, uNR} R).sourceMap

private abbrev normalizedSourceStage1
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
    (normalizedOriginalNorm.{uR, uMR, uNR} R).sourceMap

private abbrev normalizedSourceStage2
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
    ((CategoryTheory.realizedNerveFunctorMap
      (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)).comp
      ((finiteFreeRowProjectiveZeroHomotopyEquiv.{uR, uMR} R).toFun.comp
        (finiteFreeRowBasedZeroComparison R).hom))

private abbrev normalizedSourceStage3
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
    ((CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))).comp
        (finiteFreeRowBasedZeroComparison R).hom))

private abbrev normalizedSourceStage4
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
    ((CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))).comp
        (finiteFreeRowStableZeroComparison R).hom))

private abbrev normalizedSourceStage5
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
    ((CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S))).comp
        ((finiteFreeRowStableZeroComparison S).hom.comp (ordinaryBGLScalarMap f))))

private abbrev normalizedSourceStage6
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
    ((finiteFreeRowProjectiveZeroHomotopyEquiv.{uS, uMS} S).toFun.comp
      ((finiteFreeRowStableZeroComparison S).hom.comp (ordinaryBGLScalarMap f)))

private abbrev normalizedSourceStage7
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
    ((finiteFreeRowProjectiveZeroHomotopyEquiv.{uS, uMS} S).toFun.comp
      ((finiteFreeRowBasedZeroComparison S).hom.comp (ordinaryBGLScalarMap f)))

private abbrev normalizedSourceStage8
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  (normalizedOriginalNorm.{uS, uMS, uNS} S).sourceMap.comp (ordinaryBGLScalarMap f)

private def normalizedSourceFamily0
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedSourceStage1.{uR, uS, uMR, uMS, uNR, uNS} f) :=
  (nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f).symm.compContinuousMap
    (normalizedOriginalNorm.{uR, uMR, uNR} R).sourceMap

private def normalizedSourceFamily1
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedSourceStage1.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedSourceStage2.{uR, uS, uMR, uMS, uNS} f) := by
  let raw := nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let k := raw.comp (normalizedNativeChart.{uR, uMR, uNR} R).inv.hom
  let H := (ContinuousMap.Homotopy.refl k).comp
    ((normalizedOriginalModelTrace.{uR, uMR, uNR} R).symm.compContinuousMap
      (finiteFreeRowBasedZeroComparison R).hom)
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    exact congrArg raw
      (congrArg (fun a => a x) (normalizedOriginalNorm.{uR, uMR, uNR} R).sourceFormula).symm
  · apply ContinuousMap.ext
    intro x
    exact congrArg
      (fun a => a ((finiteFreeRowProjectiveZeroHomotopyEquiv.{uR, uMR} R).toFun
        (finiteFreeRowBasedZeroComparison R x)))
      (normalizedRawScalarPreSourceChart.{uR, uS, uMR, uMS, uNR, uNS} f)

private def normalizedSourceFamily2
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedSourceStage2.{uR, uS, uMR, uMS, uNS} f)
      (normalizedSourceStage3.{uR, uS, uMS, uNS} f) := by
  let GM := (finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor
  let GF := nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f
  let GQ := SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)
  let GU := SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S)
  let k := (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom
  let H := (ContinuousMap.Homotopy.refl k).comp
    ((CategoryTheory.realizedNerveFunctorMapHomotopy (normalizedActualSourceZeroIso.{uR, uS, uMR,
      uMS}
        f).hom).compContinuousMap (finiteFreeRowBasedZeroComparison R).hom)
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    let z := finiteFreeRowBasedZeroComparison R x
    have hComp := congrArg (fun a => a z) (normalizedMixedFunctorComposition GM GF)
    have hModel := congrArg (fun a => a z) (normalizedOriginalModelForwardMap.{uR, uMR} R)
    exact congrArg k (hComp.trans
      (congrArg (CategoryTheory.realizedNerveFunctorMap GF) hModel.symm))
  · apply ContinuousMap.ext
    intro x
    exact congrArg k (congrArg (fun a => a (finiteFreeRowBasedZeroComparison R x))
      (normalizedMixedFunctorComposition GQ GU))

private def normalizedSourceFamily3
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedSourceStage3.{uR, uS, uMS, uNS} f)
      (normalizedSourceStage4.{uR, uS, uMS, uNS} f) :=
  (ContinuousMap.Homotopy.refl
    ((normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp
        (CategoryTheory.realizedNerveFunctorMap
          (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)))))).comp
    (finiteFreeRowBasedZeroComparisonHomotopy R).symm

private def normalizedSourceFamily4
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedSourceStage4.{uR, uS, uMS, uNS} f)
      (normalizedSourceStage5.{uR, uS, uMS, uNS} f) :=
  (ContinuousMap.Homotopy.refl
    ((normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))))).comp
    (ordinaryBGLScalarOriginalStableRowHomotopy f)

private def normalizedSourceFamily5
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedSourceStage5.{uR, uS, uMS, uNS} f)
      (normalizedSourceStage6.{uR, uS, uMS, uNS} f) := by
  let GP := SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S)
  let GU := SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S)
  let GM := (finiteFreeRowProjectiveUniverseZeroEquivalence.{uS, uMS} S).functor
  let k := (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom
  let pre := (finiteFreeRowStableZeroComparison S).hom.comp (ordinaryBGLScalarMap f)
  let H := (ContinuousMap.Homotopy.refl k).comp
    ((CategoryTheory.realizedNerveFunctorMapHomotopy
      (normalizedActualTargetZeroIso.{uR, uS, uMS} S).hom).compContinuousMap pre)
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    exact congrArg k (congrArg (fun a => a (pre x)) (normalizedMixedFunctorComposition GP GU))
  · apply ContinuousMap.ext
    intro x
    exact congrArg k (congrArg (fun a => a (pre x))
      (normalizedOriginalModelForwardMap.{uS, uMS} S)).symm

private def normalizedSourceFamily6
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedSourceStage6.{uR, uS, uMS, uNS} f)
      (normalizedSourceStage7.{uR, uS, uMS, uNS} f) :=
  (ContinuousMap.Homotopy.refl
    ((normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
      (finiteFreeRowProjectiveZeroHomotopyEquiv.{uS, uMS} S).toFun)).comp
    ((finiteFreeRowBasedZeroComparisonHomotopy S).compContinuousMap (ordinaryBGLScalarMap f))

private def normalizedSourceFamily7
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedSourceStage7.{uR, uS, uMS, uNS} f)
      (normalizedSourceStage8.{uR, uS, uMS, uNS} f) := by
  let k := (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom
  let pre := (finiteFreeRowBasedZeroComparison S).hom.comp (ordinaryBGLScalarMap f)
  let H := (ContinuousMap.Homotopy.refl k).comp
    ((normalizedOriginalModelTrace.{uS, uMS, uNS} S).compContinuousMap pre)
  refine H.cast (by rfl) ?_
  apply ContinuousMap.ext
  intro x
  exact (congrArg (fun a => a (ordinaryBGLScalarMap f x))
    (normalizedOriginalNorm.{uS, uMS, uNS} S).sourceFormula).symm

private def normalizedSourceEightPaste
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedSourceStage8.{uR, uS, uMS, uNS} f) :=
  (normalizedSourceFamily0.{uR, uS, uMR, uMS, uNR, uNS} f).trans
    ((normalizedSourceFamily1.{uR, uS, uMR, uMS, uNR, uNS} f).trans
      ((normalizedSourceFamily2.{uR, uS, uMR, uMS, uNS} f).trans
        ((normalizedSourceFamily3.{uR, uS, uMS, uNS} f).trans
          ((normalizedSourceFamily4.{uR, uS, uMS, uNS} f).trans
            ((normalizedSourceFamily5.{uR, uS, uMS, uNS} f).trans
              ((normalizedSourceFamily6.{uR, uS, uMS, uNS} f).trans (normalizedSourceFamily7.{uR,
                uS, uMS, uNS} f)))))))

/-- The actual eight-part original whole homotopy between the exact six-role
normalized source maps. Its relative root retuning is constructed below. -/
public def nativeProjectiveZeroScalarNormalizedSourceHomotopy
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      ((nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
        (nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R).sourceMap)
      ((nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S).sourceMap.comp
        (ordinaryBGLScalarMap f)) :=
  normalizedSourceEightPaste.{uR, uS, uMR, uMS, uNR, uNS} f

/-- The complete SAME original eight-part continuous family, retaining every
original model/row/intrinsic/scalar family and choice in the displayed paste. -/
public def nativeProjectiveZeroScalarNormalizedSourceFamily
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(unitInterval × ordinaryBGL R, RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  (nativeProjectiveZeroScalarNormalizedSourceHomotopy.{uR, uS, uMR, uMS, uNR, uNS}
      f).toContinuousMap

private theorem normalizedSourceEightFamilyValue
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarNormalizedSourceHomotopy.{uR, uS, uMR, uMS, uNR, uNS}
        f).toContinuousMap =
      nativeProjectiveZeroScalarNormalizedSourceFamily.{uR, uS, uMR, uMS, uNR, uNS} f := by
  rfl

/-- The entire original eight-part homotopy keeps its SAME continuous-family value. -/
public theorem nativeProjectiveZeroScalarNormalizedSourceHomotopy_toContinuousMap
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarNormalizedSourceHomotopy.{uR, uS, uMR, uMS, uNR, uNS}
        f).toContinuousMap =
      nativeProjectiveZeroScalarNormalizedSourceFamily.{uR, uS, uMR, uMS, uNR, uNS} f :=
  normalizedSourceEightFamilyValue f

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped ContinuousMap Simplicial TopCat.modelCategory

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uX uY uC vC uD vD uE vE

namespace AlgebraicKTheory.StableGL

section WeakZeroFunctor

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E]

private def normalizedZeroWeakMap
    (F : C ⥤ D) [F.Additive]
    (G : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (A : NormalizedZeroLiftData F G) :
    ContinuousMap.WeaklyPointed
      (normalizedObjectVertex (SInverseS.ZeroComponent (C := C))
        (SInverseS.zeroComponentBaseObject (C := C)))
      (normalizedObjectVertex (SInverseS.ZeroComponent (C := D))
        (SInverseS.zeroComponentBaseObject (C := D))) where
  hom := CategoryTheory.realizedNerveFunctorMap G
  rootPath := (normalizedEdgePath A.root.hom).cast
    (CategoryTheory.realizedNerveFunctorMap_vertex G
      (SInverseS.zeroComponentBaseObject (C := C))) rfl

private theorem normalizedZeroWeakCompositeMap
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive]
    (G : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (K : SInverseS.ZeroComponent (C := D) ⥤ SInverseS.ZeroComponent (C := E))
    (A : NormalizedZeroLiftData F G) (B : NormalizedZeroLiftData H K) :
    (normalizedZeroWeakMap (F ⋙ H) (G ⋙ K)
      (normalizedZeroLiftComposite F H G K A B)).hom =
      ((normalizedZeroWeakMap F G A).comp (normalizedZeroWeakMap H K B)).hom :=
  normalizedMixedFunctorComposition G K

private theorem normalizedZeroWeakCompositeRoot
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive]
    (G : SInverseS.ZeroComponent (C := C) ⥤ SInverseS.ZeroComponent (C := D))
    (K : SInverseS.ZeroComponent (C := D) ⥤ SInverseS.ZeroComponent (C := E))
    (A : NormalizedZeroLiftData F G) (B : NormalizedZeroLiftData H K) :
    (normalizedZeroWeakMap (F ⋙ H) (G ⋙ K)
      (normalizedZeroLiftComposite F H G K A B)).rootPath.Homotopic
      ((((normalizedZeroWeakMap F G A).comp (normalizedZeroWeakMap H K B)).rootPath).cast
        (congrArg (fun k => k (normalizedObjectVertex (SInverseS.ZeroComponent (C := C))
          (SInverseS.zeroComponentBaseObject (C := C))))
          (normalizedZeroWeakCompositeMap F H G K A B)) rfl) := by
  let zC := SInverseS.zeroComponentBaseObject (C := C)
  let zD := SInverseS.zeroComponentBaseObject (C := D)
  let zE := SInverseS.zeroComponentBaseObject (C := E)
  let WM := normalizedZeroWeakMap F G A
  let WN := normalizedZeroWeakMap H K B
  let MK := CategoryTheory.realizedNerveFunctorMap K
  let hs := CategoryTheory.realizedNerveFunctorMap_vertex (G ⋙ K) zC
  let ht := CategoryTheory.realizedNerveFunctorMap_vertex K zD
  let hMap := congrArg (fun k => k (normalizedObjectVertex (SInverseS.ZeroComponent (C := C)) zC))
    (normalizedZeroWeakCompositeMap F H G K A B)
  have hEdge := (CategoryTheory.realizedNerveFunctorMap_edge_homotopic K A.root.hom).pathCast hs ht
  have hFirst :
      ((((normalizedEdgePath A.root.hom).map MK.continuous).cast
        (CategoryTheory.realizedNerveFunctorMap_vertex K (G.obj zC)).symm ht.symm).cast hs ht) =
        ((WM.rootPath.map MK.continuous).cast hMap rfl) := by
    apply Path.ext
    funext t
    rfl
  have hEdgeValue : ((WM.rootPath.map MK.continuous).cast hMap rfl).Homotopic
      ((normalizedEdgePath (K.mapIso A.root).hom).cast hs ht) :=
    (normalizedRootPathHomotopicOfEq hFirst.symm).trans hEdge
  have h := hEdgeValue.hcomp (Path.Homotopic.refl WN.rootPath)
  have hTarget :
      ((normalizedEdgePath (K.mapIso A.root).hom).cast hs ht).trans WN.rootPath =
      ((normalizedEdgePath (K.mapIso A.root).hom).trans
        (normalizedEdgePath B.root.hom)).cast hs rfl := by
    apply Path.ext
    funext t
    rfl
  have hValue := h.trans (normalizedRootPathHomotopicOfEq hTarget)
  have hTri := (normalizedEdgeIsoTriangle (K.mapIso A.root)
    (normalizedZeroLiftComposite F H G K A B).root B.root (by rfl)).pathCast hs rfl
  have hLeft :
      (((WM.comp WN).rootPath).cast hMap rfl) =
        ((WM.rootPath.map MK.continuous).cast hMap rfl).trans WN.rootPath := by
    apply Path.ext
    funext t
    rfl
  exact hTri.trans ((normalizedRootPathHomotopicOfEq hLeft).trans hValue).symm

end WeakZeroFunctor

private def normalizedRootedReplaceHomotopy
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {x : X} {y : Y} {f g : C(X, Y)} {p : Path (f x) y} {q : Path (g x) y}
    (R : NormalizedRootedFamily x y f g p q) (H : ContinuousMap.Homotopy f g)
    (h : R.homotopy.toContinuousMap = H.toContinuousMap) :
    NormalizedRootedFamily x y f g p q where
  homotopy := H
  root := by
    have hPath : R.homotopy.evalAt x = H.evalAt x := by
      apply Path.ext
      funext t
      exact congrArg (fun k : C(unitInterval × X, Y) => k (t, x)) h
    exact R.root.trans (normalizedRootPathHomotopicOfEq
      (congrArg (fun a : Path (f x) (g x) => a.trans q) hPath))

private theorem normalizedRootedNullTrace
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {x : X} {y : Y} {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
    (R : NormalizedRootedFamily x y f g
      ((Path.refl y).cast hf rfl) ((Path.refl y).cast hg rfl)) :
    ((R.homotopy.evalAt x).cast hf.symm hg.symm).Homotopic (Path.refl y) := by
  have h := R.root.pathCast hf.symm rfl
  rw [Path.cast_trans (R.homotopy.evalAt x) ((Path.refl y).cast hg rfl)
    hf.symm hg.symm rfl] at h
  have hLeft : (((Path.refl y).cast hf rfl).cast hf.symm rfl) = Path.refl y := by
    apply Path.ext
    funext t
    rfl
  have hRight : (((Path.refl y).cast hg rfl).cast hg.symm rfl) = Path.refl y := by
    apply Path.ext
    funext t
    rfl
  rw [hLeft, hRight] at h
  exact (Path.Homotopic.trans_refl ((R.homotopy.evalAt x).cast hf.symm hg.symm)).symm.trans h.symm

private theorem normalizedRootedRelativeSameUniverse
    {X Y : TopCat.{uE}} (f g : C(X, Y)) (x : X) (y : Y)
    [Cofibration (TopCat.const x : TopCat.of PUnit.{uE + 1} ⟶ X)]
    (hf : f x = y) (hg : g x = y)
    (R : NormalizedRootedFamily x y f g
      ((Path.refl y).cast hf rfl) ((Path.refl y).cast hg rfl)) :
    Nonempty (ContinuousMap.HomotopyRel f g {x}) :=
  TopCat.exists_pointRelativeHomotopy_of_null_trace (TopCat.ofHom f) (TopCat.ofHom g) x y
    hf hg R.homotopy (normalizedRootedNullTrace hf hg R).some

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial unitInterval

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uR uS uMR uMS uNR uNS

namespace AlgebraicKTheory.StableGL

private theorem normalizedSourceStartPoint
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f (ordinaryBGLBasepoint R) =
      RingK0.projectiveZeroPoint.{uS, uMS, uNS} S :=
  (congrArg (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
    (normalizedOriginalNorm.{uR, uMR, uNR} R).sourcePoint).trans
      (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f)

private theorem normalizedSourceEndPoint
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedSourceStage8.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R) =
      RingK0.projectiveZeroPoint.{uS, uMS, uNS} S :=
  (congrArg (normalizedOriginalNorm.{uS, uMS, uNS} S).sourceMap
    (ordinaryBGLScalarMap_point f)).trans
      (normalizedOriginalNorm.{uS, uMS, uNS} S).sourcePoint

private def normalizedSourceRoot0
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  (Path.refl (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)).cast
    (normalizedSourceStartPoint.{uR, uS, uMR, uMS, uNR, uNS} f) rfl

private def normalizedSourceRoot1
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage1.{uR, uS, uMR, uMS, uNR, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  (nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f).cast
    (congrArg (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedOriginalNorm.{uR, uMR, uNR} R).sourcePoint) rfl

private def normalizedSourceRoot2
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage2.{uR, uS, uMR, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  ((normalizedSourceFamily1.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt (ordinaryBGLBasepoint
    R)).symm.trans
    (normalizedSourceRoot1.{uR, uS, uMR, uMS, uNR, uNS} f)

private def normalizedLegacyCoefficientRoot
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)))
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max uS uR} S)) :=
  (normalizedEdgePath (normalizedCanonicalZeroLift (normalizedLegacySourceModule f)).root.hom).cast
    ((congrArg (CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)))
      (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
        (C := FGProjectiveCat.IdempotentModel R))).trans
      (CategoryTheory.realizedNerveFunctorMap_vertex
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))))
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max uS uR} S))

private def normalizedResizeRoot.{uSourceCarrier, uTargetRing, uTargetCarrier}
    (S : Type uTargetRing) [Ring S] :
    Path (CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor
        (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S))
      (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.{max uTargetRing uSourceCarrier} S)))
      (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.{max uTargetRing uTargetCarrier} S)) :=
  (normalizedEdgePath (normalizedCanonicalZeroLift
    (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).root.hom).cast
    ((congrArg (CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor
        (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)))
      (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
        (C := FGProjectiveCat.{max uTargetRing uSourceCarrier} S))).trans
      (CategoryTheory.realizedNerveFunctorMap_vertex
        (SInverseS.zeroComponentFunctor
          (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S))
        (SInverseS.zeroComponentBaseObject
          (C := FGProjectiveCat.{max uTargetRing uSourceCarrier} S))))
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max uTargetRing uTargetCarrier} S))

private def normalizedLegacyTotalCoefficientRoot
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path ((normalizedNativeChart.{uS, uMS, uNS} S).inv
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))
        (CategoryTheory.realizedNerveFunctorMap
          (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
          (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel
              R)))))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  (((normalizedLegacyCoefficientRoot f).map
    (CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).continuous).trans
      (normalizedResizeRoot.{uR, uS, uMS} S)).map
        (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous |>.cast rfl
          (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm

private def normalizedSourceRoot3
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage3.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  (normalizedLegacyTotalCoefficientRoot f).cast
    (congrArg (fun x => (normalizedNativeChart.{uS, uMS, uNS} S).inv
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))
        (CategoryTheory.realizedNerveFunctorMap
          (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)) x)))
      (finiteFreeRowBasedZeroComparison_basepoint R)) rfl

private def normalizedSourceRoot4
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage4.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  ((((normalizedBGLScalarSourceRoot f).map
    (CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).continuous).trans
      (normalizedResizeRoot.{uR, uS, uMS} S)).map
        (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous).cast rfl
          (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm

private def normalizedSourceRoot5
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage5.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  ((((normalizedBGLScalarTargetRoot f).map
    (CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).continuous).trans
      (normalizedResizeRoot.{uR, uS, uMS} S)).map
        (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous).cast rfl
          (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm

private theorem normalizedSourceStage7ModelPoint
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedSourceStage7.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R) =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv
        ((finiteFreeRowProjectiveZeroHomotopyEquiv.{uS, uMS} S).toFun
          (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel S)))
              := by
  change (normalizedNativeChart.{uS, uMS, uNS} S).inv
    ((finiteFreeRowProjectiveZeroHomotopyEquiv.{uS, uMS} S).toFun
      (finiteFreeRowBasedZeroComparison S (ordinaryBGLScalarMap f (ordinaryBGLBasepoint R)))) = _
  rw [ordinaryBGLScalarMap_point, finiteFreeRowBasedZeroComparison_basepoint]

private def normalizedSourceRoot7
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage7.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  ((finiteFreeRowProjectiveZeroUnitPath.{uS, uMS} S).map
    (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous).cast
      (normalizedSourceStage7ModelPoint.{uR, uS, uMS, uNS} f)
      (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm

private def normalizedSourceRoot6
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage6.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  ((normalizedSourceFamily6.{uR, uS, uMS, uNS} f).evalAt (ordinaryBGLBasepoint R)).trans
    (normalizedSourceRoot7.{uR, uS, uMS, uNS} f)

private def normalizedSourceRoot8
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage8.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  (Path.refl (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)).cast (normalizedSourceEndPoint.{uR,
    uS, uMS, uNS} f) rfl

private def normalizedConcreteRooted0
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f) (normalizedSourceStage1.{uR, uS,
        uMR, uMS, uNR, uNS} f)
      (normalizedSourceRoot0.{uR, uS, uMR, uMS, uNR, uNS} f) (normalizedSourceRoot1.{uR, uS, uMR,
        uMS, uNR, uNS} f) where
  homotopy := normalizedSourceFamily0.{uR, uS, uMR, uMS, uNR, uNS} f
  root := by
    let x := ordinaryBGLBasepoint R
    let hStart := normalizedSourceStartPoint.{uR, uS, uMR, uMS, uNR, uNS} f
    have hEval : (normalizedSourceFamily0.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt x =
        (normalizedSourceRoot1.{uR, uS, uMR, uMS, uNR, uNS} f).symm.cast hStart rfl := by
      apply Path.ext
      funext t
      change nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f
        (σ t, (normalizedOriginalNorm.{uR, uMR, uNR} R).sourceMap x) =
        nativeProjectiveZeroScalarRawRootPath.{uR, uS, uMR, uMS, uNR, uNS} f (σ t)
      rw [(normalizedOriginalNorm.{uR, uMR, uNR} R).sourcePoint]
      exact normalizedIntrinsicRetuningRootClock f (σ t)
    have h := (Path.Homotopic.symm_trans (normalizedSourceRoot1.{uR, uS, uMR, uMS, uNR, uNS}
      f)).pathCast hStart rfl
    rw [Path.cast_trans (normalizedSourceRoot1.{uR, uS, uMR, uMS, uNR, uNS} f).symm
      (normalizedSourceRoot1.{uR, uS, uMR, uMS, uNR, uNS} f)
      hStart rfl rfl, ← hEval] at h
    exact h.symm

private def normalizedConcreteRooted1
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (normalizedSourceStage1.{uR, uS, uMR, uMS, uNR, uNS} f) (normalizedSourceStage2.{uR, uS,
        uMR, uMS, uNS} f)
      (normalizedSourceRoot1.{uR, uS, uMR, uMS, uNR, uNS} f) (normalizedSourceRoot2.{uR, uS, uMR,
        uMS, uNR, uNS} f) where
  homotopy := normalizedSourceFamily1.{uR, uS, uMR, uMS, uNR, uNS} f
  root := by
    let a := (normalizedSourceFamily1.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt (ordinaryBGLBasepoint
      R)
    let p := normalizedSourceRoot1.{uR, uS, uMR, uMS, uNR, uNS} f
    have h := ((Path.Homotopic.trans_symm a).hcomp (Path.Homotopic.refl p)).trans
      (Path.Homotopic.refl_trans p)
    exact ((Path.Homotopic.trans_assoc a a.symm p).symm.trans h).symm

private def normalizedConcreteRooted4
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (normalizedSourceStage4.{uR, uS, uMS, uNS} f) (normalizedSourceStage5.{uR, uS, uMS, uNS} f)
      (normalizedSourceRoot4.{uR, uS, uMS, uNS} f) (normalizedSourceRoot5.{uR, uS, uMS, uNS} f) :=
        by
  let H := normalizedRootedPostBased
    (normalizedRootedPostWeak (normalizedOriginalBGLScalarRooted f)
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S)))
      (normalizedResizeRoot.{uR, uS, uMS} S))
    (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom
    (normalizedNativeChartInvPoint.{uS, uMS, uNS} S)
  refine normalizedRootedReplaceHomotopy H (normalizedSourceFamily4.{uR, uS, uMS, uNS} f) ?_
  apply ContinuousMap.ext
  intro z
  rfl

private def normalizedConcreteRooted6
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (normalizedSourceStage6.{uR, uS, uMS, uNS} f) (normalizedSourceStage7.{uR, uS, uMS, uNS} f)
      (normalizedSourceRoot6.{uR, uS, uMS, uNS} f) (normalizedSourceRoot7.{uR, uS, uMS, uNS} f)
        where
  homotopy := normalizedSourceFamily6.{uR, uS, uMS, uNS} f
  root := Path.Homotopic.refl _

private theorem normalizedConcreteModelTrace7
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    normalizedSourceFamily7.{uR, uS, uMS, uNS} f (t, ordinaryBGLBasepoint R) =
      normalizedSourceRoot7.{uR, uS, uMS, uNS} f t := by
  change (normalizedNativeChart.{uS, uMS, uNS} S).inv
    (normalizedOriginalModelTrace.{uS, uMS, uNS} S
      (t, finiteFreeRowBasedZeroComparison S (ordinaryBGLScalarMap f (ordinaryBGLBasepoint R)))) =
    (normalizedNativeChart.{uS, uMS, uNS} S).inv
      (finiteFreeRowProjectiveZeroUnitPath.{uS, uMS} S t)
  rw [ordinaryBGLScalarMap_point, finiteFreeRowBasedZeroComparison_basepoint]
  exact congrArg (normalizedNativeChart.{uS, uMS, uNS} S).inv
    (normalizedOriginalModelTraceRoot.{uS, uMS, uNS} S t)

private def normalizedConcreteRooted7
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (normalizedSourceStage7.{uR, uS, uMS, uNS} f) (normalizedSourceStage8.{uR, uS, uMS, uNS} f)
      (normalizedSourceRoot7.{uR, uS, uMS, uNS} f) (normalizedSourceRoot8.{uR, uS, uMS, uNS} f) :=
  normalizedRootedFromTrace (normalizedSourceFamily7.{uR, uS, uMS, uNS} f)
    (normalizedSourceEndPoint.{uR, uS, uMS, uNS} f)
    (normalizedSourceRoot7.{uR, uS, uMS, uNS} f) (normalizedConcreteModelTrace7.{uR, uS, uMS, uNS}
      f)

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uC vC uR uS uMS uNS

namespace AlgebraicKTheory.StableGL

private theorem normalizedEdgeObjectTransport
    {C : Type uC} [Category.{vC} C] {W X Y : C} (h : W = X) (a : X ≅ Y) :
    normalizedEdgePath (eqToIso h ≪≫ a).hom =
      (normalizedEdgePath a.hom).cast (congrArg (normalizedObjectVertex C) h) rfl := by
  cases h
  simp only [eqToIso_refl, Iso.refl_trans, Path.cast_rfl_rfl]

private theorem normalizedLegacySourceRowVertex
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
        (finiteFreeRowStableZeroComparison R (ordinaryBGLBasepoint R)) =
      normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S))
        ((SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)).obj
          (normalizedRowZeroObject R)) :=
  (congrArg (CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)))
    (finiteFreeRowStableZeroComparison_basepoint R)).trans
    (CategoryTheory.realizedNerveFunctorMap_vertex
      (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)) (normalizedRowZeroObject R))

private theorem normalizedLegacySourceZeroVertex
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
        (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)) =
      normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S))
        ((SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)).obj
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))) :=
  (congrArg (CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)))
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.IdempotentModel R))).trans
    (CategoryTheory.realizedNerveFunctorMap_vertex
      (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
      (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)))

private theorem normalizedLegacyGammaSourceRowEdge
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedBGLScalarSourceRoot f =
      (normalizedEdgePath (normalizedRowFunctorRoot R
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
        (normalizedCanonicalZeroLift (normalizedLegacySourceModule f)).root).hom).cast
        (normalizedLegacySourceRowVertex f)
        (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
          (C := FGProjectiveCat.{max uS uR} S)) := by
  unfold normalizedBGLScalarSourceRoot
  rw [normalizedOriginalGammaSourceUnitIso, normalizedEdgeObjectTransport]
  apply Path.ext
  funext t
  rfl

private theorem normalizedLegacyGammaSourcePath
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (((finiteFreeRowStableZeroComparisonUnitPath R).map
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))).continuous).trans
      (normalizedLegacyCoefficientRoot f)).Homotopic (normalizedBGLScalarSourceRoot f) := by
  let GQ := SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)
  let FM := CategoryTheory.realizedNerveFunctorMap GQ
  let q := (normalizedCanonicalZeroLift (normalizedLegacySourceModule f)).root
  let hs := normalizedLegacySourceRowVertex f
  let ht := normalizedLegacySourceZeroVertex f
  let hz := SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
    (C := FGProjectiveCat.{max uS uR} S)
  have hMap := (CategoryTheory.realizedNerveFunctorMap_edge_homotopic GQ
    (normalizedRowZeroIso R).hom).pathCast hs ht
  have hLeft :
      ((((normalizedEdgePath (normalizedRowZeroIso R).hom).map FM.continuous).cast
        (CategoryTheory.realizedNerveFunctorMap_vertex GQ (normalizedRowZeroObject R)).symm
        (CategoryTheory.realizedNerveFunctorMap_vertex GQ
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))).symm).cast
          hs ht) = (finiteFreeRowStableZeroComparisonUnitPath R).map FM.continuous := by
    rw [normalizedOriginalRowUnitEdge]
    apply Path.ext
    funext t
    rfl
  have hMapValue := (normalizedRootPathHomotopicOfEq hLeft.symm).trans hMap
  have h := hMapValue.hcomp (Path.Homotopic.refl (normalizedLegacyCoefficientRoot f))
  have hTarget :
      ((normalizedEdgePath (GQ.mapIso (normalizedRowZeroIso R)).hom).cast hs ht).trans
        (normalizedLegacyCoefficientRoot f) =
      ((normalizedEdgePath (GQ.mapIso (normalizedRowZeroIso R)).hom).trans
        (normalizedEdgePath q.hom)).cast hs hz := by
    apply Path.ext
    funext t
    rfl
  have hValue := h.trans (normalizedRootPathHomotopicOfEq hTarget)
  have hTri := (normalizedEdgeIsoTriangle (GQ.mapIso (normalizedRowZeroIso R))
    (normalizedRowFunctorRoot R GQ q) q (by rfl)).pathCast hs hz
  exact (hValue.trans hTri.symm).trans
    (normalizedRootPathHomotopicOfEq (normalizedLegacyGammaSourceRowEdge f).symm)

private theorem normalizedConcreteRootBridge3Source
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (normalizedSourceRoot3.{uR, uS, uMS, uNS} f).Homotopic
      (((((Path.refl (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.IdempotentModel R))).cast
        (finiteFreeRowBasedZeroComparison_basepoint R) rfl).map
        ((normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
          ((CategoryTheory.realizedNerveFunctorMap
            (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp
            (CategoryTheory.realizedNerveFunctorMap
              (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))))).continuous).trans
              (normalizedLegacyTotalCoefficientRoot f))) := by
  let z := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
  let k := (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
    ((CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))))
  let p := normalizedLegacyTotalCoefficientRoot f
  let hs := congrArg k (finiteFreeRowBasedZeroComparison_basepoint R)
  have h := (Path.Homotopic.refl_trans p).pathCast hs rfl
  have hConstTrans :
      ((((Path.refl z).cast (finiteFreeRowBasedZeroComparison_basepoint R) rfl).map
        k.continuous).trans p) = ((Path.refl (k z)).trans p).cast hs rfl := by
    apply Path.ext
    funext t
    rfl
  exact ((normalizedRootPathHomotopicOfEq hConstTrans).trans h).symm

private theorem normalizedConcreteRootBridge3Target
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ((((finiteFreeRowStableZeroComparisonUnitPath R).map
      ((normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
        ((CategoryTheory.realizedNerveFunctorMap
          (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp
          (CategoryTheory.realizedNerveFunctorMap
            (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))))).continuous).trans
              (normalizedLegacyTotalCoefficientRoot f))).Homotopic (normalizedSourceRoot4.{uR, uS,
                uMS, uNS} f) := by
  let MQ := CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
  let MU := CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))
  let nativeS := normalizedNativeChart.{uS, uMS, uNS} S
  let a := ((finiteFreeRowStableZeroComparisonUnitPath R).map MQ.continuous).map MU.continuous
  let b := (normalizedLegacyCoefficientRoot f).map MU.continuous
  let c := normalizedResizeRoot.{uR, uS, uMS} S
  have hGamma := (normalizedLegacyGammaSourcePath f).map MU
  rw [Path.map_trans] at hGamma
  have hOrd := (Path.Homotopic.trans_assoc a b c).symm.trans
    (hGamma.hcomp (Path.Homotopic.refl c))
  have h := (hOrd.map nativeS.inv.hom).pathCast rfl
    (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm
  have hLeft :
      (((a.trans (b.trans c)).map nativeS.inv.hom.continuous).cast rfl
        (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm) =
      (((finiteFreeRowStableZeroComparisonUnitPath R).map
        (nativeS.inv.hom.comp (MU.comp MQ)).continuous).trans
        (normalizedLegacyTotalCoefficientRoot f)) := by
    apply Path.ext
    funext t
    exact congrArg (fun q => q t)
      (Path.map_trans a (b.trans c) nativeS.inv.hom.continuous)
  exact (normalizedRootPathHomotopicOfEq hLeft.symm).trans h

private def normalizedConcreteRooted3
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (normalizedSourceStage3.{uR, uS, uMS, uNS} f) (normalizedSourceStage4.{uR, uS, uMS, uNS} f)
      (normalizedSourceRoot3.{uR, uS, uMS, uNS} f) (normalizedSourceRoot4.{uR, uS, uMS, uNS} f) :=
        by
  let k := (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
    ((CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))))
  let H := normalizedRootedSymm
    (normalizedRootedPostWeak (normalizedOriginalRowRooted R) k
      (normalizedLegacyTotalCoefficientRoot f))
  let H' := normalizedRootedChangePaths H
    (normalizedConcreteRootBridge3Source.{uR, uS, uMS, uNS} f)
      (normalizedConcreteRootBridge3Target.{uR, uS, uMS, uNS} f)
  refine normalizedRootedReplaceHomotopy H' (normalizedSourceFamily3.{uR, uS, uMS, uNS} f) ?_
  apply ContinuousMap.ext
  intro z
  rfl

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uR uS uMS uNS

namespace AlgebraicKTheory.StableGL

private theorem normalizedLegacyTargetRowVertex
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S))
        (finiteFreeRowStableZeroComparison S (ordinaryBGLScalarMap f (ordinaryBGLBasepoint R))) =
      normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S))
        ((SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S)).obj
          (normalizedRowZeroObject S)) :=
  ((congrArg (fun x => CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S))
    (finiteFreeRowStableZeroComparison S x)) (ordinaryBGLScalarMap_point f)).trans
    (congrArg (CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S)))
      (finiteFreeRowStableZeroComparison_basepoint S))).trans
      (CategoryTheory.realizedNerveFunctorMap_vertex
        (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S))
        (normalizedRowZeroObject S))

private theorem normalizedResizeZeroVertex.{uSourceCarrier, uTargetRing, uTargetCarrier}
    (S : Type uTargetRing) [Ring S] :
    CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor
          (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S))
        (SInverseS.ComponentTranslation.zeroSpacePoint
          (C := FGProjectiveCat.{max uTargetRing uSourceCarrier} S)) =
      normalizedObjectVertex
        (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uTargetRing uTargetCarrier} S))
        ((SInverseS.zeroComponentFunctor
          (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).obj
          (SInverseS.zeroComponentBaseObject
            (C := FGProjectiveCat.{max uTargetRing uSourceCarrier} S))) :=
  (congrArg (CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor
      (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)))
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max uTargetRing uSourceCarrier} S))).trans
      (CategoryTheory.realizedNerveFunctorMap_vertex
        (SInverseS.zeroComponentFunctor
          (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S))
        (SInverseS.zeroComponentBaseObject
          (C := FGProjectiveCat.{max uTargetRing uSourceCarrier} S)))

private theorem normalizedLegacyGammaTargetRowEdge
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedBGLScalarTargetRoot f =
      (normalizedEdgePath (normalizedRowFunctorRoot S
        (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S))
        (normalizedCanonicalZeroLift (normalizedLegacyTargetModule.{uR, uS} S)).root).hom).cast
        (normalizedLegacyTargetRowVertex f)
        (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
          (C := FGProjectiveCat.{max uS uR} S)) := by
  unfold normalizedBGLScalarTargetRoot
  rw [normalizedOriginalGammaTargetUnitIso, normalizedEdgeObjectTransport]
  apply Path.ext
  funext t
  rfl

private abbrev normalizedTargetRowLeftRoot.{uSourceCarrier, uTargetRing, uTargetCarrier}
    (S : Type uTargetRing) [Ring S] :=
  normalizedRowFunctorRoot S
    (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S) ⋙
      SInverseS.zeroComponentFunctor
        (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S))
    ((SInverseS.zeroComponentFunctor
      (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).mapIso
      (normalizedCanonicalZeroLift
        (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S)).root ≪≫
      (normalizedCanonicalZeroLift
        (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).root)

private theorem normalizedTargetRowLeftRootFactor.{uSourceCarrier, uTargetRing, uTargetCarrier}
    (S : Type uTargetRing) [Ring S] :
    normalizedTargetRowLeftRoot.{uSourceCarrier, uTargetRing, uTargetCarrier} S =
      (SInverseS.zeroComponentFunctor
        (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).mapIso
        (normalizedRowFunctorRoot S
          (SInverseS.zeroComponentFunctor
            (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S))
          (normalizedCanonicalZeroLift
            (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S)).root) ≪≫
          (normalizedCanonicalZeroLift
            (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).root := by
  let GP := SInverseS.zeroComponentFunctor
    (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S)
  let GU := SInverseS.zeroComponentFunctor
    (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)
  let p := GP.mapIso (normalizedRowZeroIso S)
  let q := (normalizedCanonicalZeroLift
    (normalizedLegacyTargetModule.{uSourceCarrier, uTargetRing} S)).root
  let r := (normalizedCanonicalZeroLift
    (normalizedModuleResize.{uSourceCarrier, uTargetRing, uTargetCarrier} S)).root
  change GU.mapIso p ≪≫ (GU.mapIso q ≪≫ r) = GU.mapIso (p ≪≫ q) ≪≫ r
  exact (Iso.trans_assoc (GU.mapIso p) (GU.mapIso q) r).symm.trans
    (congrArg (fun e => e ≪≫ r) (normalizedFunctorMapIsoTrans GU p q).symm)

private theorem normalizedSourceStage5Vertex
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedSourceStage5.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R) =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv
        (normalizedObjectVertex
          (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))
          (((SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S)) ⋙
            SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S)).obj
            (normalizedRowZeroObject S))) := by
  let MU := CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))
  exact (congrArg (fun x => (normalizedNativeChart.{uS, uMS, uNS} S).inv (MU x))
    (normalizedLegacyTargetRowVertex f)).trans
    (congrArg (normalizedNativeChart.{uS, uMS, uNS} S).inv
      (CategoryTheory.realizedNerveFunctorMap_vertex
        (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))
        ((SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S)).obj
          (normalizedRowZeroObject S))))

private def normalizedCanonicalRoot5
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage5.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  ((normalizedEdgePath (normalizedTargetRowLeftRoot.{uR, uS, uMS} S).hom).map
    (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous).cast
      (normalizedSourceStage5Vertex.{uR, uS, uMS, uNS} f)
        (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)

private theorem normalizedConcreteRootBridge5Source
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (normalizedSourceRoot5.{uR, uS, uMS, uNS} f).Homotopic (normalizedCanonicalRoot5.{uR, uS, uMS,
      uNS} f) := by
  let GP := SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S)
  let GU := SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S)
  let MU := CategoryTheory.realizedNerveFunctorMap GU
  let p := normalizedRowFunctorRoot S GP
    (normalizedCanonicalZeroLift (normalizedLegacyTargetModule.{uR, uS} S)).root
  let r := (normalizedCanonicalZeroLift (normalizedModuleResize.{uR, uS, uMS} S)).root
  let hs := (congrArg MU (normalizedLegacyTargetRowVertex f)).trans
    (CategoryTheory.realizedNerveFunctorMap_vertex GU (GP.obj (normalizedRowZeroObject S)))
  let ht := normalizedResizeZeroVertex.{uR, uS, uMS} S
  let hz := SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
    (C := FGProjectiveCat.{max uS uMS} S)
  have hMap := (CategoryTheory.realizedNerveFunctorMap_edge_homotopic GU p.hom).pathCast hs ht
  have hLeft :
      ((((normalizedEdgePath p.hom).map MU.continuous).cast
        (CategoryTheory.realizedNerveFunctorMap_vertex GU (GP.obj (normalizedRowZeroObject S))).symm
        (CategoryTheory.realizedNerveFunctorMap_vertex GU
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uR} S))).symm).cast
          hs ht) = (normalizedBGLScalarTargetRoot f).map MU.continuous := by
    rw [normalizedLegacyGammaTargetRowEdge]
    apply Path.ext
    funext t
    rfl
  have hMapValue := (normalizedRootPathHomotopicOfEq hLeft.symm).trans hMap
  have h := hMapValue.hcomp (Path.Homotopic.refl (normalizedResizeRoot.{uR, uS, uMS} S))
  have hTarget :
      ((normalizedEdgePath (GU.mapIso p).hom).cast hs ht).trans
        (normalizedResizeRoot.{uR, uS, uMS} S) =
      ((normalizedEdgePath (GU.mapIso p).hom).trans (normalizedEdgePath r.hom)).cast hs hz := by
    apply Path.ext
    funext t
    rfl
  have hValue := h.trans (normalizedRootPathHomotopicOfEq hTarget)
  have hTri := (normalizedEdgeIsoTriangle (GU.mapIso p)
    (normalizedTargetRowLeftRoot.{uR, uS, uMS} S) r
    (normalizedTargetRowLeftRootFactor.{uR, uS, uMS} S).symm).pathCast hs hz
  have hOrd := hValue.trans hTri.symm
  have hNative := (hOrd.map (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom).pathCast rfl
    (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm
  have hRight :
      (((normalizedEdgePath (normalizedTargetRowLeftRoot.{uR, uS, uMS} S).hom).cast hs hz).map
        (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous).cast rfl
          (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm =
        normalizedCanonicalRoot5.{uR, uS, uMS, uNS} f := by
    apply Path.ext
    funext t
    rfl
  exact hNative.trans (normalizedRootPathHomotopicOfEq hRight)

private theorem normalizedOriginalModelObjectVertex.{uModelRing, uModelCarrier}
    (R : Type uModelRing) [Ring R]
    (X : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)) :
    (finiteFreeRowProjectiveZeroHomotopyEquiv.{uModelRing, uModelCarrier} R).toFun
        (normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
            X) =
      normalizedObjectVertex
        (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uModelRing uModelCarrier} R))
        ((finiteFreeRowProjectiveUniverseZeroEquivalence.{uModelRing, uModelCarrier} R).functor.obj
            X) := by
  rw [finiteFreeRowProjectiveZeroHomotopyEquiv_value]
  exact CategoryTheory.realizedNerveEquivalence_vertex _ X

private theorem normalizedSourceStage6Vertex
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedSourceStage6.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R) =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv
        (normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uMS} S))
          ((finiteFreeRowProjectiveUniverseZeroEquivalence.{uS, uMS} S).functor.obj
            (normalizedRowZeroObject S))) := by
  have hPre : finiteFreeRowStableZeroComparison S (ordinaryBGLScalarMap f (ordinaryBGLBasepoint R))
      =
      normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel S))
        (normalizedRowZeroObject S) :=
    (congrArg (finiteFreeRowStableZeroComparison S).hom (ordinaryBGLScalarMap_point f)).trans
      (finiteFreeRowStableZeroComparison_basepoint S)
  exact (congrArg (fun x => (normalizedNativeChart.{uS, uMS, uNS} S).inv
    ((finiteFreeRowProjectiveZeroHomotopyEquiv.{uS, uMS} S).toFun x)) hPre).trans
    (congrArg (normalizedNativeChart.{uS, uMS, uNS} S).inv
      (normalizedOriginalModelObjectVertex.{uS, uMS} S (normalizedRowZeroObject S)))

private def normalizedCanonicalRoot6
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage6.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  ((normalizedEdgePath (normalizedRowFunctorRoot S
    (finiteFreeRowProjectiveUniverseZeroEquivalence.{uS, uMS} S).functor
    (finiteFreeRowProjectiveUniverseZeroPointIso.{uS, uMS} S)).hom).map
      (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous).cast
        (normalizedSourceStage6Vertex.{uR, uS, uMS, uNS} f)
          (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)

private theorem normalizedConcreteRootBridge5Target
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (normalizedSourceRoot6.{uR, uS, uMS, uNS} f).Homotopic (normalizedCanonicalRoot6.{uR, uS, uMS,
      uNS} f) := by
  let GM := (finiteFreeRowProjectiveUniverseZeroEquivalence.{uS, uMS} S).functor
  let MM := (finiteFreeRowProjectiveZeroHomotopyEquiv.{uS, uMS} S).toFun
  let nativeS := normalizedNativeChart.{uS, uMS, uNS} S
  let d := finiteFreeRowStableZeroComparisonUnitPath S
  let m := finiteFreeRowProjectiveZeroUnitPath.{uS, uMS} S
  let p := normalizedRowFunctorRoot S GM (finiteFreeRowProjectiveUniverseZeroPointIso.{uS, uMS} S)
  let hs := (congrArg MM (finiteFreeRowStableZeroComparison_basepoint S)).trans
    (normalizedOriginalModelObjectVertex.{uS, uMS} S (normalizedRowZeroObject S))
  let ht := normalizedOriginalModelZeroVertex.{uS, uMS} S
  let hz := SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
    (C := FGProjectiveCat.{max uS uMS} S)
  have hEdge := (CategoryTheory.realizedNerveFunctorMap_edge_homotopic GM
    (normalizedRowZeroIso S).hom).pathCast hs ht
  have hLeft :
      ((((normalizedEdgePath (normalizedRowZeroIso S).hom).map
        (CategoryTheory.realizedNerveFunctorMap GM).continuous).cast
        (CategoryTheory.realizedNerveFunctorMap_vertex GM (normalizedRowZeroObject S)).symm
        (CategoryTheory.realizedNerveFunctorMap_vertex GM
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel S))).symm).cast
            hs ht) = d.map MM.continuous := by
    apply Path.ext
    funext t
    have hRow : d t = normalizedEdgePath (normalizedRowZeroIso S).hom t :=
      congrArg (fun q => q t) (normalizedOriginalRowUnitEdge S)
    exact ((congrArg (fun k => k (normalizedEdgePath (normalizedRowZeroIso S).hom t))
      (normalizedOriginalModelForwardMap.{uS, uMS} S)).symm).trans
        (congrArg MM hRow).symm
  have hEdgeValue := (normalizedRootPathHomotopicOfEq hLeft.symm).trans hEdge
  have h := hEdgeValue.hcomp (Path.Homotopic.refl m)
  have hTarget :
      ((normalizedEdgePath (GM.mapIso (normalizedRowZeroIso S)).hom).cast hs ht).trans m =
      ((normalizedEdgePath (GM.mapIso (normalizedRowZeroIso S)).hom).trans
        (normalizedEdgePath (finiteFreeRowProjectiveUniverseZeroPointIso.{uS, uMS} S).hom)).cast
          hs hz := by
    exact congrArg (fun q =>
      ((normalizedEdgePath (GM.mapIso (normalizedRowZeroIso S)).hom).cast hs ht).trans q)
      (normalizedOriginalModelUnitEdge.{uS, uMS} S)
  have hValue := h.trans (normalizedRootPathHomotopicOfEq hTarget)
  have hTri := (normalizedEdgeIsoTriangle (GM.mapIso (normalizedRowZeroIso S)) p
    (finiteFreeRowProjectiveUniverseZeroPointIso.{uS, uMS} S) (by rfl)).pathCast hs hz
  have hOrd := hValue.trans hTri.symm
  have hClock : ∀ t : unitInterval,
      normalizedSourceFamily6.{uR, uS, uMS, uNS} f (t, ordinaryBGLBasepoint R) = nativeS.inv (MM
        (d t)) := by
    intro t
    change nativeS.inv (MM (finiteFreeRowBasedZeroComparisonHomotopy S
      (t, ordinaryBGLScalarMap f (ordinaryBGLBasepoint R)))) = _
    rw [ordinaryBGLScalarMap_point]
    exact congrArg (fun x => nativeS.inv (MM x))
      (finiteFreeRowBasedZeroComparison_homotopy_basepoint S t)
  let a := (normalizedSourceFamily6.{uR, uS, uMS, uNS} f).evalAt (ordinaryBGLBasepoint R)
  let b := (d.map MM.continuous).map nativeS.inv.hom.continuous
  have hStart : normalizedSourceStage6.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R) =
      nativeS.inv (MM (finiteFreeRowStableZeroComparison S (ordinaryBGLBasepoint S))) :=
    a.source.symm.trans ((hClock 0).trans (congrArg (fun x => nativeS.inv (MM x)) d.source))
  have hEnd : normalizedSourceStage7.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R) =
      nativeS.inv (MM (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.IdempotentModel S))) :=
    a.target.symm.trans ((hClock 1).trans (congrArg (fun x => nativeS.inv (MM x)) d.target))
  have hA : a = b.cast hStart hEnd := by
    apply Path.ext
    funext t
    exact hClock t
  have hCombined : normalizedSourceRoot6.{uR, uS, uMS, uNS} f =
      (((d.map MM.continuous).trans m).map nativeS.inv.hom.continuous).cast
        hStart (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm := by
    have hMapped :
        (((d.map MM.continuous).trans m).map nativeS.inv.hom.continuous).cast
          hStart (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm =
        (b.cast hStart hEnd).trans (normalizedSourceRoot7.{uR, uS, uMS, uNS} f) := by
      apply Path.ext
      funext t
      exact congrArg (fun q => q t)
        (Path.map_trans (d.map MM.continuous) m nativeS.inv.hom.continuous)
    exact (congrArg (fun q => q.trans (normalizedSourceRoot7.{uR, uS, uMS, uNS} f)) hA).trans
      hMapped.symm
  have hNative := (hOrd.map nativeS.inv.hom).pathCast hStart
    (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm
  have hRight : (((normalizedEdgePath p.hom).cast hs hz).map nativeS.inv.hom.continuous).cast
      hStart (normalizedNativeChartInvPoint.{uS, uMS, uNS} S).symm =
        normalizedCanonicalRoot6.{uR, uS, uMS, uNS} f := by
    apply Path.ext
    funext t
    rfl
  have hNativeValue := hNative.trans (normalizedRootPathHomotopicOfEq hRight)
  exact (normalizedRootPathHomotopicOfEq hCombined).trans hNativeValue

private def normalizedConcreteRooted5
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (normalizedSourceStage5.{uR, uS, uMS, uNS} f) (normalizedSourceStage6.{uR, uS, uMS, uNS} f)
      (normalizedSourceRoot5.{uR, uS, uMS, uNS} f) (normalizedSourceRoot6.{uR, uS, uMS, uNS} f) :=
        by
  let pre := (finiteFreeRowStableZeroComparison S).hom.comp (ordinaryBGLScalarMap f)
  have hPre : pre (ordinaryBGLBasepoint R) =
      normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel S))
        (normalizedRowZeroObject S) :=
    (congrArg (finiteFreeRowStableZeroComparison S).hom (ordinaryBGLScalarMap_point f)).trans
      (finiteFreeRowStableZeroComparison_basepoint S)
  let Hraw := normalizedRootedPostBased
    (normalizedRootedPreBased (normalizedActualTargetRowRooted.{uR, uS, uMS} S) pre hPre)
    (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom
    (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S).symm
  have hFamily : Hraw.homotopy.toContinuousMap = (normalizedSourceFamily5.{uR, uS, uMS, uNS}
    f).toContinuousMap := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hs : (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacyTargetModule.{uR, uS} S) ⋙
          SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp pre) =
        normalizedSourceStage5.{uR, uS, uMS, uNS} f := by
    apply ContinuousMap.ext
    intro x
    exact (Hraw.homotopy.map_zero_left x).symm.trans
      ((congrArg (fun H => H (0, x)) hFamily).trans ((normalizedSourceFamily5.{uR, uS, uMS, uNS}
        f).map_zero_left x))
  have ht : (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
      ((CategoryTheory.realizedNerveFunctorMap
        (finiteFreeRowProjectiveUniverseZeroEquivalence.{uS, uMS} S).functor).comp pre) =
        normalizedSourceStage6.{uR, uS, uMS, uNS} f := by
    apply ContinuousMap.ext
    intro x
    exact (Hraw.homotopy.map_one_left x).symm.trans
      ((congrArg (fun H => H (1, x)) hFamily).trans ((normalizedSourceFamily5.{uR, uS, uMS, uNS}
        f).map_one_left x))
  let Hcast := normalizedRootedCastMaps Hraw hs ht
  change NormalizedRootedFamily (ordinaryBGLBasepoint R)
    (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
    (normalizedSourceStage5.{uR, uS, uMS, uNS} f) (normalizedSourceStage6.{uR, uS, uMS, uNS} f)
    (normalizedCanonicalRoot5.{uR, uS, uMS, uNS} f) (normalizedCanonicalRoot6.{uR, uS, uMS, uNS}
      f) at Hcast
  let H := normalizedRootedChangePaths Hcast (normalizedConcreteRootBridge5Source.{uR, uS, uMS,
    uNS} f)
    (normalizedConcreteRootBridge5Target.{uR, uS, uMS, uNS} f).symm
  refine normalizedRootedReplaceHomotopy H (normalizedSourceFamily5.{uR, uS, uMS, uNS} f) ?_
  exact hFamily

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial unitInterval

open scoped ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

universe uR uS uMR uMS uNR uNS

namespace AlgebraicKTheory.StableGL

private abbrev normalizedModelScalarCompositeLift
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  normalizedZeroLiftComposite
    (normalizedModuleModel.{uR, uMR} R) (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
    (finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor
    (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)
    (normalizedOriginalModelLift.{uR, uMR} R) (normalizedIntrinsicZeroLift.{uR, uS, uMR, uMS} f)

private abbrev normalizedLegacyResizeCompositeLift
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :=
  normalizedZeroLiftComposite (normalizedLegacySourceModule f)
    (normalizedModuleResize.{uR, uS, uMS} S)
    (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f))
    (SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))
    (normalizedCanonicalZeroLift (normalizedLegacySourceModule f))
    (normalizedCanonicalZeroLift (normalizedModuleResize.{uR, uS, uMS} S))

private theorem normalizedSource2CompositePoint
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedSourceStage2.{uR, uS, uMR, uMS, uNS} f (ordinaryBGLBasepoint R) =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv
        ((normalizedZeroWeakMap
          (normalizedModuleModel.{uR, uMR} R ⋙
            nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
          ((finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor ⋙
            nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)
          (normalizedModelScalarCompositeLift.{uR, uS, uMR, uMS} f)).hom
          (normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
            (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)))) := by
  let GM := (finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor
  let GF := nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f
  let v := normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
    (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))
  have hB : (finiteFreeRowProjectiveZeroHomotopyEquiv.{uR, uMR} R).toFun
      (finiteFreeRowBasedZeroComparison R (ordinaryBGLBasepoint R)) =
      CategoryTheory.realizedNerveFunctorMap GM v :=
    ((congrArg (finiteFreeRowProjectiveZeroHomotopyEquiv.{uR, uMR} R).toFun
      (finiteFreeRowBasedZeroComparison_basepoint R)).trans
      (congrArg (finiteFreeRowProjectiveZeroHomotopyEquiv.{uR, uMR} R).toFun
        (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
          (C := FGProjectiveCat.IdempotentModel R)))).trans
        (congrArg (fun k => k v) (normalizedOriginalModelForwardMap.{uR, uMR} R))
  exact (congrArg (fun x => (normalizedNativeChart.{uS, uMS, uNS} S).inv
    (CategoryTheory.realizedNerveFunctorMap GF x)) hB).trans
    (congrArg (normalizedNativeChart.{uS, uMS, uNS} S).inv
      (congrArg (fun k => k v) (normalizedMixedFunctorComposition GM GF)).symm)

private theorem normalizedSource3CompositePoint
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedSourceStage3.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R) =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv
        ((normalizedZeroWeakMap
          (normalizedLegacySourceModule f ⋙ normalizedModuleResize.{uR, uS, uMS} S)
          (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f) ⋙
            SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))
          (normalizedLegacyResizeCompositeLift.{uR, uS, uMS} f)).hom
          (normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
            (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)))) := by
  let GQ := SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f)
  let GU := SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S)
  let v := normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
    (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))
  have hB : finiteFreeRowBasedZeroComparison R (ordinaryBGLBasepoint R) = v :=
    (finiteFreeRowBasedZeroComparison_basepoint R).trans
      (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
        (C := FGProjectiveCat.IdempotentModel R))
  exact (congrArg (fun x => (normalizedNativeChart.{uS, uMS, uNS} S).inv
    (CategoryTheory.realizedNerveFunctorMap GU (CategoryTheory.realizedNerveFunctorMap GQ x)))
    hB).trans
    (congrArg (normalizedNativeChart.{uS, uMS, uNS} S).inv
      (congrArg (fun k => k v) (normalizedMixedFunctorComposition GQ GU)).symm)

private def normalizedCanonicalRoot2
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage2.{uR, uS, uMR, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  (((normalizedZeroWeakMap
    (normalizedModuleModel.{uR, uMR} R ⋙ nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
    ((finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor ⋙
      nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)
    (normalizedModelScalarCompositeLift.{uR, uS, uMR, uMS} f)).rootPath).map
      (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous).cast
        (normalizedSource2CompositePoint.{uR, uS, uMR, uMS, uNS} f)
          (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)

private def normalizedCanonicalRoot3
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Path (normalizedSourceStage3.{uR, uS, uMS, uNS} f (ordinaryBGLBasepoint R))
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  (((normalizedZeroWeakMap
    (normalizedLegacySourceModule f ⋙ normalizedModuleResize.{uR, uS, uMS} S)
    (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f) ⋙
      SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))
    (normalizedLegacyResizeCompositeLift.{uR, uS, uMS} f)).rootPath).map
      (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.continuous).cast
        (normalizedSource3CompositePoint.{uR, uS, uMS, uNS} f)
          (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)

private theorem normalizedOriginalModelWeakRootValue.{uModelRing, uModelCarrier}
    (R : Type uModelRing) [Ring R] (t : unitInterval) :
    finiteFreeRowProjectiveZeroUnitPath.{uModelRing, uModelCarrier} R t =
      (normalizedZeroWeakMap (normalizedModuleModel.{uModelRing, uModelCarrier} R)
        (finiteFreeRowProjectiveUniverseZeroEquivalence.{uModelRing, uModelCarrier} R).functor
        (normalizedOriginalModelLift.{uModelRing, uModelCarrier} R)).rootPath t :=
  finiteFreeRowProjectiveZeroUnitPath_value.{uModelRing, uModelCarrier} R t

private theorem normalizedConcreteModelTrace1Forward
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    normalizedSourceFamily1.{uR, uS, uMR, uMS, uNR, uNS} f (t, ordinaryBGLBasepoint R) =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv
        (CategoryTheory.realizedNerveFunctorMap
          (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)
          ((normalizedZeroWeakMap (normalizedModuleModel.{uR, uMR} R)
            (finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor
            (normalizedOriginalModelLift.{uR, uMR} R)).rootPath (σ t))) := by
  change nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f
    ((normalizedNativeChart.{uR, uMR, uNR} R).inv
      (normalizedOriginalModelTrace.{uR, uMR, uNR} R
        (σ t, finiteFreeRowBasedZeroComparison R (ordinaryBGLBasepoint R)))) = _
  rw [finiteFreeRowBasedZeroComparison_basepoint, normalizedOriginalModelTraceRoot]
  exact (congrArg (fun k => k (finiteFreeRowProjectiveZeroUnitPath.{uR, uMR} R (σ t)))
    (normalizedRawScalarPreSourceChart.{uR, uS, uMR, uMS, uNR, uNS} f)).trans
    (congrArg (fun x => (normalizedNativeChart.{uS, uMS, uNS} S).inv
      (CategoryTheory.realizedNerveFunctorMap
        (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f) x))
      (normalizedOriginalModelWeakRootValue.{uR, uMR} R (σ t)))

private theorem normalizedConcreteModelTrace1Inverse
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    ((normalizedSourceFamily1.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt (ordinaryBGLBasepoint
      R)).symm t =
      (normalizedNativeChart.{uS, uMS, uNS} S).inv
        (CategoryTheory.realizedNerveFunctorMap
          (nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)
          ((normalizedZeroWeakMap (normalizedModuleModel.{uR, uMR} R)
            (finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor
            (normalizedOriginalModelLift.{uR, uMR} R)).rootPath t)) := by
  change normalizedSourceFamily1.{uR, uS, uMR, uMS, uNR, uNS} f (σ t, ordinaryBGLBasepoint R) = _
  simpa only [unitInterval.symm_symm] using normalizedConcreteModelTrace1Forward.{uR, uS, uMR,
    uMS, uNR, uNS} f (σ t)

private theorem normalizedConcreteRootBridge2Source
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (normalizedSourceRoot2.{uR, uS, uMR, uMS, uNR, uNS} f).Homotopic
      (normalizedCanonicalRoot2.{uR, uS, uMR, uMS, uNS} f) := by
  let P := normalizedModuleModel.{uR, uMR} R
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let GM := (finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor
  let GF := nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f
  let WM := normalizedZeroWeakMap P GM (normalizedOriginalModelLift.{uR, uMR} R)
  let WF := normalizedZeroWeakMap F GF (normalizedIntrinsicZeroLift.{uR, uS, uMR, uMS} f)
  let WC := normalizedZeroWeakMap (P ⋙ F) (GM ⋙ GF) (normalizedModelScalarCompositeLift.{uR, uS,
    uMR, uMS} f)
  let nativeS := normalizedNativeChart.{uS, uMS, uNS} S
  let a := ((normalizedSourceFamily1.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt (ordinaryBGLBasepoint
    R)).symm
  let first := (WM.rootPath.map (CategoryTheory.realizedNerveFunctorMap GF).continuous).map
    nativeS.inv.hom.continuous
  let second := WF.rootPath.map nativeS.inv.hom.continuous
  have hStart : normalizedSourceStage2.{uR, uS, uMR, uMS, uNS} f (ordinaryBGLBasepoint R) =
      nativeS.inv (CategoryTheory.realizedNerveFunctorMap GF
        (WM.hom (normalizedObjectVertex
          (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))))) :=
    a.source.symm.trans ((normalizedConcreteModelTrace1Inverse.{uR, uS, uMR, uMS, uNR, uNS} f
      0).trans first.source)
  have hMiddle : normalizedSourceStage1.{uR, uS, uMR, uMS, uNR, uNS} f (ordinaryBGLBasepoint R) =
      nativeS.inv (CategoryTheory.realizedNerveFunctorMap GF
        (normalizedObjectVertex
          (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uR uMR} R))
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uR uMR} R)))) :=
    a.target.symm.trans ((normalizedConcreteModelTrace1Inverse.{uR, uS, uMR, uMS, uNR, uNS} f
      1).trans first.target)
  have hFirst : a = first.cast hStart hMiddle := by
    apply Path.ext
    funext t
    exact normalizedConcreteModelTrace1Inverse.{uR, uS, uMR, uMS, uNR, uNS} f t
  have hSecond : (normalizedSourceRoot1.{uR, uS, uMR, uMS, uNR, uNS} f).Homotopic
      (second.cast hMiddle (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)) := by
    let hNR := congrArg (nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedOriginalNorm.{uR, uMR, uNR} R).sourcePoint
    have h := (normalizedIntrinsicRootNativeEdge.{uR, uS, uMR, uMS, uNR, uNS} f).pathCast hNR rfl
    have hRight :
        ((((normalizedEdgePath
          (nativeProjectiveZeroScalarZeroPointIso.{uR, uS, uMR, uMS} f).hom).map
          nativeS.inv.hom.continuous).cast (normalizedIntrinsicRawNativeVertex.{uR, uS, uMR, uMS,
            uNR, uNS} f)
          (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)).cast hNR rfl) =
          second.cast hMiddle (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S) := by
      apply Path.ext
      funext t
      rfl
    exact h.trans (normalizedRootPathHomotopicOfEq hRight)
  have hProduct := (normalizedRootPathHomotopicOfEq hFirst).hcomp hSecond
  have hProductPath : (first.cast hStart hMiddle).trans
      (second.cast hMiddle (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)) =
      (((WM.comp WF).rootPath).map nativeS.inv.hom.continuous).cast
        hStart (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S) := by
    apply Path.ext
    funext t
    exact congrArg (fun q => q t)
      (Path.map_trans
        (WM.rootPath.map (CategoryTheory.realizedNerveFunctorMap GF).continuous)
        WF.rootPath nativeS.inv.hom.continuous).symm
  have hProductValue := hProduct.trans (normalizedRootPathHomotopicOfEq hProductPath)
  have hComp := normalizedZeroWeakCompositeRoot P F GM GF
    (normalizedOriginalModelLift.{uR, uMR} R) (normalizedIntrinsicZeroLift.{uR, uS, uMR, uMS} f)
  have hNative := (hComp.map nativeS.inv.hom).pathCast
    (normalizedSource2CompositePoint.{uR, uS, uMR, uMS, uNS} f)
      (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)
  have hRight :
      ((((WM.comp WF).rootPath).cast
        (congrArg (fun k => k (normalizedObjectVertex
          (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))))
          (normalizedZeroWeakCompositeMap P F GM GF
            (normalizedOriginalModelLift.{uR, uMR} R) (normalizedIntrinsicZeroLift.{uR, uS, uMR,
              uMS} f))) rfl).map
              nativeS.inv.hom.continuous).cast (normalizedSource2CompositePoint.{uR, uS, uMR, uMS,
                uNS} f)
              (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S) =
              (((WM.comp WF).rootPath).map nativeS.inv.hom.continuous).cast
                hStart (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S) := by
    apply Path.ext
    funext t
    rfl
  have hNativeValue := hNative.trans (normalizedRootPathHomotopicOfEq hRight)
  exact hProductValue.trans hNativeValue.symm

private theorem normalizedConcreteRootBridge2Target
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (normalizedCanonicalRoot3.{uR, uS, uMS, uNS} f).Homotopic (normalizedSourceRoot3.{uR, uS, uMS,
      uNS} f) := by
  let Q := normalizedLegacySourceModule f
  let U := normalizedModuleResize.{uR, uS, uMS} S
  let GQ := SInverseS.zeroComponentFunctor Q
  let GU := SInverseS.zeroComponentFunctor U
  let WQ := normalizedZeroWeakMap Q GQ (normalizedCanonicalZeroLift Q)
  let WU := normalizedZeroWeakMap U GU (normalizedCanonicalZeroLift U)
  let nativeS := normalizedNativeChart.{uS, uMS, uNS} S
  have hComp := normalizedZeroWeakCompositeRoot Q U GQ GU
    (normalizedCanonicalZeroLift Q) (normalizedCanonicalZeroLift U)
  have h := (hComp.map nativeS.inv.hom).pathCast
    (normalizedSource3CompositePoint.{uR, uS, uMS, uNS} f)
      (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S)
  have hRight :
      ((((WQ.comp WU).rootPath).cast
        (congrArg (fun k => k (normalizedObjectVertex
          (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R))))
          (normalizedZeroWeakCompositeMap Q U GQ GU
            (normalizedCanonicalZeroLift Q) (normalizedCanonicalZeroLift U))) rfl).map
              nativeS.inv.hom.continuous).cast (normalizedSource3CompositePoint.{uR, uS, uMS, uNS}
                f)
              (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S) =
                normalizedSourceRoot3.{uR, uS, uMS, uNS} f := by
    apply Path.ext
    funext t
    rfl
  exact h.trans (normalizedRootPathHomotopicOfEq hRight)

private def normalizedConcreteRooted2
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (normalizedSourceStage2.{uR, uS, uMR, uMS, uNS} f) (normalizedSourceStage3.{uR, uS, uMS,
        uNS} f)
      (normalizedSourceRoot2.{uR, uS, uMR, uMS, uNR, uNS} f) (normalizedSourceRoot3.{uR, uS, uMS,
        uNS} f) := by
  let pre := (finiteFreeRowBasedZeroComparison R).hom
  have hPre : pre (ordinaryBGLBasepoint R) =
      normalizedObjectVertex (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) :=
    (finiteFreeRowBasedZeroComparison_basepoint R).trans
      (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
        (C := FGProjectiveCat.IdempotentModel R))
  let Hraw := normalizedRootedPostBased
    (normalizedRootedPreBased (normalizedActualSourceZeroRooted.{uR, uS, uMR, uMS} f) pre hPre)
    (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom
    (normalizedIntrinsicTargetNativeVertex.{uS, uMS, uNS} S).symm
  have hFamily : Hraw.homotopy.toContinuousMap = (normalizedSourceFamily2.{uR, uS, uMR, uMS, uNS}
    f).toContinuousMap := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hs : (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
      ((CategoryTheory.realizedNerveFunctorMap
        ((finiteFreeRowProjectiveUniverseZeroEquivalence.{uR, uMR} R).functor ⋙
          nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)).comp pre) =
        normalizedSourceStage2.{uR, uS, uMR, uMS, uNS} f := by
    apply ContinuousMap.ext
    intro x
    exact (Hraw.homotopy.map_zero_left x).symm.trans
      ((congrArg (fun H => H (0, x)) hFamily).trans ((normalizedSourceFamily2.{uR, uS, uMR, uMS,
        uNS} f).map_zero_left x))
  have ht : (normalizedNativeChart.{uS, uMS, uNS} S).inv.hom.comp
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor (normalizedLegacySourceModule f) ⋙
          SInverseS.zeroComponentFunctor (normalizedModuleResize.{uR, uS, uMS} S))).comp pre) =
        normalizedSourceStage3.{uR, uS, uMS, uNS} f := by
    apply ContinuousMap.ext
    intro x
    exact (Hraw.homotopy.map_one_left x).symm.trans
      ((congrArg (fun H => H (1, x)) hFamily).trans ((normalizedSourceFamily2.{uR, uS, uMR, uMS,
        uNS} f).map_one_left x))
  let Hcast := normalizedRootedCastMaps Hraw hs ht
  change NormalizedRootedFamily (ordinaryBGLBasepoint R)
    (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
    (normalizedSourceStage2.{uR, uS, uMR, uMS, uNS} f) (normalizedSourceStage3.{uR, uS, uMS, uNS} f)
    (normalizedCanonicalRoot2.{uR, uS, uMR, uMS, uNS} f) (normalizedCanonicalRoot3.{uR, uS, uMS,
      uNS} f) at Hcast
  let H := normalizedRootedChangePaths Hcast (normalizedConcreteRootBridge2Source.{uR, uS, uMR,
    uMS, uNR, uNS} f)
    (normalizedConcreteRootBridge2Target.{uR, uS, uMS, uNS} f)
  refine normalizedRootedReplaceHomotopy H (normalizedSourceFamily2.{uR, uS, uMR, uMS, uNS} f) ?_
  exact hFamily

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped ContinuousMap Simplicial TopCat.modelCategory

attribute [local instance] CategoryTheory.uliftCategory

open scoped ZeroObject

universe uR uS uMR uMS uNR uNS

namespace AlgebraicKTheory.StableGL

private def normalizedConcreteEightRooted
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    NormalizedRootedFamily (ordinaryBGLBasepoint R)
      (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
      (normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f) (normalizedSourceStage8.{uR, uS,
        uMS, uNS} f)
      (normalizedSourceRoot0.{uR, uS, uMR, uMS, uNR, uNS} f) (normalizedSourceRoot8.{uR, uS, uMS,
        uNS} f) :=
  normalizedRootedTrans (normalizedConcreteRooted0.{uR, uS, uMR, uMS, uNR, uNS} f)
    (normalizedRootedTrans (normalizedConcreteRooted1.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedRootedTrans (normalizedConcreteRooted2.{uR, uS, uMR, uMS, uNR, uNS} f)
        (normalizedRootedTrans (normalizedConcreteRooted3.{uR, uS, uMS, uNS} f)
          (normalizedRootedTrans (normalizedConcreteRooted4.{uR, uS, uMS, uNS} f)
            (normalizedRootedTrans (normalizedConcreteRooted5.{uR, uS, uMS, uNS} f)
              (normalizedRootedTrans (normalizedConcreteRooted6.{uR, uS, uMS, uNS} f)
                (normalizedConcreteRooted7.{uR, uS, uMS, uNS}
                  f)))))))

private theorem normalizedConcreteEightNullTrace
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (((nativeProjectiveZeroScalarNormalizedSourceHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt
      (ordinaryBGLBasepoint R)).cast (normalizedSourceStartPoint.{uR, uS, uMR, uMS, uNR, uNS}
        f).symm
        (normalizedSourceEndPoint.{uR, uS, uMS, uNS} f).symm).Homotopic
      (Path.refl (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)) :=
  by
    let H := normalizedConcreteEightRooted.{uR, uS, uMR, uMS, uNR, uNS} f
    let K := nativeProjectiveZeroScalarNormalizedSourceHomotopy.{
      uR, uS, uMR, uMS, uNR, uNS} f
    have hWhole : H.homotopy.toContinuousMap = K.toContinuousMap := by
      apply ContinuousMap.ext
      intro z
      rfl
    exact normalizedRootedNullTrace (normalizedSourceStartPoint.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedSourceEndPoint.{uR, uS, uMS, uNS} f)
      (normalizedRootedReplaceHomotopy H K hWhole)

private abbrev normalizedWorkingBGLCategory.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (R : Type uWorkR) [Ring R] :=
  ULiftHom.{max ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS) + 1) uWorkNR uWorkNS} (ULift.{max
      ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS) + 1) uWorkNR uWorkNS} (ClassifyingCategory
      R))

private abbrev normalizedWorkingBGLSpace.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (R : Type uWorkR) [Ring R] : TopCat.{max ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS) + 1)
        uWorkNR uWorkNS} :=
  SSet.toTop.obj (nerve (normalizedWorkingBGLCategory.{uWorkR, uWorkS, uWorkMR, uWorkMS,
    uWorkNR, uWorkNS} R))

private def normalizedWorkingBGLPoint.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (R : Type uWorkR) [Ring R] :
    normalizedWorkingBGLSpace.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} R :=
  normalizedObjectVertex
    (normalizedWorkingBGLCategory.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} R)
    (ULiftHom.objUp (ULift.up (SingleObj.star (StableGL R)ᵐᵒᵖ)))

private def normalizedWorkingBGLHomeo.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (R : Type uWorkR) [Ring R] :
    normalizedWorkingBGLSpace.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} R ≃ₜ ordinaryBGL
        R :=
  SSet.realizedNerveLiftHomeomorph.{0, uWorkR, max ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS)
      + 1) uWorkNR uWorkNS} (ClassifyingCategory R)

private theorem normalizedWorkingBGLHomeoPoint.{
    uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (R : Type uWorkR) [Ring R] :
    normalizedWorkingBGLHomeo.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} R
      (normalizedWorkingBGLPoint.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} R) =
      ordinaryBGLBasepoint R := by
  exact (SSet.realizedNerveLiftHomeomorph_vertex.{0, uWorkR, max ((max uWorkR uWorkMR) + 1) ((max
      uWorkS uWorkMS) + 1) uWorkNR uWorkNS}
    (ClassifyingCategory R) (SingleObj.star (StableGL R)ᵐᵒᵖ)).trans (by rfl)

private theorem normalizedWorkingBGLInversePoint.{
    uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (R : Type uWorkR) [Ring R] :
    (normalizedWorkingBGLHomeo.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} R).symm
        (ordinaryBGLBasepoint R) =
      normalizedWorkingBGLPoint.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} R := by
  let H := normalizedWorkingBGLHomeo.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} R
  let m := normalizedWorkingBGLPoint.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} R
  exact (congrArg H.symm (normalizedWorkingBGLHomeoPoint.{uWorkR, uWorkS, uWorkMR, uWorkMS,
    uWorkNR, uWorkNS} R)).symm.trans (H.symm_apply_apply m)

private abbrev normalizedWorkingTargetCategory.{
    uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (S : Type uWorkS) [Ring S] :=
  ULiftHom.{max ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS) + 1) uWorkNR uWorkNS} (ULift.{max
      ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS) + 1) uWorkNR uWorkNS}
    (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uWorkS uWorkMS} S)))

private abbrev normalizedWorkingTargetSpace.{
    uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (S : Type uWorkS) [Ring S] : TopCat.{max ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS) + 1)
        uWorkNR uWorkNS} :=
  SSet.toTop.obj (nerve (normalizedWorkingTargetCategory.{uWorkR, uWorkS, uWorkMR, uWorkMS,
    uWorkNR, uWorkNS} S))

private def normalizedWorkingTargetPoint.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (S : Type uWorkS) [Ring S] :
    normalizedWorkingTargetSpace.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S :=
  normalizedObjectVertex
    (normalizedWorkingTargetCategory.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S)
    (ULiftHom.objUp (ULift.up
      (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uWorkS uWorkMS} S))))

private def normalizedWorkingTargetHomeo.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (S : Type uWorkS) [Ring S] :
    normalizedWorkingTargetSpace.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S ≃ₜ
      SInverseS.ComponentTranslation.zeroSpace
        (C := FGProjectiveCat.{max uWorkS uWorkMS} S) :=
  SSet.realizedNerveLiftHomeomorph.{((max uWorkS uWorkMS) + 1), ((max uWorkS uWorkMS) + 1), max
      ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS) + 1) uWorkNR uWorkNS}
    (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uWorkS uWorkMS} S))

private def normalizedNativeTargetToWorking.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (S : Type uWorkS) [Ring S] :
    C(RingK0.projectiveZeroSpace.{uWorkS, uWorkMS, uWorkNS} S,
      normalizedWorkingTargetSpace.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S) :=
  (normalizedWorkingTargetHomeo.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
      S).symm.toHomotopyEquiv.toFun.comp (normalizedNativeChart.{uWorkS, uWorkMS, uWorkNS}
      S).hom.hom

private def normalizedWorkingTargetToNative.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
    (S : Type uWorkS) [Ring S] :
    C(normalizedWorkingTargetSpace.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S,
      RingK0.projectiveZeroSpace.{uWorkS, uWorkMS, uWorkNS} S) :=
  (normalizedNativeChart.{uWorkS, uWorkMS, uWorkNS} S).inv.hom.comp
    (normalizedWorkingTargetHomeo.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS}
        S).toHomotopyEquiv.toFun

private theorem normalizedNativeTargetWorkingPoint.{
    uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} (S : Type uWorkS) [Ring S] :
    normalizedNativeTargetToWorking.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S
        (RingK0.projectiveZeroPoint.{uWorkS, uWorkMS, uWorkNS} S) =
      normalizedWorkingTargetPoint.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S := by
  let HT := normalizedWorkingTargetHomeo.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S
  exact (congrArg HT.symm (normalizedNativeChartPoint.{uWorkS, uWorkMS, uWorkNS} S)).trans
    ((congrArg HT.symm (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max uWorkS uWorkMS} S))).trans
      (SSet.realizedNerveLiftHomeomorph_symm_vertex.{((max uWorkS uWorkMS) + 1), ((max uWorkS
          uWorkMS) + 1), max ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS) + 1) uWorkNR uWorkNS}
        (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uWorkS uWorkMS} S))
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uWorkS uWorkMS} S))))

private theorem normalizedWorkingTargetNativePoint.{
    uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} (S : Type uWorkS) [Ring S] :
    normalizedWorkingTargetToNative.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S
        (normalizedWorkingTargetPoint.{uWorkR, uWorkS, uWorkMR, uWorkMS, uWorkNR, uWorkNS} S) =
      RingK0.projectiveZeroPoint.{uWorkS, uWorkMS, uWorkNS} S := by
  let nativeS := normalizedNativeChart.{uWorkS, uWorkMS, uWorkNS} S
  exact (congrArg nativeS.inv
    ((SSet.realizedNerveLiftHomeomorph_vertex.{((max uWorkS uWorkMS) + 1), ((max uWorkS uWorkMS) +
        1), max ((max uWorkR uWorkMR) + 1) ((max uWorkS uWorkMS) + 1) uWorkNR uWorkNS}
      (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uWorkS uWorkMS} S))
      (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uWorkS uWorkMS} S))).trans
      (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
        (C := FGProjectiveCat.{max uWorkS uWorkMS} S)).symm)).trans
        (normalizedNativeChartInvPoint.{uWorkS, uWorkMS, uWorkNS} S)

private def normalizedWorkingSourceMap0
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(normalizedWorkingBGLSpace.{uR, uS, uMR, uMS, uNR, uNS} R,
      normalizedWorkingTargetSpace.{uR, uS, uMR, uMS, uNR, uNS} S) :=
  (normalizedNativeTargetToWorking.{uR, uS, uMR, uMS, uNR, uNS} S).comp
    ((normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f).comp
      (normalizedWorkingBGLHomeo.{uR, uS, uMR, uMS, uNR, uNS} R).toHomotopyEquiv.toFun)

private def normalizedWorkingSourceMap8
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(normalizedWorkingBGLSpace.{uR, uS, uMR, uMS, uNR, uNS} R,
      normalizedWorkingTargetSpace.{uR, uS, uMR, uMS, uNR, uNS} S) :=
  (normalizedNativeTargetToWorking.{uR, uS, uMR, uMS, uNR, uNS} S).comp
    ((normalizedSourceStage8.{uR, uS, uMS, uNS} f).comp
      (normalizedWorkingBGLHomeo.{uR, uS, uMR, uMS, uNR, uNS} R).toHomotopyEquiv.toFun)

private def normalizedWorkingEightHomotopy
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy (normalizedWorkingSourceMap0.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedWorkingSourceMap8.{uR, uS, uMR, uMS, uNR, uNS} f) :=
  (ContinuousMap.Homotopy.refl
    (normalizedNativeTargetToWorking.{uR, uS, uMR, uMS, uNR, uNS} S)).comp
    ((nativeProjectiveZeroScalarNormalizedSourceHomotopy.{uR, uS, uMR, uMS, uNR, uNS}
        f).compContinuousMap
        (normalizedWorkingBGLHomeo.{uR, uS, uMR, uMS, uNR, uNS} R).toHomotopyEquiv.toFun)

private theorem normalizedWorkingSourcePoint0
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedWorkingSourceMap0.{uR, uS, uMR, uMS, uNR, uNS} f
        (normalizedWorkingBGLPoint.{uR, uS, uMR, uMS, uNR, uNS} R) =
      normalizedWorkingTargetPoint.{uR, uS, uMR, uMS, uNR, uNS} S :=
  ((congrArg (fun x => normalizedNativeTargetToWorking.{uR, uS, uMR, uMS, uNR, uNS} S
    (normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f x))
    (normalizedWorkingBGLHomeoPoint.{uR, uS, uMR, uMS, uNR, uNS} R)).trans
    (congrArg (normalizedNativeTargetToWorking.{uR, uS, uMR, uMS, uNR, uNS} S)
      (normalizedSourceStartPoint.{uR, uS, uMR, uMS, uNR, uNS} f))).trans
      (normalizedNativeTargetWorkingPoint.{uR, uS, uMR, uMS, uNR, uNS} S)

private theorem normalizedWorkingSourcePoint8
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    normalizedWorkingSourceMap8.{uR, uS, uMR, uMS, uNR, uNS} f
        (normalizedWorkingBGLPoint.{uR, uS, uMR, uMS, uNR, uNS} R) =
      normalizedWorkingTargetPoint.{uR, uS, uMR, uMS, uNR, uNS} S :=
  ((congrArg (fun x => normalizedNativeTargetToWorking.{uR, uS, uMR, uMS, uNR, uNS} S
    (normalizedSourceStage8.{uR, uS, uMS, uNS} f x))
    (normalizedWorkingBGLHomeoPoint.{uR, uS, uMR, uMS, uNR, uNS} R)).trans
    (congrArg (normalizedNativeTargetToWorking.{uR, uS, uMR, uMS, uNR, uNS} S)
      (normalizedSourceEndPoint.{uR, uS, uMS, uNS} f))).trans
      (normalizedNativeTargetWorkingPoint.{uR, uS, uMR, uMS, uNR, uNS} S)

private theorem normalizedWorkingEightNullTrace
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (((normalizedWorkingEightHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt
      (normalizedWorkingBGLPoint.{uR, uS, uMR, uMS, uNR, uNS} R)).cast
        (normalizedWorkingSourcePoint0.{uR, uS, uMR, uMS, uNR, uNS} f).symm
          (normalizedWorkingSourcePoint8.{uR, uS, uMR, uMS, uNR, uNS} f).symm).Homotopic
      (Path.refl (normalizedWorkingTargetPoint.{uR, uS, uMR, uMS, uNR, uNS} S)) := by
  let k := normalizedNativeTargetToWorking.{uR, uS, uMR, uMS, uNR, uNS} S
  let m := normalizedWorkingBGLPoint.{uR, uS, uMR, uMS, uNR, uNS} R
  let HS := normalizedWorkingBGLHomeo.{uR, uS, uMR, uMS, uNR, uNS} R
  let y := RingK0.projectiveZeroPoint.{uS, uMS, uNS} S
  let hy := normalizedNativeTargetWorkingPoint.{uR, uS, uMR, uMS, uNR, uNS} S
  have h := ((normalizedConcreteEightNullTrace.{uR, uS, uMR, uMS, uNR, uNS} f).map k).pathCast
    hy.symm hy.symm
  have hLeft :
      (((((nativeProjectiveZeroScalarNormalizedSourceHomotopy.{
        uR, uS, uMR, uMS, uNR, uNS} f).evalAt (ordinaryBGLBasepoint R)).cast
          (normalizedSourceStartPoint.{uR, uS, uMR, uMS, uNR, uNS} f).symm
            (normalizedSourceEndPoint.{uR, uS, uMS, uNS} f).symm).map
              k.continuous).cast hy.symm hy.symm =
      (((normalizedWorkingEightHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt m).cast
        (normalizedWorkingSourcePoint0.{uR, uS, uMR, uMS, uNR, uNS} f).symm
          (normalizedWorkingSourcePoint8.{uR, uS, uMR, uMS, uNR, uNS} f).symm)) := by
    apply Path.ext
    funext t
    exact congrArg (fun x => k
      (nativeProjectiveZeroScalarNormalizedSourceHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f (t, x)))
      (normalizedWorkingBGLHomeoPoint.{uR, uS, uMR, uMS, uNR, uNS} R).symm
  have hRight : ((Path.refl y).map k.continuous).cast hy.symm hy.symm =
      Path.refl (normalizedWorkingTargetPoint.{uR, uS, uMR, uMS, uNR, uNS} S) := by
    apply Path.ext
    funext t
    exact hy
  exact ((normalizedRootPathHomotopicOfEq hLeft.symm).trans h).trans
    (normalizedRootPathHomotopicOfEq hRight)

private def normalizedWorkingSourceRelativeComputed
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.HomotopyRel (normalizedWorkingSourceMap0.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedWorkingSourceMap8.{uR, uS, uMR, uMS, uNR, uNS} f)
      {normalizedWorkingBGLPoint.{uR, uS, uMR, uMS, uNR, uNS} R} := by
  let K := normalizedWorkingBGLCategory.{uR, uS, uMR, uMS, uNR, uNS} R
  let vm : ComposableArrows K 0 := ComposableArrows.mk₀
    (ULiftHom.objUp (ULift.up (SingleObj.star (StableGL R)ᵐᵒᵖ)))
  let m := normalizedWorkingBGLPoint.{uR, uS, uMR, uMS, uNR, uNS} R
  let n := normalizedWorkingTargetPoint.{uR, uS, uMR, uMS, uNR, uNS} S
  let _ : Cofibration (TopCat.const m : TopCat.of PUnit.{max ((max uR uMR) + 1) ((max uS uMS) + 1)
      uNR uNS + 1} ⟶
      normalizedWorkingBGLSpace.{uR, uS, uMR, uMS, uNR, uNS} R) :=
    SSet.realizedVertex_pointMap_cofibration (nerve K) vm
  exact Classical.choice (TopCat.exists_pointRelativeHomotopy_of_null_trace
    (TopCat.ofHom (normalizedWorkingSourceMap0.{uR, uS, uMR, uMS, uNR, uNS} f)) (TopCat.ofHom
      (normalizedWorkingSourceMap8.{uR, uS, uMR, uMS, uNR, uNS} f))
    m n (normalizedWorkingSourcePoint0.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedWorkingSourcePoint8.{uR, uS, uMR, uMS, uNR, uNS} f)
    (normalizedWorkingEightHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedWorkingEightNullTrace.{uR, uS, uMR, uMS, uNR, uNS} f).some)

private def normalizedOriginalSourceRelativeComputed
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.HomotopyRel (normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f)
      (normalizedSourceStage8.{uR, uS, uMS, uNS} f)
      {ordinaryBGLBasepoint R} := by
  let HS := normalizedWorkingBGLHomeo.{uR, uS, uMR, uMS, uNR, uNS} R
  let HT := normalizedWorkingTargetHomeo.{uR, uS, uMR, uMS, uNR, uNS} S
  let nativeS := normalizedNativeChart.{uS, uMS, uNS} S
  let back := normalizedWorkingTargetToNative.{uR, uS, uMR, uMS, uNR, uNS} S
  let Rwork := normalizedWorkingSourceRelativeComputed.{uR, uS, uMR, uMS, uNR, uNS} f
  let Rpre := Rwork.precomposePointRelative HS.symm.toHomotopyEquiv.toFun (ordinaryBGLBasepoint R)
    (normalizedWorkingBGLInversePoint.{uR, uS, uMR, uMS, uNR, uNS} R)
  let Rnative := Rpre.compContinuousMap back
  refine Rnative.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    change nativeS.inv (HT (HT.symm (nativeS.hom (normalizedSourceStage0.{uR, uS, uMR, uMS, uNR,
      uNS} f (HS (HS.symm x)))))) =
      normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f x
    rw [HS.apply_symm_apply, HT.apply_symm_apply]
    exact TopCat.hom_inv_id_apply nativeS (normalizedSourceStage0.{uR, uS, uMR, uMS, uNR, uNS} f x)
  · apply ContinuousMap.ext
    intro x
    change nativeS.inv (HT (HT.symm (nativeS.hom (normalizedSourceStage8.{uR, uS, uMS, uNS} f (HS
      (HS.symm x)))))) =
      normalizedSourceStage8.{uR, uS, uMS, uNS} f x
    rw [HS.apply_symm_apply, HT.apply_symm_apply]
    exact TopCat.hom_inv_id_apply nativeS (normalizedSourceStage8.{uR, uS, uMS, uNS} f x)

/-- The full intrinsic SIX-role normalized source square, relative to the
original BGL root, from the SAME original model/row/scalar/retuning families. -/
public def nativeProjectiveZeroScalarNormalizedSourceComparison
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.HomotopyRel
      ((nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
        (nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R).sourceMap)
      ((nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S).sourceMap.comp
        (ordinaryBGLScalarMap f)) {ordinaryBGLBasepoint R} :=
  normalizedOriginalSourceRelativeComputed.{uR, uS, uMR, uMS, uNR, uNS} f

/-- The whole SAME SIX-role point-relative source family, with no extra choice. -/
public def nativeProjectiveZeroScalarNormalizedSourceComparisonFamily
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    C(unitInterval × ordinaryBGL R, RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  (nativeProjectiveZeroScalarNormalizedSourceComparison.{uR, uS, uMR, uMS, uNR, uNS}
      f).toContinuousMap

private theorem normalizedSourceRelativeWholeValue
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarNormalizedSourceComparison.{uR, uS, uMR, uMS, uNR, uNS}
        f).toContinuousMap =
      nativeProjectiveZeroScalarNormalizedSourceComparisonFamily.{uR, uS, uMR, uMS, uNR, uNS} f :=
          by
  rfl

/-- The relative comparison retains its SAME complete continuous-family value. -/
public theorem nativeProjectiveZeroScalarNormalizedSourceComparison_toContinuousMap
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (nativeProjectiveZeroScalarNormalizedSourceComparison.{uR, uS, uMR, uMS, uNR, uNS}
        f).toContinuousMap =
      nativeProjectiveZeroScalarNormalizedSourceComparisonFamily.{uR, uS, uMR, uMS, uNR, uNS} f :=
  normalizedSourceRelativeWholeValue f

/-- EVERY interval time fixes the SAME original normalized native target root. -/
public theorem nativeProjectiveZeroScalarNormalizedSourceComparison_root_value
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarNormalizedSourceComparisonFamily.{uR, uS, uMR, uMS, uNR, uNS} f
        (t, ordinaryBGLBasepoint R) = RingK0.projectiveZeroPoint.{uS, uMS, uNS} S :=
  ((nativeProjectiveZeroScalarNormalizedSourceComparison.{uR, uS, uMR, uMS, uNR, uNS} f).eq_fst t
    (by rfl)).trans (normalizedSourceStartPoint.{uR, uS, uMR, uMS, uNR, uNS} f)

end AlgebraicKTheory.StableGL

end
