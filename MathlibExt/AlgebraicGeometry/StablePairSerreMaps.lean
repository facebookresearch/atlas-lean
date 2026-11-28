/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairCanonicalSources
public import MathlibExt.AlgebraicGeometry.StablePairTraceDualityModels

/-!
# Source-normalized projection formula and Serre adjunction maps

The ordinary projection formula is fixed on all tensor summands by
its native module adjunction mate. The derived comparison commutes
with those maps and the native units/counits on every representative.
The Serre coefficient map is the actual proper-QCoh adjunction
transpose of projection-formula inverse, canonical trace and unitor.

The tensor shift comparison fixes every summand of the degree-two
shift using the actual symmetry map. Direct-image shifts are normalized
by the native cochain unit diagram.

Reference: Pandharipande–Thomas, arXiv:0707.2348v5, (2.13);
Huybrechts–Thomas, arXiv:0805.3527v2, (4.2); Stacks 08EU, 0A9Y.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairSerreMaps

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open FourierMukai CoherentCurveLinearSeries LineBundleTaskContracts
open NormalizedModuleTensorMaps StablePairCochainTensorMaps StablePairFourierMukaiAtiyah
open QuasicoherentDualityReferences StablePairCanonicalSources
open ModuleDerivedSquares
attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme}

/-- The ordinary projection formula is fixed on every pair of degrees. -/
structure ProjectionFormulaCochainMap (f : Y ⟶ X) (T : PullbackTensor f)
    (M : Cochains Y) (L : Cochains X) where
  map : (cochainTensor X).obj ((cochainPushforward f).obj M,L) ⟶
    (cochainPushforward f).obj ((cochainTensor Y).obj (M,(cochainPullback f).obj L))
  normalized : ∀ (i j n : ℤ) (h : i+j=n),
    tensorInsertion ((cochainPushforward f).obj M) L i j n h ≫ map.f n =
      projectionFormulaMap f T (M.X i) (L.X j) ≫
        (Scheme.Modules.pushforward f).map
          (tensorInsertion M ((cochainPullback f).obj L) i j n h)

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]

/-- The ordinary pullback/tensor map is fixed on every totalization summand. -/
structure PullbackTensorCochainMap (f : Y ⟶ X) (T : PullbackTensor f)
    (M L : Cochains X) where
  map : (cochainPullback f).obj ((cochainTensor X).obj (M,L)) ⟶
    (cochainTensor Y).obj ((cochainPullback f).obj M,(cochainPullback f).obj L)
  normalized : ∀ (i j n : ℤ) (h : i+j=n),
    (Scheme.Modules.pullback f).map (tensorInsertion M L i j n h) ≫ map.f n =
      (T.comparison (M.X i) (L.X j)).hom ≫
        tensorInsertion ((cochainPullback f).obj M) ((cochainPullback f).obj L) i j n h

/-- Derived monoidality is fixed by every native cochain tensor and pullback counit. -/
structure DerivedPullbackTensor (f : Y ⟶ X) (T : PullbackTensor f) where
  map : ∀ (M L : D X),
    (derivedPullback f).obj ((derivedTensorUncurried X).obj (M,L)) ⟶
      (derivedTensorUncurried Y).obj ((derivedPullback f).obj M,(derivedPullback f).obj L)
  naturality : ∀ {M N L K : D X} (a : M ⟶ N) (b : L ⟶ K),
    (derivedPullback f).map ((derivedTensorUncurried X).map (a,b)) ≫ map N K =
      map M L ≫ (derivedTensorUncurried Y).map
        ((derivedPullback f).map a,(derivedPullback f).map b)
  cochain : ∀ (M L : Cochains X), PullbackTensorCochainMap f T M L
  normalized : ∀ (M L : Cochains X),
    (derivedPullback f).map (tensorCounit X M L) ≫
        pullbackCounit f ((cochainTensor X).obj (M,L)) ≫
          DerivedCategory.Q.map (cochain M L).map =
      map (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj L) ≫
        (derivedTensorUncurried Y).map (pullbackCounit f M,pullbackCounit f L) ≫
          tensorCounit Y ((cochainPullback f).obj M) ((cochainPullback f).obj L)

/-- The derived projection formula is the actual native pull/push adjunction mate. -/
def derivedProjectionMate (f : Y ⟶ X) {T : PullbackTensor f}
    (A : PullPushAdjunction f) (B : DerivedPullbackTensor f T) (M : D Y) (L : D X) :
    (derivedTensorUncurried X).obj ((derivedPushforward f).obj M,L) ⟶
      (derivedPushforward f).obj
        ((derivedTensorUncurried Y).obj (M,(derivedPullback f).obj L)) :=
  (A.adjunction.homEquiv _ _)
    (B.map ((derivedPushforward f).obj M) L ≫
      (derivedTensorUncurried Y).map
        (A.adjunction.counit.app M,𝟙 ((derivedPullback f).obj L)))

/-- The actual derived projection formula is fixed by all ordinary comparison diagrams. -/
structure DerivedProjectionFormula (f : Y ⟶ X) (T : PullbackTensor f) where
  adjunction : PullPushAdjunction f
  tensorPullback : DerivedPullbackTensor f T
  cochain : ∀ (M : Cochains Y) (L : Cochains X), ProjectionFormulaCochainMap f T M L
  normalized : ∀ (M : Cochains Y) (L : Cochains X),
    (derivedTensorUncurried X).map (pushforwardUnit f M,𝟙 (DerivedCategory.Q.obj L)) ≫
        derivedProjectionMate f adjunction tensorPullback
          (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj L) ≫
        (derivedPushforward f).map
          ((derivedTensorUncurried Y).map
              (𝟙 (DerivedCategory.Q.obj M),pullbackCounit f L) ≫
            tensorCounit Y M ((cochainPullback f).obj L)) =
      tensorCounit X ((cochainPushforward f).obj M) L ≫
        DerivedCategory.Q.map (cochain M L).map ≫
          pushforwardUnit f ((cochainTensor Y).obj (M,(cochainPullback f).obj L))

/-- The packet's projection map has the native adjunction-mate body. -/
def DerivedProjectionFormula.map {f : Y ⟶ X} {T : PullbackTensor f}
    (P : DerivedProjectionFormula f T) (M : D Y) (L : D X) :=
  derivedProjectionMate f P.adjunction P.tensorPullback M L

/-- The genuine cochain left unitor is fixed in every degree. -/
structure LeftUnitCochainMap (L : Cochains X) where
  map : (cochainTensor X).obj
    ((CochainComplex.singleFunctor X.Modules 0).obj (structureModule X),L) ⟶ L
  normalized : ∀ i : ℤ,
    tensorInsertion ((CochainComplex.singleFunctor X.Modules 0).obj (structureModule X))
        L 0 i i (by simp) ≫ map.f i =
      tensorMap (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (structureModule X)).hom
        (𝟙 (L.X i)) ≫ leftUnitMap X (L.X i)

/-- The tensor shift comparison retains every summand and the actual symmetry sign. -/
structure CochainTwistShiftMap (K : Cochains Y) (ω : Y.Modules) where
  map : ((cochainTensor Y).obj
      (K,(CochainComplex.singleFunctor Y.Modules 0).obj ω))⟦(2 : ℤ)⟧ ⟶
    (cochainTensor Y).obj
      (((CochainComplex.singleFunctor Y.Modules 0).obj ω)⟦(3 : ℤ)⟧,K⟦(-1 : ℤ)⟧)
  normalized : ∀ i : ℤ,
    tensorInsertion K ((CochainComplex.singleFunctor Y.Modules 0).obj ω)
        i 0 i (by simp) ≫
      (((cochainTensor Y).obj
        (K,(CochainComplex.singleFunctor Y.Modules 0).obj ω)).shiftFunctorObjXIso
          2 (i-2) i (by omega)).inv ≫ map.f (i-2) =
      symmetryMap Y (K.X i) (((CochainComplex.singleFunctor Y.Modules 0).obj ω).X 0) ≫
        tensorMap
          ((((CochainComplex.singleFunctor Y.Modules 0).obj ω).shiftFunctorObjXIso
            3 (-3) 0 (by omega)).inv)
          ((K.shiftFunctorObjXIso (-1) (i+1) i (by omega)).inv) ≫
        tensorInsertion
          (((CochainComplex.singleFunctor Y.Modules 0).obj ω)⟦(3 : ℤ)⟧)
          (K⟦(-1 : ℤ)⟧) (-3) (i+1) (i-2) (by omega)

/-- The derived tensor shift map is assembled from the native tensor and localization counits. -/
def twistShiftMap (K : Cochains Y) (ω : Y.Modules) (C : CochainTwistShiftMap K ω)
    (ht : IsIso (tensorCounit Y
      (((CochainComplex.singleFunctor Y.Modules 0).obj ω)⟦(3 : ℤ)⟧)
      (K⟦(-1 : ℤ)⟧))) :
    ((derivedTensorUncurried Y).obj
      (DerivedCategory.Q.obj K,
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor Y.Modules 0).obj ω)))⟦(2 : ℤ)⟧ ⟶
      (derivedTensorUncurried Y).obj
        (DerivedCategory.Q.obj (((CochainComplex.singleFunctor Y.Modules 0).obj ω)⟦(3 : ℤ)⟧),
          DerivedCategory.Q.obj (K⟦(-1 : ℤ)⟧)) := by
  letI := ht
  exact (tensorCounit Y K ((CochainComplex.singleFunctor Y.Modules 0).obj ω))⟦(2 : ℤ)⟧' ≫
    (DerivedCategory.Q.commShiftIso (2 : ℤ)).inv.app
      ((cochainTensor Y).obj (K,(CochainComplex.singleFunctor Y.Modules 0).obj ω)) ≫
      DerivedCategory.Q.map C.map ≫
        inv (tensorCounit Y (((CochainComplex.singleFunctor Y.Modules 0).obj ω)⟦(3 : ℤ)⟧)
          (K⟦(-1 : ℤ)⟧))

/-- A direct-image shift is fixed by its native unit diagram for every cochain and shift. -/
structure PushforwardShift (f : Y ⟶ X) where
  shift : (derivedPushforward f).CommShift ℤ
  normalized : letI := shift
    ∀ (m : ℤ) (K : Cochains Y),
      pushforwardUnit f (K⟦m⟧) ≫
          (derivedPushforward f).map ((DerivedCategory.Q.commShiftIso m).hom.app K) ≫
          ((derivedPushforward f).commShiftIso m).hom.app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map (((cochainPushforward f).commShiftIso m).hom.app K) ≫
          (DerivedCategory.Q.commShiftIso m).hom.app ((cochainPushforward f).obj K) ≫
            (pushforwardUnit f K)⟦m⟧'

/-- The coefficient trace is the actual projection-formula inverse, canonical trace and unitor. -/
def coefficientTrace {f : Y ⟶ X} (P : ProperReference f) (ω : Cochains Y)
    (w : DerivedCategory.Q.obj ω ⟶ properDuality P) (L : Cochains X)
    (T : PullbackTensor f) (J : DerivedProjectionFormula f T) (U : LeftUnitCochainMap L)
    (hJ : IsIso (J.map (DerivedCategory.Q.obj ω) (DerivedCategory.Q.obj L))) :
    (derivedPushforward f).obj
      ((derivedTensorUncurried Y).obj
        (DerivedCategory.Q.obj ω,(derivedPullback f).obj (DerivedCategory.Q.obj L))) ⟶
      DerivedCategory.Q.obj L := by
  letI := hJ
  exact inv (J.map (DerivedCategory.Q.obj ω) (DerivedCategory.Q.obj L)) ≫
    (derivedTensorUncurried X).map
      ((derivedPushforward f).map w ≫ properTrace P,𝟙 (DerivedCategory.Q.obj L)) ≫
    tensorCounit X ((CochainComplex.singleFunctor X.Modules 0).obj (structureModule X)) L ≫
      DerivedCategory.Q.map U.map

/-- The Serre coefficient map is the fixed proper-QCoh adjunction transpose of that trace. -/
def serreCoefficient {f : Y ⟶ X} (P : ProperReference f) (ω : Cochains Y)
    (w : DerivedCategory.Q.obj ω ⟶ properDuality P) (L : Cochains X)
    (T : PullbackTensor f) (J : DerivedProjectionFormula f T) (U : LeftUnitCochainMap L)
    (hJ : IsIso (J.map (DerivedCategory.Q.obj ω) (DerivedCategory.Q.obj L)))
    (hSource : quasicoherent Y ((derivedTensorUncurried Y).obj
      (DerivedCategory.Q.obj ω, (derivedPullback f).obj (DerivedCategory.Q.obj L))))
    (hTarget : quasicoherent X (DerivedCategory.Q.obj L)) : letI := P.adjoint
    (derivedTensorUncurried Y).obj
        (DerivedCategory.Q.obj ω,(derivedPullback f).obj (DerivedCategory.Q.obj L)) ⟶
      ((directImage f P.preservation).rightAdjoint.obj
        (⟨DerivedCategory.Q.obj L,hTarget⟩ : QCohDerived X)).obj := by
  letI := P.adjoint
  let s : QCohDerived Y := ⟨_,hSource⟩
  let l : QCohDerived X := ⟨_,hTarget⟩
  exact (((Adjunction.ofIsLeftAdjoint (directImage f P.preservation)).homEquiv s l)
    (ObjectProperty.homMk (coefficientTrace P ω w L T J U hJ))).hom

end MathlibExt.AlgebraicGeometry.StablePairSerreMaps
