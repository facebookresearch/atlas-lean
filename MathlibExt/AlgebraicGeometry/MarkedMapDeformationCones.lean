/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Full cotangent differential and marked-map deformation cone

A relative cotangent differential is fixed on every actual common affine
base chart by augmentation-preserving simplicial polynomial-resolution
maps and their pure differentials. This excludes an arbitrarily named
global cotangent arrow or independent overlap choices.

The marked map complex is the cone of
RHom(L_C/T,I_marks) → RHom(Lf*L_target/T,O_C). The arrow uses the
actual marking-ideal inclusion and the same normalized differential.
Its cochain representative is fixed by a quotient-map equation, and
the pushforward is the native Rπ_*.

Global cotangent functoriality and arbitrary-resolution comparisons are
completed AxiomMath/Stacks integration at
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Cotangent/SchemeCotangentComplex.lean and
ResolutionCotangentAny.lean (Apache 2.0); they are not re-requested.
Primary reference: Graber--Harris--Starr math/0109220v1, §2;
Behrend--Fantechi alg-geom/9601010, §4.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MarkedMapDeformationCones

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicTopology _root_.Simplicial
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
open MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes
open MathlibExt.AlgebraicGeometry.DerivedInternalHom
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.RationalResolution
attribute [local instance] HasDerivedCategory.standard

/-- Three actual affine opens over one actual affine base open. -/
structure CommonChart {X Y T : Scheme.{0}} (p : X ⟶ T) (q : Y ⟶ T) (f : X ⟶ Y) where
  base : T.Opens
  source : X.Opens
  target : Y.Opens
  base_affine : IsAffineOpen base
  source_affine : IsAffineOpen source
  target_affine : IsAffineOpen target
  source_over : source ≤ p ⁻¹ᵁ base
  target_over : target ≤ q ⁻¹ᵁ base
  map_over : source ≤ f ⁻¹ᵁ target

def CommonChart.sourceChart {X Y T : Scheme.{0}} {p : X ⟶ T} {q : Y ⟶ T} {f : X ⟶ Y}
    (a : CommonChart p q f) : AffineChart p :=
  ⟨a.source,a.base,a.source_affine,a.base_affine,a.source_over⟩

def CommonChart.targetChart {X Y T : Scheme.{0}} {p : X ⟶ T} {q : Y ⟶ T} {f : X ⟶ Y}
    (a : CommonChart p q f) : AffineChart q :=
  ⟨a.target,a.base,a.target_affine,a.base_affine,a.target_over⟩

/-- Literal maps of the actual relative polynomial resolutions on each common chart. -/
structure ResolutionMap {X Y T : Scheme.{0}} {p : X ⟶ T} {q : Y ⟶ T} {f : X ⟶ Y}
    (a : CommonChart p q f) (P : CotangentNormalization p) (Q : CotangentNormalization q) where
  map : ∀ n, (Q.resolution a.targetChart).algebra.obj n →+*
    (P.resolution a.sourceChart).algebra.obj n
  scalar : ∀ n (x : Γ(T,a.base)),
    map n (algebraMap Γ(T,a.base) ((Q.resolution a.targetChart).algebra.obj n) x) =
      algebraMap Γ(T,a.base) ((P.resolution a.sourceChart).algebra.obj n) x
  augmentation : ∀ n (x : (Q.resolution a.targetChart).algebra.obj n),
    (P.resolution a.sourceChart).augmentation.app n (map n x) =
      (f.appLE a.target a.source a.map_over).hom
        ((Q.resolution a.targetChart).augmentation.app n x)
  simplicial : ∀ {i j} (g : i ⟶ j) (x : (Q.resolution a.targetChart).algebra.obj i),
    map j ((Q.resolution a.targetChart).algebra.map g x) =
      (P.resolution a.sourceChart).algebra.map g (map i x)

/-- Native global differential fixed on every actual affine polynomial-resolution generator. -/
structure RelativeDifferential {X Y T : Scheme.{0}} {p : X ⟶ T} {q : Y ⟶ T}
    (f : X ⟶ Y) (comm : f ≫ q = p)
    (P : CotangentNormalization p) (Q : CotangentNormalization q) where
  map : ((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj Q.complex ⟶ P.complex
  resolution : ∀ a : CommonChart p q f, ResolutionMap a P Q
  normalized : ∀ (a : CommonChart p q f) (n : ℕ)
    (x : (Q.resolution a.targetChart).algebra.obj (op ⦋n⦌)),
    ((map.f (-(n : ℤ))).app a.source)
      (localPullbackSection f (Q.complex.X (-(n : ℤ))) a.target a.source a.map_over
        (((Q.comparison a.targetChart).f (-(n : ℤ)))
          ((affineDegreeIso (Q.resolution a.targetChart) n).inv
            (CommAlgCat.resolutionCotangentTermDifferential a.targetChart.base
              (CommAlgCat.of a.targetChart.base a.targetChart.ring)
              (Q.resolution a.targetChart).algebra (Q.resolution a.targetChart).augmentation
              (op ⦋n⦌) x)))) =
    ((P.comparison a.sourceChart).f (-(n : ℤ)))
      ((affineDegreeIso (P.resolution a.sourceChart) n).inv
        (CommAlgCat.resolutionCotangentTermDifferential a.sourceChart.base
          (CommAlgCat.of a.sourceChart.base a.sourceChart.ring)
          (P.resolution a.sourceChart).algebra (P.resolution a.sourceChart).augmentation
          (op ⦋n⦌) ((resolution a).map (op ⦋n⦌) x)))

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]

/-- The full derived differential uses the actual derived pullback counit and quotient map. -/
def RelativeDifferential.derived {X Y T : Scheme.{0}} {p : X ⟶ T} {q : Y ⟶ T}
    {f : X ⟶ Y} {comm : f ≫ q = p}
    {P : CotangentNormalization p} {Q : CotangentNormalization q}
    (D : RelativeDifferential f comm P Q) :
    (derivedPullback f).obj (DerivedCategory.Q.obj Q.complex) ⟶ DerivedCategory.Q.obj P.complex :=
  (derivedPullbackCounit f).app Q.complex ≫ DerivedCategory.Q.map D.map

/-- The actual ideal inclusion of all marked sections. -/
def markingInclusion {V S T : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} {b : T ⟶ S}
    (F : Family q n g T b) : markingIdeal F ⟶ structureModule F.curve.X :=
  kernel.ι (Pi.lift (fun i : Fin n => structureUnit (F.curve.marking i)))

/-- Actual marked tangent arrow, with source vector fields vanishing at the markings. -/
def markedArrow {V S T : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} {b : T ⟶ S}
    (F : Family q n g T b) (P : CotangentNormalization F.curve.π)
    (Q : CotangentNormalization (pullback.snd q b))
    (D : RelativeDifferential (mapToRelativeTarget F) (pullback.lift_snd _ _ _) P Q)
    [((derivedTensor F.curve.X).obj (DerivedCategory.Q.obj P.complex)).IsLeftAdjoint]
    [((derivedTensor F.curve.X).obj
      ((derivedPullback (mapToRelativeTarget F)).obj
        (DerivedCategory.Q.obj Q.complex))).IsLeftAdjoint] :
    internalHom F.curve.X (DerivedCategory.Q.obj P.complex)
      ((DerivedCategory.singleFunctor F.curve.X.Modules 0).obj (markingIdeal F)) ⟶
    internalHom F.curve.X
      ((derivedPullback (mapToRelativeTarget F)).obj (DerivedCategory.Q.obj Q.complex))
      (derivedUnit F.curve.X) :=
  (Functor.rightAdjoint ((derivedTensor F.curve.X).obj (DerivedCategory.Q.obj P.complex))).map
      ((DerivedCategory.singleFunctor F.curve.X.Modules 0).map (markingInclusion F)) ≫
    precomp D.derived (derivedUnit F.curve.X)

/-- Cochain cone representative fixed by the displayed actual derived arrow. -/
structure ConeModel {X : Scheme.{0}} {K L : D X} (a : K ⟶ L) where
  source : CochainComplex X.Modules ℤ
  target : CochainComplex X.Modules ℤ
  sourceIso : DerivedCategory.Q.obj source ≅ K
  targetIso : DerivedCategory.Q.obj target ≅ L
  map : source ⟶ target
  normalized : DerivedCategory.Q.map map = sourceIso.hom ≫ a ≫ targetIso.inv

/-- The actual marked map deformation object on the actual parameter scheme. -/
def markedDeformation {V S T : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} {b : T ⟶ S}
    (F : Family q n g T b) (P : CotangentNormalization F.curve.π)
    (Q : CotangentNormalization (pullback.snd q b))
    (D : RelativeDifferential (mapToRelativeTarget F) (pullback.lift_snd _ _ _) P Q)
    [((derivedTensor F.curve.X).obj (DerivedCategory.Q.obj P.complex)).IsLeftAdjoint]
    [((derivedTensor F.curve.X).obj
      ((derivedPullback (mapToRelativeTarget F)).obj
        (DerivedCategory.Q.obj Q.complex))).IsLeftAdjoint]
    (C : ConeModel (markedArrow F P Q D)) : FourierMukai.D T :=
  (derivedPushforward F.curve.π).obj
    (DerivedCategory.Q.obj (CochainComplex.mappingCone C.map))

end MathlibExt.AlgebraicGeometry.MarkedMapDeformationCones
