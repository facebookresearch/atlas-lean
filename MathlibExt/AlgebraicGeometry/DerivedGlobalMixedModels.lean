/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
public import MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
public import MathlibExt.AlgebraicGeometry.WeightedNCIntegration

/-!
# Actual global graded mixed and weighted NC models

The affine mixed structure is lifted with every coefficient and epsilon
component fixed. Replacement is in the whole category of graded mixed
diagrams, and each global weight is the native limit of that diagram.
Its epsilon is fixed by every affine projection.

Weighted NC comparison retains every product closing coefficient and
the entire actual augmentation square. The comparison with the global
NC complex is the literal native limit lift through that square.
No independently chosen global closed-form complex is introduced.

References: PTVV arXiv:1111.3209v4, §1.1 and §2.1; Bousfield–Kan,
Chapters X–XI. Generic model assembly/proofs are separate Wanted inputs.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open CochainComplex.HomComplex
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry

universe u
variable {k : Type u} [CommRing k]

/-- The global module carrier already has the required universe; only the
actual transported scalar action changes. -/
def globalToCoefficients (k : Type u) [CommRing k] : GlobalComplex k ⥤ Cochains (LargeScalar k) :=
  (ModuleCat.restrictScalars (ULift.ringEquiv : LargeScalar k ≃+* k).toRingHom).mapHomologicalComplex
    (.up ℤ)

/-- The entire mixed-complex universe lift is fixed by the actual coefficient lift. -/
structure MixedLiftModel (L : CochainLiftModel k) where
  functor : GradedMixed k ⥤ GradedMixed (LargeScalar k)
  weight : ∀ (E : GradedMixed k) (w : ℤ),
    (functor.obj E).weight w ≅ (largeCochainLift k).obj (E.weight w)
  map : ∀ (E F : GradedMixed k) (f : MixedMap E F) (w : ℤ),
    (functor.map f).map w ≫ (weight F w).hom =
      (weight E w).hom ≫ (largeCochainLift k).map (f.map w)
  epsilon : ∀ (E : GradedMixed k) (w i : ℤ) (a : (E.weight w).X i),
    ((weight E (w + 1)).hom.f (i - 1)).hom
      ((((functor.obj E).epsilon w).v i (i - 1) (by omega)).hom
        (((weight E w).inv.f i).hom (ULift.up a))) =
      ULift.up (((E.epsilon w).v i (i - 1) (by omega)).hom a)

/-- The genuine lifting property of a whole mixed diagram, retaining all weights and epsilon. -/
structure MixedDiagramReplacement {J : Type (u + 1)} [Category.{u} J]
    (D : J ⥤ GradedMixed (LargeScalar k)) where
  diagram : J ⥤ GradedMixed (LargeScalar k)
  augmentation : D ⟶ diagram
  mono : ∀ (j : J) (w : ℤ), Mono ((augmentation.app j).map w)
  weak : ∀ (j : J) (w : ℤ), QuasiIso ((augmentation.app j).map w)
  fibrant : ∀ (A B : J ⥤ GradedMixed (LargeScalar k)) (i : A ⟶ B),
    (∀ (j : J) (w : ℤ), Mono ((i.app j).map w) ∧ QuasiIso ((i.app j).map w)) →
      ∀ f : A ⟶ diagram, ∃ g : B ⟶ diagram, i ≫ g = f

/-- The exact larger-universe affine mixed diagram. -/
def mixedDiagram {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    {L : CochainLiftModel k} (T : MixedLiftModel L) (X : Prestack k) :
    Families X ⥤ GradedMixed (LargeScalar k) := algebraProjection X ⋙ D.functor ⋙ T.functor

/-- Global mixed weights and epsilon are the actual full replacement limits. -/
structure GlobalMixedModel {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    {L : CochainLiftModel k} (T : MixedLiftModel L) (X : Prestack k) where
  replacement : MixedDiagramReplacement (mixedDiagram D T X)
  mixed : GradedMixed (LargeScalar k)
  weight : ∀ w : ℤ,
    mixed.weight w ≅ limit (replacement.diagram ⋙ weightFunctor w)
  epsilon : ∀ (w i : ℤ) (j : Families X),
    (mixed.epsilon w).v i (i - 1) (by omega) ≫
      ((weight (w + 1)).hom ≫ limit.π (replacement.diagram ⋙ weightFunctor (w + 1)) j).f (i - 1) =
    ((weight w).hom ≫ limit.π (replacement.diagram ⋙ weightFunctor w) j).f i ≫
      ((replacement.diagram.obj j).epsilon w).v i (i - 1) (by omega)

/-- The actual global mixed cone is computed from the native weight-limit projections. -/
def globalMixedCone {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {T : MixedLiftModel L} {X : Prestack k}
    (G : GlobalMixedModel D T X) :
    (Functor.const (Families X)).obj G.mixed ⟶ G.replacement.diagram where
  app j :=
    { map w := (G.weight w).hom ≫ limit.π (G.replacement.diagram ⋙ weightFunctor w) j
      epsilon w a b h := by
        obtain rfl : b = a - 1 := by omega
        exact G.epsilon w a j }
  naturality j l f := by
    apply mixedMap_ext
    intro w
    change 𝟙 (G.mixed.weight w) ≫
      ((G.weight w).hom ≫ limit.π (G.replacement.diagram ⋙ weightFunctor w) l) =
        ((G.weight w).hom ≫ limit.π (G.replacement.diagram ⋙ weightFunctor w) j) ≫
          (G.replacement.diagram ⋙ weightFunctor w).map f
    simpa only [Category.id_comp, Category.assoc] using
      congrArg (fun a => (G.weight w).hom ≫ a)
        (limit.w (G.replacement.diagram ⋙ weightFunctor w) f).symm

/-- Actual mixed pullback uses the whole reindexed augmentation square.
Its weight maps are fixed by every native affine-family projection. -/
structure MixedPullbackModel {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {T : MixedLiftModel L} {X Y : Prestack k}
    (f : X ⟶ Y) (GY : GlobalMixedModel D T Y) (GX : GlobalMixedModel D T X) where
  comparison : reindex f ⋙ GY.replacement.diagram ⟶ GX.replacement.diagram
  square : HEq (Functor.whiskerLeft (reindex f) GY.replacement.augmentation ≫ comparison)
    GX.replacement.augmentation
  map : MixedMap GY.mixed GX.mixed
  normalized : ∀ (j : Families X) (w : ℤ),
    map.map w ≫ ((globalMixedCone GX).app j).map w =
      ((globalMixedCone GY).app ((reindex f).obj j)).map w ≫ (comparison.app j).map w

/-- The lifted affine NC comparison keeps every closing coefficient. -/
structure LiftedNCDiagram {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    {L : CochainLiftModel k} (T : MixedLiftModel L) (p : ℕ)
    (N : NegativeCyclicDiagram D.functor (p : ℤ)) where
  diagram : NegativeCyclicDiagram (D.functor ⋙ T.functor) (p : ℤ)
  comparison : N.complex ⋙ largeCochainLift k ⟶ diagram.complex
  normalized : ∀ (A : SAlg k) (n : ℤ) (x : (N.complex.obj A).X n) (i : ℕ),
    (((T.weight (D.functor.obj A) ((p : ℤ) + (i : ℤ))).hom.f (n - 2 * (i : ℤ))).hom
      ((diagram.termIso A n).hom (((comparison.app A).f n).hom (ULift.up x)) i)) =
      ULift.up ((N.termIso A n).hom x i)

/-- Whole native NC augmentation and its injective cochain target. -/
structure ReplacementNCDiagram {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {T : MixedLiftModel L} {p : ℕ}
    {N : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (G : GlobalMixedModel D T X) (B : LiftedNCDiagram D T p N) where
  diagram : NegativeCyclicDiagram G.replacement.diagram (p : ℤ)
  augmentation : algebraProjection X ⋙ B.diagram.complex ⟶ diagram.complex
  normalized : ∀ j : Families X,
    IsNegativeCyclicMap (G.replacement.augmentation.app j) (p : ℤ)
      (B.diagram.toModel ((algebraProjection X).obj j)) (diagram.toModel j) (augmentation.app j)
  mono : ∀ j : Families X, Mono (augmentation.app j)
  weak : ∀ j : Families X, QuasiIso (augmentation.app j)
  fibrant : IsInjectivelyFibrant diagram.complex

/-- NC of the actual mixed limit agrees with the actual NC-diagram limit
on every closing coefficient and affine projection. -/
structure MixedLimitNC {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {T : MixedLiftModel L} {p : ℕ}
    {N : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    {G : GlobalMixedModel D T X} {B : LiftedNCDiagram D T p N}
    (I : ReplacementNCDiagram G B) where
  model : NegativeCyclicModel G.mixed (p : ℤ)
  comparison : model.complex ≅ limit I.diagram.complex
  normalized : ∀ (n : ℤ) (x : model.complex.X n) (i : ℕ) (j : Families X),
    (I.diagram.termIso j n).hom
        ((limit.π I.diagram.complex j).f n ((comparison.hom.f n).hom x)) i =
      ((limit.π (G.replacement.diagram ⋙ weightFunctor ((p : ℤ) + (i : ℤ))) j).f
        (n - 2 * (i : ℤ))).hom
          (((G.weight ((p : ℤ) + (i : ℤ))).hom.f (n - 2 * (i : ℤ))).hom
            ((model.termIso n).hom x i))

/-- Reassociation retains the literal lifted NC coefficients and every map. -/
def sourceNCIso {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q) (p : ℕ)
    (N : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k) :
    ncDiagram D p N X ⋙ globalToCoefficients k ≅
      algebraProjection X ⋙ (N.complex ⋙ largeCochainLift k) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The source NC lift is one entire augmentation square, retaining all family simplices. -/
structure GlobalNCLift {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {T : MixedLiftModel L} {p : ℕ}
    {N : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    {G : GlobalMixedModel D T X} {B : LiftedNCDiagram D T p N}
    (I : ReplacementNCDiagram G B) (F : GlobalNCModel D p N X) where
  map : F.closed.diagram ⋙ globalToCoefficients k ⟶ I.diagram.complex
  square : Functor.whiskerRight F.closed.map (globalToCoefficients k) ≫ map =
    (sourceNCIso D p N X).hom ≫
      Functor.whiskerLeft (algebraProjection X) B.comparison ≫ I.augmentation

/-- The actual native cochain comparison is computed by limit functoriality. -/
def globalNCComparison {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {T : MixedLiftModel L} {p : ℕ}
    {N : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    {G : GlobalMixedModel D T X} {B : LiftedNCDiagram D T p N}
    {I : ReplacementNCDiagram G B} (H : MixedLimitNC I) {F : GlobalNCModel D p N X}
    (A : GlobalNCLift I F) : (globalToCoefficients k).obj (ncComplex F) ⟶ H.model.complex :=
  limit.lift I.diagram.complex
    ((Cone.postcompose A.map).obj
      ((globalToCoefficients k).mapCone (limit.cone F.closed.diagram))) ≫ H.comparison.inv

end MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
