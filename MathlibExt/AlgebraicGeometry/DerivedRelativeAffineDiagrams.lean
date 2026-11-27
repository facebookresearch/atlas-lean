/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NormalizedRelativeDeRham
public import MathlibExt.AlgebraicGeometry.DerivedProjectiveTensorDiagrams

/-!
# Full source relative de Rham diagrams

The source is the actual product of the two cofibrant affine algebras.
Its forms, algebra maps and graded mixed maps are normalized on the
native simplicial generators. Every product-resolution comparison is
one natural transformation over all algebras.

The lifted relative projection is fixed in every weight by the actual
product projection, Moore–AW comparison, Q(B)→B coefficient map and
the canonical lifted cochain tensor map. Naturality is retained on the
whole tensor-family category, including its simplex maps.

Reference: PTVV arXiv:1111.3209v4, §2.1, pp.30–32.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedRelativeAffineDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedTensorAffineFamilies
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
open MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham
open MathlibExt.AlgebraicGeometry.NormalizedRelativeDeRham
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedProjectiveTensorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u
variable {k : Type u} [CommRing k]

/-- The actual product of the two source Q algebras. -/
def sourceProductFunctor (Q : AlgebraReplacementFunctor k) : (SAlg k × SAlg k) ⥤ SAlg k :=
  Q.functor.prod Q.functor ⋙ tensor (SAlg k)

/-- A product replacement comparison is natural over the entire algebra pair category. -/
structure ProductReplacementSystem (Q : AlgebraReplacementFunctor k) where
  comparison : sourceProductFunctor Q ⟶ tensor (SAlg k) ⋙ Q.functor
  square : ∀ A B : SAlg k,
    comparison.app (A, B) ≫ Q.augmentation.app (A ⊗ B) =
      Q.augmentation.app A ⊗ₘ Q.augmentation.app B
  cofibrant : ∀ A B : SAlg k, IsAlgebraCofibrant (Q.functor.obj A ⊗ Q.functor.obj B)
  weak : ∀ A B : SAlg k, AlgebraWeakEquivalence (comparison.app (A, B))

/-- The single-chart comparison is the restriction of that same natural source system. -/
def productReplacementAt {Q : AlgebraReplacementFunctor k} (R : ProductReplacementSystem Q)
    (A B : SAlg k) : ProductReplacement Q A B :=
  ⟨R.comparison.app (A, B), R.square A B, R.cofibrant A B, R.weak A B⟩

/-- The cochain lift uses the actual normalized monoidal tensor map, which is invertible. -/
structure StrongCochainLift (L : CochainLiftModel k) where
  tensor : letI := L.monoidal
    ∀ C D : Cochains k, IsIso (Functor.LaxMonoidal.μ (largeCochainLift k) C D)

/-- The inverse tensor comparison is the actual native lifted tensor map. -/
def liftedTensorIso {L : CochainLiftModel k} (S : StrongCochainLift L) (C D : Cochains k) :
    (largeCochainLift k).obj (C ⊗ D) ≅
      (largeCochainLift k).obj C ⊗ (largeCochainLift k).obj D := by
  letI := L.monoidal
  letI := S.tensor C D
  exact (asIso (Functor.LaxMonoidal.μ (largeCochainLift k) C D)).symm

/-- The Q(B) coefficient augmentation is the literal normalized algebra map. -/
def coefficientAugmentation (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k)
    (B : SAlg k) : normalizedCoefficient (Q.functor.obj B) ⟶ (N.functor.obj B).X :=
  normalizedMap (Q.augmentation.app B) ≫ (N.model B).complexIso.inv

/-- The native opposite coefficient Hom is the same lifted source algebra complex. -/
def coefficientLiftIso (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k) (B : SAlg k) :
    (largeCochainLift k).obj (N.functor.obj B).X ≅ affineCoefficient L N B := Iso.refl _

/-- Affine de Rham weights are transported through the same actual system object equality. -/
def affineWeightLiftIso {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    {L : CochainLiftModel k} (T : MixedLiftModel L) (A : SAlg k) (w : ℤ) :
    (largeCochainLift k).obj ((D.model A).graded.weight w) ≅
      (T.functor.obj (D.functor.obj A)).weight w :=
  eqToIso (congrArg (fun E : GradedMixed k => (largeCochainLift k).obj (E.weight w))
    (D.object_eq A)) ≪≫ (T.weight (D.functor.obj A) w).symm

/-- The actual lifted relative weight map, including the Q(B)→B coefficient map. -/
def liftedRelativeWeight {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    {L : CochainLiftModel k} (T : MixedLiftModel L) (S : StrongCochainLift L)
    (N : ShuffleAlgebraFunctor k) (A B : SAlg k)
    {M : SimplicialDRModel (Q.functor.obj A ⊗ Q.functor.obj B)}
    (E : RawDRModel (Q.functor.obj A ⊗ Q.functor.obj B) M)
    {F : ProjectionModel (Q.functor.obj A) (Q.functor.obj B) (D.forms A) M}
    {P : PureTensorModel (D.model A).graded (normalizedCoefficient (Q.functor.obj B))}
    (R : RelativeDRModel (rawOfAffine (D.model A)) E F P) (w : ℤ) :
    (T.functor.obj E.graded).weight w ⟶
      (T.functor.obj (D.functor.obj A)).weight w ⊗ affineCoefficient L N B :=
  (T.weight E.graded w).hom ≫ (largeCochainLift k).map (R.map.map w) ≫
    (largeCochainLift k).map (P.weightIso w).hom ≫
    (liftedTensorIso S ((D.model A).graded.weight w) (normalizedCoefficient (Q.functor.obj B))).hom ≫
    ((affineWeightLiftIso D T A w).hom ⊗ₘ
      ((largeCochainLift k).map (coefficientAugmentation Q N B) ≫ (coefficientLiftIso L N B).hom))

/-- The actual first and second coefficient algebra functors of tensor families. -/
def firstAlgebra (F X : Prestack k) := first F X ⋙ algebraProjection F
def secondAlgebra (F X : Prestack k) := second F X ⋙ algebraProjection X

/-- The full raw product forms and comparison diagrams, all generator-normalized. -/
structure RelativeAffineFamilyDiagram {Q : AlgebraReplacementFunctor k}
    (D : AffineDRSystem Q) (R : ProductReplacementSystem Q) (F X : Prestack k) where
  forms : ∀ j : TensorFamilies F X, SimplicialDRModel
    (Q.functor.obj ((firstAlgebra F X).obj j) ⊗ Q.functor.obj ((secondAlgebra F X).obj j))
  model : ∀ j : TensorFamilies F X, RawDRModel _ (forms j)
  diagram : TensorFamilies F X ⥤ GradedMixed k
  object : ∀ j : TensorFamilies F X, diagram.obj j = (model j).graded
  simplicialMap : ∀ (j l : TensorFamilies F X) (f : j ⟶ l),
    SimplicialDRMap (forms j) (forms l)
      (Q.functor.map ((firstAlgebra F X).map f) ⊗ₘ Q.functor.map ((secondAlgebra F X).map f))
  mapModel : ∀ (j l : TensorFamilies F X) (f : j ⟶ l),
    RawDRMap (model j) (model l) _ (simplicialMap j l f)
  map : ∀ (j l : TensorFamilies F X) (f : j ⟶ l),
    HEq (diagram.map f) (mapModel j l f).map
  comparisonForms : ∀ j : TensorFamilies F X,
    SimplicialDRMap (forms j) (D.forms ((firstAlgebra F X).obj j ⊗ (secondAlgebra F X).obj j))
      (R.comparison.app ((firstAlgebra F X).obj j, (secondAlgebra F X).obj j))
  comparisonModel : ∀ j : TensorFamilies F X,
    RawDRMap (model j)
      (rawOfAffine (D.model ((firstAlgebra F X).obj j ⊗ (secondAlgebra F X).obj j))) _
      (comparisonForms j)
  comparison : diagram ⟶ product F X ⋙ algebraProjection (F ⊗ X) ⋙ D.functor
  comparison_eq : ∀ j : TensorFamilies F X,
    HEq (comparison.app j) (comparisonModel j).map
  projection : ∀ j : TensorFamilies F X,
    ProjectionModel (Q.functor.obj ((firstAlgebra F X).obj j))
      (Q.functor.obj ((secondAlgebra F X).obj j)) (D.forms ((firstAlgebra F X).obj j)) (forms j)
  tensor : ∀ j : TensorFamilies F X, PureTensorModel (D.model ((firstAlgebra F X).obj j)).graded
    (normalizedCoefficient (Q.functor.obj ((secondAlgebra F X).obj j)))
  relative : ∀ j : TensorFamilies F X,
    RelativeDRModel (rawOfAffine (D.model ((firstAlgebra F X).obj j)))
      (model j) (projection j) (tensor j)

/-- The actual lifted relative family map, fixed on all raw de Rham weights and coefficients. -/
structure LiftedRelativeFamilyDiagram {Q : AlgebraReplacementFunctor k}
    (D : AffineDRSystem Q) (R : ProductReplacementSystem Q) {L : CochainLiftModel k}
    (T : MixedLiftModel L) (S : StrongCochainLift L) (N : ShuffleAlgebraFunctor k)
    (F X : Prestack k) (A : RelativeAffineFamilyDiagram D R F X)
    (C : Families X ⥤ Cochains (LargeScalar k))
    (value : ∀ j : Families X, C.obj j = affineCoefficient L N ((algebraProjection X).obj j))
    (B : TensorMixedDiagram (first F X ⋙ algebraProjection F ⋙ D.functor ⋙ T.functor)
      (second F X ⋙ C)) where
  map : A.diagram ⋙ T.functor ⟶ B.diagram
  normalized : ∀ (j : TensorFamilies F X) (w : ℤ),
    (map.app j).map w ≫ (pureWeightComparison (B.diagram.obj j) (B.model j) (B.object j) w).hom =
      eqToHom (congrArg (fun E : GradedMixed k => (T.functor.obj E).weight w) (A.object j)) ≫
        liftedRelativeWeight D T S N ((firstAlgebra F X).obj j) ((secondAlgebra F X).obj j)
          (A.model j) (A.relative j) w ≫
        (𝟙 ((T.functor.obj (D.functor.obj ((firstAlgebra F X).obj j))).weight w) ⊗ₘ
          eqToHom (value ((second F X).obj j)).symm)

/-- Only native functor reassociation occurs in the product diagram universe lift. -/
def productLiftIso {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    {L : CochainLiftModel k} (T : MixedLiftModel L) (F X : Prestack k) :
    (product F X ⋙ algebraProjection (F ⊗ X) ⋙ D.functor) ⋙ T.functor ≅
      product F X ⋙ mixedDiagram D T (F ⊗ X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The full source product comparison is computed through the actual mixed augmentation. -/
def liftedProductComparison {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {R : ProductReplacementSystem Q} {L : CochainLiftModel k} {T : MixedLiftModel L}
    {F X : Prestack k} (A : RelativeAffineFamilyDiagram D R F X)
    (G : GlobalMixedModel D T (F ⊗ X)) :
    A.diagram ⋙ T.functor ⟶ product F X ⋙ G.replacement.diagram :=
  Functor.whiskerRight A.comparison T.functor ≫ (productLiftIso D T F X).hom ≫
    Functor.whiskerLeft (product F X) G.replacement.augmentation

end MathlibExt.AlgebraicGeometry.DerivedRelativeAffineDiagrams
