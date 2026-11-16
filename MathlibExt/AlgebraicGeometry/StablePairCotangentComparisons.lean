/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairCotangentTruncations
public import MathlibExt.AlgebraicGeometry.StablePairAtiyahKernels
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory

/-!
# Generator and refinement normalization of the diagonal cotangent target

Ambient rings are actual affine sections of the specified scheme
embedding. Diagonal generators are lifts of p₂*f-p₁*f in the actual
diagonal ideal; relations use the actual restricted ideal kernel.
Their cotangent coordinates fix both nonzero degrees, including the
negative conormal sign caused by the native shift. The full polynomial
bar comparison is an equality of cochain maps on every chart.

References: Huybrechts–Thomas, arXiv:0805.3527v2, §2.1–2.2,
especially the generator calculation following (2.6); Stacks 08QI.
The global cotangent constructor is source-completed; only its bridge
to this diagonal presentation is requested separately.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairCotangentComparisons

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GlobalPerfectObstructionTheory GeometricCotangentComplex
open StablePairDiagonalIdeals StablePairAtiyahKernels StablePairCotangentTruncations
open CoherentCurveLinearSeries GenericSectionMaps
open scoped TensorProduct

variable {Y Z : Over (Spec (.of ℂ))} (i : Y ⟶ Z)

/-- Actual affine ambient sections over a cotangent source chart. -/
structure EmbeddingChart (a : AffineChart Y.hom) where
  ambient : Z.left.Opens
  affine : IsAffineOpen ambient
  over : a.source ≤ i.left ⁻¹ᵁ ambient
  baseOver : ambient ≤ Z.hom ⁻¹ᵁ a.target
  scalar : ∀ x : a.base,
    (i.left.appLE ambient a.source over).hom
      ((Z.hom.appLE a.target ambient baseOver).hom x) =
        (Y.hom.appLE a.target a.source a.over).hom x
  surjective : Function.Surjective (i.left.appLE ambient a.source over).hom

namespace EmbeddingChart
variable {i} {a : AffineChart Y.hom} (c : EmbeddingChart i a)

instance : Algebra a.base Γ(Z.left,c.ambient) :=
  (Z.hom.appLE a.target c.ambient c.baseOver).hom.toAlgebra

/-- The actual restriction ring map, read as the compatible algebra homomorphism. -/
def restrictionAlgHom : Γ(Z.left,c.ambient) →ₐ[a.base] a.ring where
  toRingHom := (i.left.appLE c.ambient a.source c.over).hom
  commutes' := c.scalar

/-- The extension ring is literally the chosen ambient affine ring. -/
def extension : Algebra.Extension.{0} a.base a.ring :=
  Algebra.Extension.ofSurjective c.restrictionAlgHom c.surjective
end EmbeddingChart

/-- Pull an actual scalar section by the native module pullback and structure-unit comparison. -/
def ringPullback {A B : Scheme} (f : B ⟶ A) (V : A.Opens) (W : B.Opens)
    (h : W ≤ f ⁻¹ᵁ V) (x : Γ(A,V)) : Γ(B,W) :=
  ((SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom).val.app (op W)).hom
    (localPullbackSection f (structureModule A) V W h x)

/-- A diagonal-ideal section is fixed by its monomorphism into the structure sheaf. -/
structure DiagonalDifference (V : Z.left.Opens) (W : (pullback Z.hom Z.hom).Opens)
    (h₁ : W ≤ pullback.fst Z.hom Z.hom ⁻¹ᵁ V)
    (h₂ : W ≤ pullback.snd Z.hom Z.hom ⁻¹ᵁ V) (x : Γ(Z.left,V)) where
  element : Γ(ideal (diagonal Z),W)
  normalized : (idealInclusion (diagonal Z)).app W element =
    ringPullback (pullback.snd Z.hom Z.hom) V W h₂ x -
      ringPullback (pullback.fst Z.hom Z.hom) V W h₁ x

variable (S : IdealSquare (diagonal Z))

/-- The actual ambient differential generator in cotangent degree zero. -/
def quotientGenerator {a : AffineChart Y.hom} (c : EmbeddingChart i a)
    (W : (pullback Z.hom Z.hom).Opens)
    (h : a.source ≤ (diagonal Y ≫ productEmbedding i) ⁻¹ᵁ W)
    {h₁ : W ≤ pullback.fst Z.hom Z.hom ⁻¹ᵁ c.ambient}
    {h₂ : W ≤ pullback.snd Z.hom Z.hom ⁻¹ᵁ c.ambient}
    {x : Γ(Z.left,c.ambient)} (D : DiagonalDifference c.ambient W h₁ h₂ x) :
    Γ((cotangent i S).X 0,a.source) :=
  ((Scheme.Modules.pullbackComp (diagonal Y) (productEmbedding i)).inv.app
    (cokernel S.map)).app a.source
      (localPullbackSection (diagonal Y ≫ productEmbedding i) (cokernel S.map)
        W a.source h ((cokernel.π S.map).app W D.element))

/-- A source relation is the actual kernel lift of an ambient diagonal difference. -/
structure RelationGenerator {a : AffineChart Y.hom} (c : EmbeddingChart i a)
    (f : Γ(ideal i.left,c.ambient)) where
  ambientProduct : (pullback Z.hom Z.hom).Opens
  product : (pullback Y.hom Y.hom).Opens
  first : ambientProduct ≤ pullback.fst Z.hom Z.hom ⁻¹ᵁ c.ambient
  second : ambientProduct ≤ pullback.snd Z.hom Z.hom ⁻¹ᵁ c.ambient
  over : product ≤ productEmbedding i ⁻¹ᵁ ambientProduct
  diagonalOver : a.source ≤ diagonal Y ⁻¹ᵁ product
  difference : DiagonalDifference c.ambient ambientProduct first second
    ((idealInclusion i.left).app c.ambient f)
  element : Γ(diagonalKernel i,product)
  normalized : (kernel.ι (restrictedIdealMap i)).app product element =
    localPullbackSection (productEmbedding i) (ideal (diagonal Z))
      ambientProduct product over difference.element

/-- Pull the actual relation section to the diagonal, without a chosen conormal carrier. -/
def relationGenerator {a : AffineChart Y.hom} {c : EmbeddingChart i a}
    {f : Γ(ideal i.left,c.ambient)} (r : RelationGenerator i c f) :
    Γ((cotangent i S).X (-1),a.source) :=
  localPullbackSection (diagonal Y) (diagonalKernel i) r.product a.source
    r.diagonalOver r.element

def zeroProjection {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (P : Algebra.Extension.{0} k A) :
    (truncatedComplex P).X 0 ⟶ ModuleCat.of A P.CotangentSpace :=
  (CochainComplex.mappingCone.snd
      ((CochainComplex.singleFunctor (ModuleCat A) 0).map
        (ModuleCat.ofHom P.cotangentComplex))).v 0 0 (by omega) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A P.CotangentSpace)).hom

def negativeProjection {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (P : Algebra.Extension.{0} k A) :
    (truncatedComplex P).X (-1) ⟶ ModuleCat.of A P.Cotangent :=
  (CochainComplex.mappingCone.fst
      ((CochainComplex.singleFunctor (ModuleCat A) 0).map
        (ModuleCat.ofHom P.cotangentComplex))).val.v (-1) 0 (by omega) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A P.Cotangent)).hom

/-- Every coordinate is fixed on all actual diagonal and relation generators. -/
structure CotangentCoordinates {a : AffineChart Y.hom} (c : EmbeddingChart i a) where
  map : sectionsComplex (cotangent i S) a.source ⟶ truncatedComplex c.extension
  [quasiIso : QuasiIso map]
  zero_normalized : ∀ (x : Γ(Z.left,c.ambient))
    (W : (pullback Z.hom Z.hom).Opens)
    (h : a.source ≤ (diagonal Y ≫ productEmbedding i) ⁻¹ᵁ W)
    (h₁ : W ≤ pullback.fst Z.hom Z.hom ⁻¹ᵁ c.ambient)
    (h₂ : W ≤ pullback.snd Z.hom Z.hom ⁻¹ᵁ c.ambient)
    (D : DiagonalDifference c.ambient W h₁ h₂ x),
    (map.f 0 ≫ zeroProjection c.extension) (quotientGenerator i S c W h D) =
      (1 : a.ring) ⊗ₜ[c.extension.Ring]
        KaehlerDifferential.D a.base c.extension.Ring x
  negative_normalized : ∀ (f : Γ(ideal i.left,c.ambient))
    (r : RelationGenerator i c f)
    (hf : (idealInclusion i.left).app c.ambient f ∈ c.extension.ker),
    (map.f (-1) ≫ negativeProjection c.extension) (relationGenerator i S r) =
      -Algebra.Extension.Cotangent.mk ⟨(idealInclusion i.left).app c.ambient f,hf⟩

attribute [instance] CotangentCoordinates.quasiIso

/-- Full polynomial bar and refinement comparison for the native diagonal truncation. -/
structure CotangentTruncation (C : CotangentNormalization Y.hom) where
  projection : C.complex ⟶ cotangent i S
  lift : ∀ (a : AffineChart Y.hom) (c : EmbeddingChart i a),
    PolynomialLift c.extension (C.resolution a)
  bar : ∀ (a : AffineChart Y.hom) (c : EmbeddingChart i a),
    AffineTruncation c.extension (C.resolution a) (lift a c)
  coordinates : ∀ (a : AffineChart Y.hom) (c : EmbeddingChart i a),
    CotangentCoordinates i S c
  full_bar : ∀ (a : AffineChart Y.hom) (c : EmbeddingChart i a),
    C.comparison a ≫
      ((moduleSections a.source).mapHomologicalComplex (.up ℤ)).map projection ≫
        (coordinates a c).map = (bar a c).map
  refinement : ∀ (a b : AffineChart Y.hom)
    (_c : EmbeddingChart i a) (d : EmbeddingChart i b)
    (hU : b.source ≤ a.source) (hV : b.target ≤ a.target),
    C.comparison a ≫
        ((moduleSections a.source).mapHomologicalComplex (.up ℤ)).map projection ≫
          sectionRestriction (cotangent i S) hU ≫
          ((ModuleCat.restrictScalars
            (Y.left.presheaf.map (homOfLE hU).op).hom).mapHomologicalComplex
            (.up ℤ)).map (coordinates b d).map =
      (C.refinement a b hU hV).cotangentMap ≫
        ((ModuleCat.restrictScalars (Y.left.presheaf.map (homOfLE hU).op).hom).mapHomologicalComplex
          (.up ℤ)).map (bar b d).map

end MathlibExt.AlgebraicGeometry.StablePairCotangentComparisons
