/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairFamilies
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import MathlibExt.AlgebraicGeometry.FourierMukai

/-!
# Product cotangent projection through the actual relative comparison

The absolute-to-relative map is fixed by augmentation-preserving maps
of the full polynomial resolutions. The product base-change map is
fixed on every differential generator and every scalar coefficient
by native parameter pullback. Both polynomial diagrams commute with
all refinements. The projection is their computed composite, with
native pullback/shift and derived-counit comparisons.

Reference: Pandharipande–Thomas, arXiv:0707.2348v5, (2.12)–(2.13);
Stacks 08T0–08T3, 08QI.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairProductCotangents

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
open _root_.AlgebraicGeometry
open StablePairFamilies GlobalPerfectObstructionTheory GeometricCotangentComplex
open FourierMukai GenericSectionMaps
attribute [local instance] HasDerivedCategory.standard

variable (X P : Over (Spec (.of ℂ)))

/-- The actual product with its complex structure map. -/
def product : Over (Spec (.of ℂ)) := Over.mk (pullback.fst X.hom P.hom ≫ X.hom)

abbrev cochainParameterPullback :=
  (Scheme.Modules.pullback (projection X P)).mapHomologicalComplex (.up ℤ)

/-- Compatible actual affine charts for the two factors and their product. -/
structure ProductChart (a : AffineChart (product X P).hom) where
  xOpen : X.left.Opens
  pOpen : P.left.Opens
  xAffine : IsAffineOpen xOpen
  pAffine : IsAffineOpen pOpen
  xBase : xOpen ≤ X.hom ⁻¹ᵁ a.target
  pBase : pOpen ≤ P.hom ⁻¹ᵁ a.target
  overX : a.source ≤ pullback.fst X.hom P.hom ⁻¹ᵁ xOpen
  overP : a.source ≤ projection X P ⁻¹ᵁ pOpen

namespace ProductChart
variable {X P} {a : AffineChart (product X P).hom} (c : ProductChart X P a)

@[implicit_reducible]
def relativeChart : AffineChart (pullback.fst X.hom P.hom) :=
  ⟨a.source,c.xOpen,a.source_affine,c.xAffine,c.overX⟩

@[implicit_reducible]
def parameterChart : AffineChart P.hom :=
  ⟨c.pOpen,a.target,c.pAffine,a.target_affine,c.pBase⟩

instance relativeAlgebra : Algebra c.relativeChart.base a.ring :=
  (pullback.fst X.hom P.hom |>.appLE c.xOpen a.source c.overX).hom.toAlgebra
end ProductChart

variable (C : CotangentNormalization (product X P).hom)
  (R : CotangentNormalization (pullback.fst X.hom P.hom))
  (B : CotangentNormalization P.hom)

/-- Actual all-stage polynomial maps for the absolute-to-relative change of base. -/
structure AbsoluteRelativePolynomial {a : AffineChart (product X P).hom}
    (c : ProductChart X P a) where
  map : ∀ n, (C.resolution a).algebra.obj n →+*
    (R.resolution c.relativeChart).algebra.obj n
  scalar : ∀ n (x : a.base),
    map n (algebraMap a.base ((C.resolution a).algebra.obj n) x) =
      algebraMap c.relativeChart.base ((R.resolution c.relativeChart).algebra.obj n)
        ((X.hom.appLE a.target c.xOpen c.xBase).hom x)
  augmentation : ∀ n (x : (C.resolution a).algebra.obj n),
    (R.resolution c.relativeChart).augmentation.app n (map n x) =
      (C.resolution a).augmentation.app n x
  simplicial : ∀ {m n} (g : m ⟶ n) (x : (C.resolution a).algebra.obj m),
    map n ((C.resolution a).algebra.map g x) =
      (R.resolution c.relativeChart).algebra.map g (map m x)
  cotangentMap : affineComplex (C.resolution a) ⟶ affineComplex (R.resolution c.relativeChart)
  normalized : ∀ (n : ℕ) (x : (C.resolution a).algebra.obj (op ⦋n⦌)),
    (affineDegreeIso (R.resolution c.relativeChart) n).hom
      ((cotangentMap.f (-(n : ℤ)))
        ((affineDegreeIso (C.resolution a) n).inv
          (CommAlgCat.resolutionCotangentTermDifferential a.base (CommAlgCat.of a.base a.ring)
            (C.resolution a).algebra (C.resolution a).augmentation (op ⦋n⦌) x))) =
      CommAlgCat.resolutionCotangentTermDifferential c.relativeChart.base
        (CommAlgCat.of c.relativeChart.base c.relativeChart.ring)
        (R.resolution c.relativeChart).algebra (R.resolution c.relativeChart).augmentation
        (op ⦋n⦌) (map (op ⦋n⦌) x)

/-- Actual all-stage polynomial maps for cotangent base change along the product square. -/
structure ParameterPolynomial {a : AffineChart (product X P).hom}
    (c : ProductChart X P a) where
  map : ∀ n, (B.resolution c.parameterChart).algebra.obj n →+*
    (R.resolution c.relativeChart).algebra.obj n
  scalar : ∀ n (x : a.base),
    map n (algebraMap a.base ((B.resolution c.parameterChart).algebra.obj n) x) =
      algebraMap c.relativeChart.base ((R.resolution c.relativeChart).algebra.obj n)
        ((X.hom.appLE a.target c.xOpen c.xBase).hom x)
  augmentation : ∀ n (x : (B.resolution c.parameterChart).algebra.obj n),
    (R.resolution c.relativeChart).augmentation.app n (map n x) =
      ((projection X P).appLE c.pOpen a.source c.overP).hom
        ((B.resolution c.parameterChart).augmentation.app n x)
  simplicial : ∀ {m n} (g : m ⟶ n)
    (x : (B.resolution c.parameterChart).algebra.obj m),
    map n ((B.resolution c.parameterChart).algebra.map g x) =
      (R.resolution c.relativeChart).algebra.map g (map m x)

/-- Native cochain maps with the full coefficient and refinement normalization. -/
structure ProductCotangentDiagram where
  relative : C.complex ⟶ R.complex
  baseChange : (cochainParameterPullback X P).obj B.complex ⟶ R.complex
  [baseChange_quasiIso : QuasiIso baseChange]
  absolutePolynomial : ∀ (a : AffineChart (product X P).hom) (c : ProductChart X P a),
    AbsoluteRelativePolynomial X P C R c
  parameterPolynomial : ∀ (a : AffineChart (product X P).hom) (c : ProductChart X P a),
    ParameterPolynomial X P R B c
  relative_normalized : ∀ (a : AffineChart (product X P).hom) (c : ProductChart X P a),
    C.comparison a ≫ ((moduleSections a.source).mapHomologicalComplex (.up ℤ)).map relative =
      (absolutePolynomial a c).cotangentMap ≫ R.comparison c.relativeChart
  baseChange_normalized : ∀ (a : AffineChart (product X P).hom)
    (c : ProductChart X P a) (n : ℕ)
    (x : (B.resolution c.parameterChart).algebra.obj (op ⦋n⦌)) (r : a.ring),
    r • (baseChange.f (-(n : ℤ))).app a.source
      (localPullbackSection (projection X P) (B.complex.X (-(n : ℤ)))
        c.pOpen a.source c.overP
        ((B.comparison c.parameterChart).f (-(n : ℤ))
          ((affineDegreeIso (B.resolution c.parameterChart) n).inv
            (CommAlgCat.resolutionCotangentTermDifferential c.parameterChart.base
              (CommAlgCat.of c.parameterChart.base c.parameterChart.ring)
              (B.resolution c.parameterChart).algebra (B.resolution c.parameterChart).augmentation
              (op ⦋n⦌) x)))) =
      r • (R.comparison c.relativeChart).f (-(n : ℤ))
        ((affineDegreeIso (R.resolution c.relativeChart) n).inv
          (CommAlgCat.resolutionCotangentTermDifferential c.relativeChart.base
            (CommAlgCat.of c.relativeChart.base c.relativeChart.ring)
            (R.resolution c.relativeChart).algebra (R.resolution c.relativeChart).augmentation
            (op ⦋n⦌) ((parameterPolynomial a c).map (op ⦋n⦌) x)))
  absolute_refinement : ∀ (a b : AffineChart (product X P).hom)
    (c : ProductChart X P a) (d : ProductChart X P b)
    (hU : b.source ≤ a.source) (hV : b.target ≤ a.target)
    (hX : d.xOpen ≤ c.xOpen) n (x : (C.resolution a).algebra.obj n),
    (absolutePolynomial b d).map n ((C.refinement a b hU hV).polynomialMap n x) =
      (R.refinement c.relativeChart d.relativeChart hU hX).polynomialMap n
        ((absolutePolynomial a c).map n x)
  parameter_refinement : ∀ (a b : AffineChart (product X P).hom)
    (c : ProductChart X P a) (d : ProductChart X P b)
    (hU : b.source ≤ a.source) (hV : b.target ≤ a.target)
    (hX : d.xOpen ≤ c.xOpen) (hP : d.pOpen ≤ c.pOpen) n
    (x : (B.resolution c.parameterChart).algebra.obj n),
    (parameterPolynomial b d).map n
        ((B.refinement c.parameterChart d.parameterChart hP hV).polynomialMap n x) =
      (R.refinement c.relativeChart d.relativeChart hU hX).polynomialMap n
        ((parameterPolynomial a c).map n x)

attribute [instance] ProductCotangentDiagram.baseChange_quasiIso

variable [HasDerivedPullbacks.{0}]

/-- The actual cochain-model projection before the native derived pullback comparison. -/
def productProjectionCochain (D : ProductCotangentDiagram X P C R B) (m : ℤ)
    (hBase : IsIso (DerivedCategory.Q.map (D.baseChange⟦m⟧'))) :
    DerivedCategory.Q.obj (C.complex⟦m⟧) ⟶
      DerivedCategory.Q.obj (((cochainParameterPullback X P).obj B.complex)⟦m⟧) := by
  let b := DerivedCategory.Q.map (D.baseChange⟦m⟧')
  letI : IsIso b := hBase
  exact DerivedCategory.Q.map (D.relative⟦m⟧') ≫ inv b

/-- The actual product cotangent projection, with every shift explicit. -/
def productProjection (D : ProductCotangentDiagram X P C R B) (m : ℤ)
    (hBase : IsIso (DerivedCategory.Q.map (D.baseChange⟦m⟧')))
    (hPull : IsIso ((derivedPullbackCounit (projection X P)).app (B.complex⟦m⟧))) :
    DerivedCategory.Q.obj (C.complex⟦m⟧) ⟶
      (derivedPullback (projection X P)).obj (DerivedCategory.Q.obj (B.complex⟦m⟧)) := by
  letI := hPull
  exact productProjectionCochain X P C R B D m hBase ≫
      DerivedCategory.Q.map (((cochainParameterPullback X P).commShiftIso m).inv.app B.complex) ≫
        inv ((derivedPullbackCounit (projection X P)).app (B.complex⟦m⟧))

end MathlibExt.AlgebraicGeometry.StablePairProductCotangents
