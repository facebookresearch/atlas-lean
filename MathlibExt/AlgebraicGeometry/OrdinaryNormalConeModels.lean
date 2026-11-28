/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GradedConeProjectiveModels
public import MathlibExt.AlgebraicGeometry.AffineNormalConeMaps

/-!
# Ordinary normal cones and the distinguished normal-cone cycle

For a closed embedding, the affine presentation is the literal
surjective map from the ambient affine open to its whole inverse
image. Its normal algebra is B⊗_R Rees(ker(R→B)). The degree-n part
is the span of the actual degree-n Rees monomials.

Every ambient affine open has a view. All refinement maps are the
native coefficient/degree-one normal maps, with unit/composition
coherence and their actual global scheme maps. This is the ordinary
cone, including singular ambient schemes; it is not the quotient by
ambient tangent translations used for an intrinsic stack cone.

The distinguished cycle is the genuine signed generic-length sum
over irreducible cone components, with sign given by the dimension
of their actual projected image closures. It is not homogeneous.

Reference: Behrend, arXiv:math/0507523v2, §1.1, Proposition 1.1.
The Rees maps reuse Mathlib at 56a005855ea17e0b0958f73ec801ae140b0a1679
and the existing coefficient-normalized AffineNormalConeMaps module.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinaryNormalConeModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GlobalPerfectObstructionTheory IntegralChowChernModels
open AffineConeAtlas AffineNormalConeMaps GradedConeProjectiveModels
open TopologicalSpace StackCycleGeometry

variable {X M : SchemeData}

/-- The full inverse image of an actual ambient affine open under a closed embedding. -/
structure ClosedAffineChart (i : X.scheme ⟶ M.scheme) where
  chart : AffineChart i.left
  source_eq : chart.source = i.left ⁻¹ᵁ chart.target
  surjective : Function.Surjective (algebraMap chart.base chart.ring)

/-- The presentation ring is the actual ambient section ring, not a chosen polynomial ring. -/
def embeddingPresentation {i : X.scheme ⟶ M.scheme} (a : ClosedAffineChart i) :
    _root_.Algebra.Extension.{0} a.chart.base a.chart.ring :=
  _root_.Algebra.Extension.ofSurjective
    ({ toRingHom := algebraMap a.chart.base a.chart.ring
       commutes' := by intro r; rfl } : a.chart.base →ₐ[a.chart.base] a.chart.ring)
    a.surjective

/-- The literal normal algebra's homogeneous monomial of any degree. -/
def normalMonomial {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (P : _root_.Algebra.Extension.{0} A B) (n : ℕ) (x : ↥(P.ker ^ n)) : normalAlgebra P :=
  Algebra.TensorProduct.includeRight
    (⟨Polynomial.monomial n x.val,reesAlgebra.monomial_mem.mpr x.property⟩ : reesAlgebra P.ker)

def normalGrade {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (P : _root_.Algebra.Extension.{0} A B) (n : ℕ) : Submodule B (normalAlgebra P) :=
  Submodule.span B (Set.range (normalMonomial P n))

/-- Native grading proofs for the already fixed Rees monomial submodules. -/
structure NormalGrading {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (P : _root_.Algebra.Extension.{0} A B) where
  grading : GradedRing (normalGrade P)
  coefficient_injective : Function.Injective (algebraMap B (normalAlgebra P))
  degreeZero : ∀ a : normalAlgebra P, a ∈ normalGrade P 0 ↔
    ∃ b : B, algebraMap B (normalAlgebra P) b = a
  generated : Algebra.adjoin B (normalGrade P 1 : Set (normalAlgebra P)) = ⊤

def normalConeAlgebra {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    {P : _root_.Algebra.Extension.{0} A B} (N : NormalGrading P) :
    AffineGradedCone (.of B) where
  algebra := CommAlgCat.of B (normalAlgebra P)
  grade := normalGrade P
  grading := N.grading
  coefficient_injective := N.coefficient_injective
  degreeZero := N.degreeZero
  generated := N.generated

/-- The affine chart map is the native section-ring Spec isomorphism and open inclusion. -/
def chartBaseMap {i : X.scheme ⟶ M.scheme} (a : ClosedAffineChart i) :
    Spec (.of a.chart.ring) ⟶ X.scheme.left := a.chart.source_affine.fromSpec

/-- The two actual section-ring restriction maps. -/
structure NormalRefinement {i : X.scheme ⟶ M.scheme} (a b : ClosedAffineChart i)
    (hU : b.chart.source ≤ a.chart.source) (hV : b.chart.target ≤ a.chart.target) where
  square :
    (algebraMap (embeddingPresentation b).Ring b.chart.ring).comp
      (M.scheme.left.presheaf.map (homOfLE hV).op).hom =
    (X.scheme.left.presheaf.map (homOfLE hU).op).hom.comp
      (algebraMap (embeddingPresentation a).Ring a.chart.ring)
  normal : NormalMap (embeddingPresentation a) (embeddingPresentation b)
    (M.scheme.left.presheaf.map (homOfLE hV).op).hom
    (X.scheme.left.presheaf.map (homOfLE hU).op).hom square

/-- The actual global cone is tied to all affine closed-embedding views and their maps. -/
structure OrdinaryNormalCone (i : X.scheme ⟶ M.scheme) where
  [closed : IsClosedImmersion i.left]
  cone : GlobalGradedCone X
  affineCharts : ∀ (U : M.scheme.left.Opens) (_hU : IsAffineOpen U),
    {a : ClosedAffineChart i // a.chart.target=U}
  grading : ∀ a : ClosedAffineChart i, NormalGrading (embeddingPresentation a)
  algebraIso : ∀ a : ClosedAffineChart i,
    (cone.chart (.of a.chart.ring) (chartBaseMap a)).algebra ≃ₐ[a.chart.ring]
      normalAlgebra (embeddingPresentation a)
  grade_normalized : ∀ (a : ClosedAffineChart i) (n : ℕ)
    (r : (cone.chart (.of a.chart.ring) (chartBaseMap a)).algebra),
    r ∈ (cone.chart (.of a.chart.ring) (chartBaseMap a)).grade n ↔
      algebraIso a r ∈ normalGrade (embeddingPresentation a) n
  refinement : ∀ (a b : ClosedAffineChart i)
    (hU : b.chart.source≤a.chart.source) (hV : b.chart.target≤a.chart.target),
    NormalRefinement a b hU hV
  overlap : ∀ (a b : ClosedAffineChart i)
    (hU : b.chart.source≤a.chart.source) (hV : b.chart.target≤a.chart.target),
    Spec.map (CommRingCat.ofHom (refinement a b hU hV).normal.map) ≫
      (Spec.map (CommRingCat.ofHom (algebraIso a).toRingHom) ≫
        (cone.comparison (.of a.chart.ring) (chartBaseMap a)).inv ≫
          pullback.fst cone.projection.left (chartBaseMap a)) =
    Spec.map (CommRingCat.ofHom (algebraIso b).toRingHom) ≫
      (cone.comparison (.of b.chart.ring) (chartBaseMap b)).inv ≫
        pullback.fst cone.projection.left (chartBaseMap b)
  identity : ∀ a : ClosedAffineChart i,
    (refinement a a le_rfl le_rfl).normal.map = RingHom.id _
  composition : ∀ (a b c : ClosedAffineChart i)
    (hU : b.chart.source≤a.chart.source) (hV : b.chart.target≤a.chart.target)
    (hU' : c.chart.source≤b.chart.source) (hV' : c.chart.target≤b.chart.target),
    (refinement a c (hU'.trans hU) (hV'.trans hV)).normal.map =
      (refinement b c hU' hV').normal.map.comp (refinement a b hU hV).normal.map

/-- The image point is the actual projection of the generic point of the cone component. -/
def imageGenericPoint {i : X.scheme ⟶ M.scheme} (N : OrdinaryNormalCone i)
    (Z : irreducibleComponents N.cone.total.scheme.left) : X.scheme.left :=
  N.cone.projection.left Z.property.1.genericPoint

/-- Image dimensions are fixed by the native point-closure dimension. -/
structure DistinguishedDimension {i : X.scheme ⟶ M.scheme} (N : OrdinaryNormalCone i) where
  dimension : irreducibleComponents N.cone.total.scheme.left → ℕ
  normalized : ∀ Z, Order.height (imageGenericPoint N Z) = dimension Z

/-- The actual nilpotent generic length of a normal-cone component. -/
def coneMultiplicity {i : X.scheme ⟶ M.scheme} (N : OrdinaryNormalCone i)
    (Z : irreducibleComponents N.cone.total.scheme.left) : ℤ :=
  (Module.length
    (N.cone.total.scheme.left.presheaf.stalk Z.property.1.genericPoint)
    (N.cone.total.scheme.left.presheaf.stalk Z.property.1.genericPoint)).toNat

/-- Behrend's nonhomogeneous distinguished cycle c_(X/M). -/
def distinguishedCycle {i : X.scheme ⟶ M.scheme} (N : OrdinaryNormalCone i)
    (D : DistinguishedDimension N) : AlgebraicCycle X.scheme.left ℤ := by
  classical
  letI : Finite (irreducibleComponents N.cone.total.scheme.left) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  letI := Fintype.ofFinite (irreducibleComponents N.cone.total.scheme.left)
  exact ∑ Z : irreducibleComponents N.cone.total.scheme.left,
    Function.locallyFinsuppWithin.single (imageGenericPoint N Z)
      ((-1 : ℤ)^(D.dimension Z) * coneMultiplicity N Z)

end MathlibExt.AlgebraicGeometry.OrdinaryNormalConeModels
