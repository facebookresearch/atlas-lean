/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackSourceFiltrations
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Normalized trait charts of Θ and ST

The chart at 1, the chart at 0, and the two ST trait restrictions
are genuine quotient-stack points. Their total torsors are identified
with the actual multiplicative group. Every equivariant map is fixed
on all scheme-valued points by its affine coordinate formulas.

For ST, the first chart is (s,t)=(g,π/g), the second is (πg,1/g).
The common generic-fibre arrow is determined by g_second=g_first/π.
Applying a stack map to this arrow gives the elementary-modification
comparison; it is not an arbitrary generic isomorphism.

Reference: Alper–Halpern-Leistner–Heinloth, arXiv:1812.01128v5,
§2.3 and §3.5, equation (3.6) and Definition 3.36.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ThetaTraitCharts

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open ThetaQuotientSources GroupTorsorGeometry StackSourceFiltrations
open scoped Pseudofunctor.StrongTrans
attribute [local instance] CategoryTheory.ModObj.regular

universe u
variable (R : Type u) [CommRing R]

/-- The normalized equivariant presentation of a Θ section. -/
structure ThetaChart [A : ContractingAction R]
    (Q : @QuotientSource R _ (multiplicativeGroup R) (affineLine R) _ A.action)
    (a : R) where
  point : Q.stack.Fibre (Over.mk (𝟙 (Spec (.of R))))
  trivial : ((Q.fibre _).functor.obj point).torsor.total ≅ multiplicativeGroup R
  equivariant : γ[multiplicativeGroup R,((Q.fibre _).functor.obj point).torsor.total] ≫
      trivial.hom = (multiplicativeGroup R ◁ trivial.hom) ≫
        γ[multiplicativeGroup R,multiplicativeGroup R]
  normalized : ∀ (T : Scheme.{u})
    (p : T ⟶ ((Q.fibre _).functor.obj point).torsor.total.left),
    coordinate (p ≫ ((Q.fibre _).functor.obj point).map.left) Polynomial.X =
      coordinate (p ≫ trivial.hom.left) (LaurentPolynomial.T 1) *
        coordinate (p ≫ ((Q.fibre _).functor.obj point).torsor.projection.left) a

/-- The actual filtration source and its coordinate-normalized zero and one evaluations. -/
structure FiltrationSource [A : ContractingAction R] where
  quotient : @QuotientSource R _ (multiplicativeGroup R) (affineLine R) _ A.action
  zero : ThetaChart R quotient 0
  one : ThetaChart R quotient 1

variable {R}

/-- Evaluation at a=0 or a=1 is literal evaluation of the same actual mapping family. -/
def chartEvaluation [A : ContractingAction R]
    {Q : @QuotientSource R _ (multiplicativeGroup R) (affineLine R) _ A.action}
    {a : R} (C : ThetaChart R Q a)
    (X : RelativeStack (Spec (.of R))) (T : Over (Spec (.of R))) :
    Maps Q.stack X T ⥤ X.Fibre T :=
  evaluate Q.stack X T ((SourceSection.mk C.point).point T)

/-- At zero, retain the entire actual source stabilizer action on the
evaluated object. This is the grading supplied by the same strong map;
it is not lost by replacing the map with an isomorphism class. -/
def chartGrading [A : ContractingAction R]
    {Q : @QuotientSource R _ (multiplicativeGroup R) (affineLine R) _ A.action}
    (C : ThetaChart R Q 0) (X : RelativeStack (Spec (.of R)))
    (T : Over (Spec (.of R))) (q : Maps Q.stack X T) :
    Aut ((SourceSection.mk C.point).point T) →*
      Aut ((chartEvaluation C X T).obj q) :=
  (q.app (.mk (op (Over.mk (𝟙 T))))).toFunctor.mapAut _

/-- A normalized ST chart uses the literal equivariant coordinates for one
of the two standard trait inclusions. -/
structure SurfaceChart {π : R} [A : OppositeWeightAction R π]
    (Q : @QuotientSource R _ (multiplicativeGroup R) (nodeSurface R π) _ A.action)
    (first : Bool) where
  point : Q.stack.Fibre (Over.mk (𝟙 (Spec (.of R))))
  trivial : ((Q.fibre _).functor.obj point).torsor.total ≅ multiplicativeGroup R
  equivariant : γ[multiplicativeGroup R,((Q.fibre _).functor.obj point).torsor.total] ≫
      trivial.hom = (multiplicativeGroup R ◁ trivial.hom) ≫
        γ[multiplicativeGroup R,multiplicativeGroup R]
  normalized_s : ∀ (T : Scheme.{u})
    (p : T ⟶ ((Q.fibre _).functor.obj point).torsor.total.left),
    coordinate (p ≫ ((Q.fibre _).functor.obj point).map.left) (nodeS R π) =
      coordinate (p ≫ trivial.hom.left) (LaurentPolynomial.T 1) *
        coordinate (p ≫ ((Q.fibre _).functor.obj point).torsor.projection.left)
          (if first then 1 else π)
  normalized_t : ∀ (T : Scheme.{u})
    (p : T ⟶ ((Q.fibre _).functor.obj point).torsor.total.left),
    coordinate (p ≫ ((Q.fibre _).functor.obj point).map.left) (nodeT R π) =
      coordinate (p ≫ trivial.hom.left) (LaurentPolynomial.T (-1)) *
        coordinate (p ≫ ((Q.fibre _).functor.obj point).torsor.projection.left)
          (if first then π else 1)

/-- The two actual trait charts and their coordinate-fixed generic comparison. -/
structure SurfaceTraitSource (π : R) (K : Over (Spec (.of R)))
    [A : OppositeWeightAction R π] where
  quotient : @QuotientSource R _ (multiplicativeGroup R) (nodeSurface R π) _ A.action
  first : SurfaceChart quotient true
  second : SurfaceChart quotient false
  genericIso :
    ((SourceSection.mk first.point).point K) ≅ ((SourceSection.mk second.point).point K)
  normalized_generic : ∀ (T : Scheme.{u})
    (p : T ⟶ ((quotient.fibre K).functor.obj
      ((SourceSection.mk first.point).point K)).torsor.total.left),
    coordinate
      (p ≫ ((quotient.fibre K).functor.map genericIso.hom).iso.hom.left ≫
        (quotient.restriction (StackSourceFiltrations.toUnit K) second.point).iso.hom.left ≫
        ((quotient.reindex (StackSourceFiltrations.toUnit K) second.point).original
          (multiplicativeGroup R)).left ≫
        second.trivial.hom.left) (LaurentPolynomial.T 1) *
      coordinate
        (p ≫ ((quotient.fibre K).functor.obj
          ((SourceSection.mk first.point).point K)).torsor.projection.left ≫ K.hom) π =
    coordinate
      (p ≫ (quotient.restriction (StackSourceFiltrations.toUnit K) first.point).iso.hom.left ≫
        ((quotient.reindex (StackSourceFiltrations.toUnit K) first.point).original
          (multiplicativeGroup R)).left ≫
        first.trivial.hom.left) (LaurentPolynomial.T 1)

def SurfaceTraitSource.modification {π : R} {K : Over (Spec (.of R))}
    [OppositeWeightAction R π] (D : SurfaceTraitSource π K) :
    ModificationSource (Y := D.quotient.stack) (Over.mk (𝟙 (Spec (.of R)))) K
      (StackSourceFiltrations.toUnit K) where
  first := ⟨D.first.point⟩
  second := ⟨D.second.point⟩
  genericIso := D.genericIso

end MathlibExt.AlgebraicGeometry.ThetaTraitCharts
