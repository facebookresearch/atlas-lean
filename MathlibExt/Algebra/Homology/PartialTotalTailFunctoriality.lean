/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.PartialTotalEvenTail
public import Mathlib.CategoryTheory.Whiskering

/-!
# Natural tail comparisons for initial-column quotients

For a first-quadrant bicomplex K, the outer tail at s retains its horizontal columns s,s+1,… in
their given degrees. In a preadditive category with a zero object and finite coproducts, tail
totalization and totalization of the reindexed restriction followed by zero extension through s
are functors on bicomplexes. The projection Tot K→Tot(tail_{p+1}K) is natural.

When the category is abelian, the cokernel of P_p(K)→Tot K is naturally isomorphic to
Tot(tail_{p+1}K), and its quotient projection agrees with the tail projection through this
isomorphism. For p=1, the offset is two. Its even parity preserves the vertical totalization
sign (-1)^a under horizontal translation a↦a+2, giving a natural isomorphism with the total of
the restricted bicomplex extended by zero through two degrees. Applying H_n gives the same
comparison in homology degree n, without changing that degree. Category universes are arbitrary.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace HomologicalComplex₂

section TailFunctors

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- Let C be preadditive with a zero object and finite coproducts and s∈ℕ. This functor sends a
bicomplex K of shape (down ℕ,down ℕ) to the total complex of its outer tail, which is zero in
horizontal degrees below s and retains the columns at and above s in their given degrees. A
bicomplex morphism is restricted to the retained columns and then totalized. -/
def outerTailTotalFunctor (s : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      ChainComplex C ℕ :=
  (partialTotalOuterEmbedding s).stupidTruncFunctor (ChainComplex C ℕ) ⋙
    totalFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- For a preadditive category C with a zero object and finite coproducts and s∈ℕ, this functor
first restricts a first-quadrant bicomplex K along the horizontal embedding a↦a+s, then
totalizes that reindexed bicomplex, and finally extends the total chain complex by degree n↦n+s.
The result is zero below total degree s and is functorial in all bicomplex morphisms. -/
def outerRestrictedTotalExtendFunctor (s : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      ChainComplex C ℕ :=
  (partialTotalOuterEmbedding s).restrictionFunctor (ChainComplex C ℕ) ⋙
    totalFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⋙
      (partialTotalOuterEmbedding s).extendFunctor C

/-- Let C be preadditive with a zero object and finite coproducts and p∈ℕ. This natural
transformation from totalization to outer-tail totalization at p+1 has component q_K:Tot
K→Tot(tail_{p+1}K), induced by the projection that discards horizontal columns 0,…,p. For f:K→L,
it satisfies Tot f≫q_L=q_K≫Tot(tail_{p+1}f). -/
def partialTotalTailProjectionNatTrans (p : ℕ) :
    totalFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⟶
      outerTailTotalFunctor (C := C) (p + 1) where
  app K := total.map (natTailProjection K (p + 1)) (ComplexShape.down ℕ)
  naturality {K L} φ := by
    change total.map φ (ComplexShape.down ℕ) ≫
        total.map (natTailProjection L (p + 1)) (ComplexShape.down ℕ) =
      total.map (natTailProjection K (p + 1)) (ComplexShape.down ℕ) ≫
        total.map (stupidTruncMap φ (partialTotalOuterEmbedding (p + 1))) (ComplexShape.down ℕ)
    simpa only [total.map_comp] using
      congrArg (fun f => total.map f (ComplexShape.down ℕ))
        (natTailProjection_naturality φ (p + 1))

end TailFunctors

section CokernelComparisons

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let C be abelian and p∈ℕ. For a bicomplex K of shape (down ℕ,down ℕ), let P_p(K) retain
horizontal columns 0,…,p. This natural isomorphism identifies coker(P_p(K)→Tot K) with
Tot(tail_{p+1}K), where the tail retains columns from p+1 in their given degrees. The
components commute with the maps induced by every bicomplex morphism. -/
def partialTotalCokernelTailNatIso (p : ℕ) :
    partialTotalCokernelFunctor (A := C) p ≅ outerTailTotalFunctor (C := C) (p + 1) :=
  NatIso.ofComponents (fun K => K.partialTotalCokernelTailIso p) (by
    intro K L φ
    exact partialTotalCokernelTailIso_hom_naturality φ p)

/-- For an abelian category C and p∈ℕ, let e_p be the natural isomorphism from coker(P_p(K)→Tot K)
to Tot(tail_{p+1}K) on first-quadrant bicomplexes K. If π_p is the cokernel projection
transformation and q_p the totalized projection discarding columns 0,…,p, then π_p≫e_p.hom=q_p.
This equality holds as a natural transformation in the bicomplex. -/
theorem partialTotalCokernelπ_comp_tailNatIso (p : ℕ) :
    partialTotalCokernelπ (A := C) p ≫ (partialTotalCokernelTailNatIso (C := C) p).hom =
      partialTotalTailProjectionNatTrans (C := C) p := by
  apply NatTrans.ext
  funext K
  exact K.partialTotalCokernelTailIso_π p

/-- Let C be abelian. On bicomplexes K of shape (down ℕ,down ℕ), this natural isomorphism sends
coker(P_1(K)→Tot K) to the total of the horizontal restriction a↦a+2, extended by zero through
total degree two. It is the initial-column cokernel-to-tail comparison followed by the
even-offset extension–total isomorphism. Translation by two preserves the totalization sign
(-1)^a. -/
def firstTwoColumnCokernelTailNatIso :
    partialTotalCokernelFunctor (A := C) 1 ≅ outerRestrictedTotalExtendFunctor (C := C) 2 :=
  NatIso.ofComponents (fun K => K.firstTwoColumnCokernelTailIso) (by
    intro K L φ
    exact firstTwoColumnCokernelTailIso_hom_naturality φ)

/-- For a first-quadrant bicomplex K in an abelian category, let π:Tot K→coker(P_1(K)→Tot K), e the
comparison with the zero-extended total of the horizontal restriction a↦a+2, and q:Tot
K→Tot(tail_2 K) the tail projection. If u:Tot(tail_2 K)≅E_2(Tot(K|_{a↦a+2})) is the canonical
even-offset extension comparison, then π≫e.hom=q≫u.hom. -/
@[reassoc]
theorem firstTwoColumnCokernelTailNatIso_π
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    cokernel.π (K.partialTotalι 1) ≫ (firstTwoColumnCokernelTailNatIso (C := C)).hom.app K =
      total.map (natTailProjection K 2) (ComplexShape.down ℕ) ≫
        (evenOuterExtensionTotalIso
          (K.restriction (c := ComplexShape.down ℕ) (partialTotalOuterEmbedding 2)) 1).hom := by
  have paste {X Y Z W : ChainComplex C ℕ}
      (π : X ⟶ Y) (a : Y ⟶ Z) (b : Z ⟶ W) (q : X ⟶ Z)
      (h : π ≫ a = q) : π ≫ (a ≫ b) = q ≫ b :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ b) h)
  exact paste (cokernel.π (K.partialTotalι 1)) (K.partialTotalCokernelTailIso 1).hom
    (evenOuterExtensionTotalIso
      (K.restriction (c := ComplexShape.down ℕ) (partialTotalOuterEmbedding 2)) 1).hom
    (total.map (natTailProjection K 2) (ComplexShape.down ℕ))
    (K.partialTotalCokernelTailIso_π 1)

/-- Let C be abelian and n∈ℕ. Applying H_n to the natural two-column quotient comparison gives an
isomorphism of functors H_n(coker(P_1(K)→Tot K))≅H_n(E_2(Tot(K|_{a↦a+2}))) on first-quadrant
bicomplexes K. The target is the zero-extended total complex itself, evaluated in the same
homology degree n; its degree is not reindexed in this statement. -/
def firstTwoColumnCokernelTailHomologyNatIso (n : ℕ) :
    partialTotalCokernelFunctor (A := C) 1 ⋙ homologyFunctor C (ComplexShape.down ℕ) n ≅
      outerRestrictedTotalExtendFunctor (C := C) 2 ⋙ homologyFunctor C (ComplexShape.down ℕ) n :=
  Functor.isoWhiskerRight (firstTwoColumnCokernelTailNatIso (C := C))
    (homologyFunctor C (ComplexShape.down ℕ) n)

end CokernelComparisons

end HomologicalComplex₂
