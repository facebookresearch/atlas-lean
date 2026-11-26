/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestriction

/-!
# Bicomplex naturality of complete-filtration restriction

Let C be preadditive with a zero object and finite coproducts. For a bicomplex K of shape (down
ℕ,down ℕ), write R_K(n)=G_{e(n)}(K) for the complete horizontal filtration restricted along the
finite-cut embedding e:ℕ→ℤ∪{⊥,⊤}, and S_K(n)=G^fin_n(K) for the finite horizontal diagram. Both
assignments are functors from first-quadrant bicomplexes to natural-index diagrams of chain
complexes.

The canonical stage isomorphisms ε_{K,n}:R_K(n)≅S_K(n) form a natural isomorphism R≅S of
diagram-valued functors. Besides commuting with transitions in n, they satisfy
R(f)_n≫ε_{L,n}.hom=ε_{K,n}.hom≫S(f)_n for every bicomplex morphism f:K→L. Category universes are
arbitrary.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be preadditive with a zero object and finite coproducts. This functor sends bicomplexes K
of shape (down ℕ,down ℕ) to natural-index chain diagrams R_K(n)=G_{e(n)}(K), where e(n) is the
finite integer cut n of the complete horizontal filtration. Diagram arrows are the
complete-stage transitions, and a bicomplex morphism f:K→L is sent to the transformation with
component G_{e(n)}(f) at n. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ ChainComplex C ℕ) where
  obj K := horizontalFiltrationNatToEIntFunctor ⋙
    (horizontalCompleteTotalFiltration K).diagram
  map f := Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
    (horizontalCompleteTotalFilteredObjectMap f).natTrans
  map_id K := by
    have h := congrArg CategoryTheory.FilteredObject.Hom.natTrans
      (horizontalCompleteTotalFilteredObjectFunctor.map_id K)
    change (horizontalCompleteTotalFilteredObjectMap (𝟙 K)).natTrans =
      CategoryTheory.FilteredObject.Hom.natTrans
        (𝟙 (horizontalCompleteTotalFilteredObject K)) at h
    change Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
        (horizontalCompleteTotalFilteredObjectMap (𝟙 K)).natTrans = 𝟙 _
    rw [h]
    rfl
  map_comp f g := by
    have h := congrArg CategoryTheory.FilteredObject.Hom.natTrans
      (horizontalCompleteTotalFilteredObjectFunctor.map_comp f g)
    change (horizontalCompleteTotalFilteredObjectMap (f ≫ g)).natTrans =
      CategoryTheory.FilteredObject.Hom.natTrans
        (horizontalCompleteTotalFilteredObjectMap f ≫
          horizontalCompleteTotalFilteredObjectMap g) at h
    change Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
        (horizontalCompleteTotalFilteredObjectMap (f ≫ g)).natTrans =
      Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
          (horizontalCompleteTotalFilteredObjectMap f).natTrans ≫
        Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
          (horizontalCompleteTotalFilteredObjectMap g).natTrans
    rw [h]
    rfl

/-- Let C be preadditive with a zero object and finite coproducts. This functor sends a bicomplex K
of shape (down ℕ,down ℕ) to its finite horizontal filtration diagram S_K:ℕ→ChainComplex(C,ℕ),
with S_K(n)=G^fin_n(K). An inequality n≤m gives the finite-stage transition, and a bicomplex map
f:K→L gives the transformation with component G^fin_n(f). The assignments preserve identities
and composition. -/
noncomputable def horizontalTotalFiltrationDiagramFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ ChainComplex C ℕ) where
  obj K := (horizontalTotalFiltration K).diagram
  map f := (horizontalTotalFilteredObjectMap f).natTrans
  map_id K := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    (horizontalTotalFilteredObjectFunctor.map_id K)
  map_comp f g := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    (horizontalTotalFilteredObjectFunctor.map_comp f g)

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor.obj K =
      horizontalFiltrationNatToEIntFunctor ⋙
        (horizontalCompleteTotalFiltration K).diagram :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor_map_app
    (f : K ⟶ L) (n : ℕ) :
    (horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor.map f).app n =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f
        ((n : ℤ) : EInt) :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationDiagramFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalTotalFiltrationDiagramFunctor.obj K =
      (horizontalTotalFiltration K).diagram :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationDiagramFunctor_map_app
    (f : K ⟶ L) (n : ℕ) :
    (horizontalTotalFiltrationDiagramFunctor.map f).app n =
      horizontalFilteredTotalComplexMapOfBicomplex f n :=
  rfl

/-- Let C be preadditive with a zero object and finite coproducts. Let R_K(n)=G_{e(n)}(K) and
S_K(n)=G^fin_n(K) for first-quadrant bicomplexes K, with e the embedding as finite integer cuts.
The stage comparisons ε_{K,n}:R_K(n)≅S_K(n) define this natural isomorphism between the
bicomplex-to-chain-diagram functors R and S. They commute with every index transition and
satisfy R(f)_n≫ε_{L,n}.hom=ε_{K,n}.hom≫S(f)_n for every f:K→L. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionNatIso :
    horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor (C := C) ≅
      horizontalTotalFiltrationDiagramFunctor (C := C) :=
  NatIso.ofComponents horizontalCompleteTotalFiltrationNatRestrictionIso
    (by
      intro K L f
      apply NatTrans.ext
      funext n
      change horizontalCompleteFilteredTotalComplexMapOfBicomplex f
            ((n : ℤ) : EInt) ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso L
            (n : ℤ) (Int.natCast_nonneg n)).hom =
        (horizontalCompleteFilteredTotalComplexFiniteIso K
            (n : ℤ) (Int.natCast_nonneg n)).hom ≫
          horizontalFilteredTotalComplexMapOfBicomplex f n
      simpa only [Int.toNat_natCast] using
        (horizontalCompleteFilteredTotalComplexFiniteIso_naturality f
          (n : ℤ) (Int.natCast_nonneg n)).symm)

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (horizontalCompleteTotalFiltrationNatRestrictionNatIso
      (C := C)).hom.app K =
      (horizontalCompleteTotalFiltrationNatRestrictionIso K).hom :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_app_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionNatIso
      (C := C)).hom.app K).app n =
      (horizontalCompleteFilteredTotalComplexFiniteIso K
        (n : ℤ) (Int.natCast_nonneg n)).hom :=
  rfl

end HomologicalComplex₂

end
