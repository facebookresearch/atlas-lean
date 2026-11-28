/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestrictionNaturality

/-!
# Total-complex compatibility of complete-to-finite restriction

Let C be preadditive with a zero object and finite coproducts. For a first-quadrant bicomplex K,
the finite horizontal diagram S_K(n)=G^fin_n(K) and the restricted complete diagram
R_K(n)=G_{e(n)}(K) both map to the constant natural-index diagram T_K(n)=Tot K, where e(n) is
the finite integer cut n. Their components are the canonical stage inclusions.

The complete-to-finite comparisons ε_{K,n}:R_K(n)≅S_K(n) are natural in the filtration index and
in K. They preserve the total inclusions, so ε.hom≫(S→T)=(R→T) as transformations between
bicomplex-to-diagram functors. This packages the stage comparisons together with their common
target Tot K, in arbitrary category universes.
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

/-- Let C be preadditive with a zero object and finite coproducts. This functor sends a bicomplex K
of shape (down ℕ,down ℕ) to the constant diagram T_K:ℕ→ChainComplex(C,ℕ) with value Tot K. Its
index transitions are identities, and a bicomplex morphism f:K→L is sent to the natural
transformation whose component at every index is Tot f. -/
noncomputable def horizontalTotalComplexNatConstDiagramFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ ChainComplex C ℕ) :=
  HomologicalComplex₂.totalFunctor C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⋙
    Functor.const ℕ

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalComplexNatConstDiagramFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalTotalComplexNatConstDiagramFunctor.obj K =
      (Functor.const ℕ).obj (K.total (ComplexShape.down ℕ)) :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalComplexNatConstDiagramFunctor_map_app
    (f : K ⟶ L) (n : ℕ) :
    (horizontalTotalComplexNatConstDiagramFunctor.map f).app n =
      total.map f (ComplexShape.down ℕ) :=
  rfl

/-- Let C be preadditive with a zero object and finite coproducts. For a first-quadrant bicomplex K,
let S_K(n)=G^fin_n(K) and T_K(n)=Tot K. This natural transformation between the corresponding
bicomplex-to-diagram functors has component ι^fin_n:G^fin_n(K)→Tot K at K and n. It is natural
in n because stage transitions preserve total inclusions, and natural in K because
G^fin_n(f)≫ι^fin_{L,n}=ι^fin_{K,n}≫Tot f. -/
noncomputable def horizontalTotalFiltrationDiagramToTotal :
    horizontalTotalFiltrationDiagramFunctor (C := C) ⟶
      horizontalTotalComplexNatConstDiagramFunctor (C := C) where
  app K := (horizontalTotalFiltration K).ι
  naturality K L f := by
    apply NatTrans.ext
    funext n
    exact (horizontalTotalFilteredObjectMap f).comm n

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationDiagramToTotal_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (horizontalTotalFiltrationDiagramToTotal (C := C)).app K =
      (horizontalTotalFiltration K).ι :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationDiagramToTotal_app_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    ((horizontalTotalFiltrationDiagramToTotal (C := C)).app K).app n =
      horizontalFilteredTotalComplexToTotal K n :=
  rfl

/-- Let C be preadditive with a zero object and finite coproducts. For a first-quadrant bicomplex K,
let R_K(n)=G_{e(n)}(K), where e(n) is the finite integer cut n, and T_K(n)=Tot K. This
transformation has component ι_{e(n)}:G_{e(n)}(K)→Tot K at K and n. It is natural in the index
and the bicomplex; for f:K→L its square is G_{e(n)}(f)≫ι_{L,e(n)}=ι_{K,e(n)}≫Tot f. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal :
    horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor (C := C) ⟶
      horizontalTotalComplexNatConstDiagramFunctor (C := C) where
  app K := Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
    (horizontalCompleteTotalFiltration K).ι
  naturality K L f := by
    apply NatTrans.ext
    funext n
    change horizontalCompleteFilteredTotalComplexMapOfBicomplex f
          ((n : ℤ) : EInt) ≫
        horizontalCompleteFilteredTotalToTotal L ((n : ℤ) : EInt) =
      horizontalCompleteFilteredTotalToTotal K ((n : ℤ) : EInt) ≫
        total.map f (ComplexShape.down ℕ)
    exact (horizontalCompleteTotalFilteredObjectMap f).comm
      ((n : ℤ) : EInt)

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
      (C := C)).app K =
      Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
        (horizontalCompleteTotalFiltration K).ι :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal_app_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
      (C := C)).app K).app n =
      horizontalCompleteFilteredTotalToTotal K ((n : ℤ) : EInt) :=
  rfl

/-- Let C be preadditive with a zero object and finite coproducts. For first-quadrant bicomplexes K,
write R_K(n)=G_{e(n)}(K), S_K(n)=G^fin_n(K), and T_K(n)=Tot K, with e(n) the finite integer cut
n. Let ε:R≅S be the complete-to-finite natural isomorphism, s:S→T the finite-stage inclusion and
r:R→T the restricted complete-stage inclusion. Then ε.hom≫s=r as natural transformations of
bicomplex-to-diagram functors. At K and n, ε_{K,n}.hom≫ι^fin_n=ι_{e(n)}. -/
theorem horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_comp_toTotal :
    (horizontalCompleteTotalFiltrationNatRestrictionNatIso
        (C := C)).hom ≫
      horizontalTotalFiltrationDiagramToTotal (C := C) =
    horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
      (C := C) := by
  apply NatTrans.ext
  funext K
  exact horizontalCompleteTotalFiltrationNatRestrictionIso_hom_comp_ι K

end HomologicalComplex₂

end
