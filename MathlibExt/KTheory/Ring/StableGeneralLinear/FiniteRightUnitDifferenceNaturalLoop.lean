/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteUnitDifferenceNaturalLoop
public import MathlibExt.KTheory.Ring.StableGeneralLinear.RightUnitStabilizationDifferences
public import Mathlib.CategoryTheory.Whiskering

/-!
# The whole ORIGINAL right-unit difference and its actual inactive prism

The next right-unit comparison is the existing next natural isomorphism
whiskered by the ORIGINAL transition and transported only along the proved
original inclusion square. Its complete difference is the SAME computed
perfect inactive loop at every object. The entire original prism, including
its active parameter, is retained.
-/

noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private def finiteNextRightUnitIsoRecipe (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ≅
      (finiteToStableCategoryMap R n).toFunctor ⋙ blockSumRightClassifyingFunctor R :=
  eqToIso (finiteToStableSuccessorFunctor_eq R n).symm ≪≫
    Functor.isoWhiskerLeft
      (((finiteClassifyingCategoryDiagram R).map (homOfLE (Nat.le_add_right n 1))).toFunctor)
      (finiteRightBlockUnitIso R (n + 1)) ≪≫
        eqToIso (congrArg (fun F : (finiteClassifyingCategoryDiagram R).obj n ⥤
          ClassifyingCategory R => F ⋙ blockSumRightClassifyingFunctor R)
            (finiteToStableSuccessorFunctor_eq R n))

private theorem finiteRightUnitBundledClassifyingTransport
    {a b c d : Cat.of (ClassifyingCategory R)}
    (hab : a = b) (hcd : c = d) (g : (StableGL R)ᵐᵒᵖ) :
    (eqToHom hab : a ⟶ b) ≫ (show b ⟶ c from g) ≫ (eqToHom hcd : c ⟶ d) =
      (show a ⟶ d from g) := by
  cases hab
  cases hcd
  simp only [eqToHom_refl, Category.id_comp]
  exact @Category.comp_id (Cat.of (ClassifyingCategory R))
    (Cat.str (Cat.of (ClassifyingCategory R))) a c (show a ⟶ c from g)

private theorem finiteNextRightUnitIsoRecipe_hom_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteNextRightUnitIsoRecipe R n).hom.app x =
      MulOpposite.op (rightBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ := by
  simp only [finiteNextRightUnitIsoRecipe, Iso.trans_hom, eqToIso.hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, eqToHom_app, Functor.whiskerLeft_app,
    finiteRightBlockUnitIso_hom_app]
  exact finiteRightUnitBundledClassifyingTransport R _ _
    (MulOpposite.op (rightBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹)

private theorem finiteNextRightUnitIsoRecipe_inv_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteNextRightUnitIsoRecipe R n).inv.app x =
      MulOpposite.op (rightBlockElementaryConjugator R (n + 1) : StableGL R) := by
  have h := congrArg (fun g => MulOpposite.unop g)
    (finiteNextRightUnitIsoRecipe_hom_app R n x)
  have hInv := congrArg (fun g : (StableGL R)ᵐᵒᵖ => MulOpposite.unop g)
    (Iso.hom_inv_id_app (finiteNextRightUnitIsoRecipe R n) x)
  apply MulOpposite.unop_injective
  change MulOpposite.unop ((finiteNextRightUnitIsoRecipe R n).hom.app x) *
    MulOpposite.unop ((finiteNextRightUnitIsoRecipe R n).inv.app x) = 1 at hInv
  rw [h] at hInv
  exact (inv_mul_eq_one.mp hInv).symm

/-- The actual next right comparison on the ORIGINAL finite source, with
no newly selected conjugator or naturality witness. -/
public def finiteNextRightBlockUnitIso (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ≅
      (finiteToStableCategoryMap R n).toFunctor ⋙ blockSumRightClassifyingFunctor R :=
  finiteNextRightUnitIsoRecipe R n

/-- Its complete forward component is the original normalized next matrix. -/
public theorem finiteNextRightBlockUnitIso_hom_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteNextRightBlockUnitIso R n).hom.app x =
      MulOpposite.op (rightBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ :=
  finiteNextRightUnitIsoRecipe_hom_app R n x

/-- Its complete inverse component is the SAME original next matrix. -/
public theorem finiteNextRightBlockUnitIso_inv_app (n : ℕ)
    (x : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteNextRightBlockUnitIso R n).inv.app x =
      MulOpposite.op (rightBlockElementaryConjugator R (n + 1) : StableGL R) :=
  finiteNextRightUnitIsoRecipe_inv_app R n x

private theorem finiteNextRightUnitIsoRecipe_hom_computed (n : ℕ) :
    (finiteNextRightBlockUnitIso R n).hom =
      eqToHom (finiteToStableSuccessorFunctor_eq R n).symm ≫
        Functor.whiskerLeft
          (((finiteClassifyingCategoryDiagram R).map (homOfLE (Nat.le_add_right n 1))).toFunctor)
          (finiteRightBlockUnitIso R (n + 1)).hom ≫
            eqToHom (congrArg (fun F : (finiteClassifyingCategoryDiagram R).obj n ⥤
              ClassifyingCategory R => F ⋙ blockSumRightClassifyingFunctor R)
                (finiteToStableSuccessorFunctor_eq R n)) := by
  unfold finiteNextRightBlockUnitIso finiteNextRightUnitIsoRecipe
  simp only [Iso.trans_hom, eqToIso.hom, Functor.isoWhiskerLeft_hom]

/-- The ENTIRE next right-unit prism is the original next prism restricted
along the ORIGINAL successor nerve map. -/
public theorem finiteNextRightBlockUnitIso_nerveHomotopyMap_restriction (n : ℕ) :
    NatTrans.nerveHomotopyMap (finiteNextRightBlockUnitIso R n).hom =
      (nerveMap
        (((finiteClassifyingCategoryDiagram R).map
          (homOfLE (Nat.le_add_right n 1))).toFunctor) ▷ (Δ[1] : SSet.{u})) ≫
            NatTrans.nerveHomotopyMap (finiteRightBlockUnitIso R (n + 1)).hom := by
  let I := ((finiteClassifyingCategoryDiagram R).map
    (homOfLE (Nat.le_add_right n 1))).toFunctor
  let α := (finiteRightBlockUnitIso R (n + 1)).hom
  have ht := NatTrans.nerveHomotopyMap_eqToHomEndpoints
    (finiteToStableSuccessorFunctor_eq R n)
    (congrArg (fun F : (finiteClassifyingCategoryDiagram R).obj n ⥤
      ClassifyingCategory R => F ⋙ blockSumRightClassifyingFunctor R)
        (finiteToStableSuccessorFunctor_eq R n)) (Functor.whiskerLeft I α)
  rw [finiteNextRightUnitIsoRecipe_hom_computed]
  exact ht.trans (NatTrans.nerveHomotopyMap_precomp I α).symm

/-- The actual difference of both WHOLE original right-unit comparisons. -/
public abbrev finiteRightUnitDifferenceLoop (n : ℕ) :
    (finiteToStableCategoryMap R n).toFunctor ⟶ (finiteToStableCategoryMap R n).toFunctor :=
  (finiteRightBlockUnitIso R n).hom ≫ (finiteNextRightBlockUnitIso R n).inv

private theorem finiteRightUnitInactiveStableMatrixHom_set_cast
    {N : ℕ} {s t : Set (Fin N)}
    [ds : DecidablePred (· ∈ s)] [dt : DecidablePred (· ∈ t)]
    (h : s = t) (g : Matrix.GeneralLinearGroup (Equiv.Perm.InactivePaddedIndex s) R) :
    inactiveStableMatrixHom R N t
        (Matrix.GeneralLinearGroup.reindexMulEquiv
          (Equiv.cast (congrArg (fun q : Set (Fin N) =>
            Equiv.Perm.InactivePaddedIndex q) h)) g) =
      inactiveStableMatrixHom R N s g := by
  cases h
  have hdict : ds = dt := Subsingleton.elim _ _
  cases hdict
  have hreindex :
      Matrix.GeneralLinearGroup.reindexMulEquiv
        (Equiv.refl (Equiv.Perm.InactivePaddedIndex s)) g = g := by
    apply Units.ext
    simpa only [Matrix.GeneralLinearGroup.coe_reindexMulEquiv] using
      (Matrix.reindex_refl_refl
        (g.val : Matrix (Equiv.Perm.InactivePaddedIndex s)
          (Equiv.Perm.InactivePaddedIndex s) R))
  simp only [Equiv.cast_refl, hreindex]

/-- The whole natural-transformation difference is its COMPUTED perfect
inactive loop, including the original active functor and normalized order. -/
public theorem finiteRightUnitDifferenceLoop_eq_inactive (n : ℕ) :
    finiteRightUnitDifferenceLoop R n =
      finiteInactiveClassifyingLoop R (rightUnitCommonRank_bound.{u} n)
        (rightUnitDifferencePerfectFactor R n) := by
  have hFactor :
      inactiveStableMatrixHom R (rightUnitCommonRank.{u} n)
        (initialActiveIndices n (rightUnitCommonRank.{u} n))
        (rightUnitDifferencePerfectFactor R n).val =
          (rightBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ *
            (rightBlockElementaryConjugator R n : StableGL R) :=
    (finiteRightUnitInactiveStableMatrixHom_set_cast R
      (rightUnitPermutationStages_activeSet_eq.{u} n)
      (rightUnitDifferencePerfectFactor R n).val).symm.trans
        (rightUnitDifferencePerfectFactor_reconstruct R n)
  apply NatTrans.ext
  funext c
  rw [NatTrans.comp_app, finiteRightBlockUnitIso_hom_app,
    finiteNextRightBlockUnitIso_inv_app, finiteInactiveClassifyingLoop_app,
    hFactor, classifyingCategory_comp_as_mul]
  apply MulOpposite.unop_injective
  change (rightBlockElementaryConjugator R n : StableGL R)⁻¹ *
      (rightBlockElementaryConjugator R (n + 1) : StableGL R) =
    ((rightBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ *
      (rightBlockElementaryConjugator R n : StableGL R))⁻¹
  rw [mul_inv_rev, inv_inv]

/-- Its WHOLE original nerve cylinder is the same perfect inactive family
prism; no selected-point trace replaces the active parameter. -/
public theorem finiteRightUnitDifferenceLoop_nerveHomotopyMap (n : ℕ) :
    NatTrans.nerveHomotopyMap (finiteRightUnitDifferenceLoop R n) =
      NatTrans.nerveHomotopyMap
        (initialInactiveClassifyingLoop R (rightUnitCommonRank_bound.{u} n)
          (rightUnitDifferencePerfectFactor R n)) := by
  rw [finiteRightUnitDifferenceLoop_eq_inactive, finiteInactiveClassifyingLoop_nerveHomotopyMap]

end AlgebraicKTheory.StableGL

end
