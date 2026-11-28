/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleCoset
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleCoordinates
public import MathlibExt.AlgebraicTopology.SemiSimplicialObject.SimplicialComparison
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Tactic.NormNum

/-!
# Small shuffle cosets and simplicial restriction

Empty block-permutation cosets have one element; the (1,1) coset space has
two. The swapped ordered shuffle has negative sign and is recovered by the
canonical coset equivalence. A repeated simplex edge inserts the unit.
For constant integer simplicial chains, the restriction comparison acts as
the identity, commutes with doubling, and preserves a nonzero differential.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology AlgebraicTopology.EilenbergZilber
open scoped Simplicial

namespace ShuffleRestrictionExamples

example : Nat.card (Equiv.Perm.ModSumCongr (Fin 0) (Fin 0)) = 1 := by
  rw [Nat.card_congr ((Shuffle.cosetEquiv 0 0).trans Shuffle.equivLeftPositions)]
  rw [Set.powersetCard.card]
  simp

example : Nat.card (Equiv.Perm.ModSumCongr (Fin 1) (Fin 1)) = 2 := by
  rw [Nat.card_congr ((Shuffle.cosetEquiv 1 1).trans Shuffle.equivLeftPositions)]
  rw [Set.powersetCard.card]
  simp

private def swapped : Shuffle 1 1 where
  perm := Equiv.swap (0 : Fin 2) 1
  isShuffle := by
    constructor
    · intro i j hij
      exact False.elim ((ne_of_lt hij) (Subsingleton.elim i j))
    · intro i j hij
      exact False.elim ((ne_of_lt hij) (Subsingleton.elim i j))

example :
    Shuffle.cosetEquiv 1 1 (Quotient.mk'' (Shuffle.cosetRepresentative 1 1 swapped)) =
        swapped ∧
      Equiv.Perm.sign (Shuffle.cosetRepresentative 1 1 swapped) = (-1 : ℤˣ) := by
  constructor
  · simpa only [Shuffle.cosetEquiv_symm_apply] using
      (Shuffle.cosetEquiv 1 1).apply_symm_apply swapped
  · rw [Shuffle.cosetRepresentative_sign]
    simp [swapped]

example : SimplexCategory.pullbackEdges (SimplexCategory.σ (0 : Fin 1))
    (Fin.elim0 : Fin 0 → ℤ) 0 = 1 := by
  simp [SimplexCategory.pullbackEdges]

example : SimplexCategory.pullbackEdges (SimplexCategory.σ (1 : Fin 2))
    ![(7 : ℤ)] = ![7, 1] := by
  have h := SimplexCategory.pullbackEdges_σ_comp (𝟙 ⦋1⦌) (1 : Fin 2) ![(7 : ℤ)]
  simpa only [Category.comp_id, SimplexCategory.pullbackEdges_id] using h

private abbrev Z : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
private abbrev X : SimplicialObject (ModuleCat.{0} ℤ) :=
  (Functor.const SimplexCategoryᵒᵖ).obj Z
private def double : Z ⟶ Z := ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ (2 : ℤ))
private def f : X ⟶ X := (Functor.const SimplexCategoryᵒᵖ).map double

example :
    ((SemiSimplicialAlternatingFaceMapComplex.ofSimplicialIso X).hom.f 2).hom 3 = 3 ∧
      (f.app (Opposite.op ⦋2⦌)).hom 3 = 6 := by
  constructor
  · have h := SemiSimplicialAlternatingFaceMapComplex.ofSimplicialIso_hom_f X 2
    simpa using congrArg (fun k : Z ⟶ Z => k.hom 3) h
  · change (2 : ℤ) • 3 = 6
    norm_num

example :
    (semiSimplicialAlternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
        (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op f) ≫
        (SemiSimplicialAlternatingFaceMapComplex.ofSimplicialIso X).hom =
      (SemiSimplicialAlternatingFaceMapComplex.ofSimplicialIso X).hom ≫
        (alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map f :=
  SemiSimplicialAlternatingFaceMapComplex.ofSimplicialIso_naturality f

example : ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).obj X).d 2 1 ≠ 0 := by
  have hd : ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).obj X).d 2 1 = 𝟙 Z := by
    rw [alternatingFaceMapComplex_obj_d]
    change (∑ i : Fin 3, (-1 : ℤ) ^ i.val • (𝟙 Z)) = 𝟙 Z
    simp [Fin.sum_univ_succ]
  rw [hd]
  intro hz
  have h := congrArg (fun k : Z ⟶ Z => k.hom 1) hz
  norm_num at h

end ShuffleRestrictionExamples
