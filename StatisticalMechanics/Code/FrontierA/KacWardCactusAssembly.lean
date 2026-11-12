/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.KacWardUnicyclicAssembly

open scoped BigOperators

namespace StatMech.FrontierA

open Matrix



noncomputable def kwCycleFamilyDiagonal
    {E Block : Type*} [Fintype E] [DecidableEq E]
    [Fintype Block] [DecidableEq Block]
    (sigma : Block -> Equiv.Perm E)
    (weight : Block -> Bool -> E -> ℂ) :
    Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ :=
  Matrix.blockDiagonal fun b =>
    kwTwoOrientationCycleTransition (sigma b) (weight b)



noncomputable def kwCycleFamilyExtension
    {E Block : Type*} [Fintype E] [DecidableEq E]
    [Fintype Block] [DecidableEq Block]
    (sigma : Block -> Equiv.Perm E)
    (weight : Block -> Bool -> E -> ℂ)
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ) :
    Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ :=
  kwCycleFamilyDiagonal sigma weight + forward



def kwCycleBlockEquiv {E Block : Type*} (b : Block) :
    {d : (E × Bool) × Block // d.2 = b} ≃ (E × Bool) where
  toFun d := d.1.1
  invFun d := ⟨(d, b), rfl⟩
  left_inv d := by
    apply Subtype.ext
    exact Prod.ext rfl d.property.symm
  right_inv d := rfl


def kwStrictlyForward
    {E Block : Type*} [LT Block]
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ) : Prop :=
  ∀ i j, forward i j ≠ 0 -> i.2 < j.2


theorem kwStrictlyForward.blockTriangular
    {E Block : Type*} [Preorder Block]
    {forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ}
    (hforward : kwStrictlyForward forward) :
    forward.BlockTriangular Prod.snd := by
  intro i j hji
  by_contra hne
  exact (not_le_of_gt (hforward i j hne)) hji.le


theorem kwStrictlyForward.eq_zero_of_same_block
    {E Block : Type*} [Preorder Block]
    {forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ}
    (hforward : kwStrictlyForward forward)
    {i j : (E × Bool) × Block} (hij : i.2 = j.2) :
    forward i j = 0 := by
  by_contra hne
  exact (hforward i j hne).ne (by simpa using hij)



theorem kw_cycleFamily_diagonalBlock
    {E Block : Type*} [Fintype E] [DecidableEq E]
    [Fintype Block] [DecidableEq Block] [LinearOrder Block]
    (sigma : Block -> Equiv.Perm E)
    (weight : Block -> Bool -> E -> ℂ)
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ)
    (hforward : kwStrictlyForward forward) (b : Block) :
    Matrix.reindex (kwCycleBlockEquiv b) (kwCycleBlockEquiv b)
        ((kwCycleFamilyExtension sigma weight forward).toSquareBlock Prod.snd b) =
      kwTwoOrientationCycleTransition (sigma b) (weight b) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.toSquareBlock_def]
  change kwCycleFamilyExtension sigma weight forward (i, b) (j, b) = _
  have hz : forward (i, b) (j, b) = 0 :=
    hforward.eq_zero_of_same_block (i := (i, b)) (j := (j, b)) rfl
  rw [kwCycleFamilyExtension, Matrix.add_apply, hz, add_zero]
  exact Matrix.blockDiagonal_apply_eq _ _ _ b



theorem kw_det_cycleFamilyExtension
    {E Block : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype Block] [DecidableEq Block] [LinearOrder Block]
    (sigma : Block -> Equiv.Perm E)
    (weight : Block -> Bool -> E -> ℂ)
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ)
    (hforward : kwStrictlyForward forward) :
    (1 - kwCycleFamilyExtension sigma weight forward).det =
      ∏ b : Block, (1 - kwTwoOrientationCycleTransition (sigma b) (weight b)).det := by
  have htriangular :
      (kwCycleFamilyExtension sigma weight forward).BlockTriangular Prod.snd :=
    (Matrix.blockTriangular_blockDiagonal _).add hforward.blockTriangular
  rw [kw_det_one_sub_blockTriangular _ _ htriangular]
  apply Finset.prod_congr rfl
  intro b _
  rw [<- Matrix.det_reindex_self (kwCycleBlockEquiv b)]
  congr 1
  ext i j
  have hblock := congrFun (congrFun
    (kw_cycleFamily_diagonalBlock sigma weight forward hforward b) i) j
  change (kwCycleFamilyExtension sigma weight forward).toSquareBlock Prod.snd b
    ((kwCycleBlockEquiv b).symm i) ((kwCycleBlockEquiv b).symm j) = _ at hblock
  change (1 - (kwCycleFamilyExtension sigma weight forward).toSquareBlock Prod.snd b)
    ((kwCycleBlockEquiv b).symm i) ((kwCycleBlockEquiv b).symm j) = _
  rw [Matrix.sub_apply]
  rw [hblock]
  simp [Matrix.one_apply]



noncomputable def kwAbstractCactusEvenPolynomial
    {E Block : Type*} [Fintype E] [Fintype Block]
    (edgeWeight : Block -> E -> ℂ) : ℂ :=
  ∏ b, kwAbstractCycleEvenPolynomial (edgeWeight b)




theorem kacWard_abstract_cactus_of_phase_sign
    {E Block : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype Block] [DecidableEq Block] [LinearOrder Block]
    (sigma : Block -> Equiv.Perm E)
    (edgeWeight : Block -> E -> ℂ)
    (phase : Block -> Bool -> E -> ℂ)
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ)
    (hforward : kwStrictlyForward forward)
    (hcycle : ∀ b, (sigma b).IsCycle)
    (hfree : ∀ b i, sigma b i ≠ i)
    (hphase : ∀ b o, ∏ i, phase b o i = -1) :
    (1 - kwCycleFamilyExtension sigma
        (fun b o i => edgeWeight b i * phase b o i) forward).det =
      (kwAbstractCactusEvenPolynomial edgeWeight) ^ 2 := by
  rw [kw_det_cycleFamilyExtension sigma _ forward hforward]
  have hblock : ∀ b,
      (1 - kwTwoOrientationCycleTransition (sigma b)
        (fun o i => edgeWeight b i * phase b o i)).det =
        (kwAbstractCycleEvenPolynomial (edgeWeight b)) ^ 2 := by
    intro b
    exact kacWard_abstract_cycle_of_phase_sign (sigma b) (edgeWeight b)
      (phase b) (hcycle b) (hfree b) (hphase b)
  simp_rw [hblock]
  unfold kwAbstractCactusEvenPolynomial
  rw [Finset.prod_pow]

end StatMech.FrontierA
