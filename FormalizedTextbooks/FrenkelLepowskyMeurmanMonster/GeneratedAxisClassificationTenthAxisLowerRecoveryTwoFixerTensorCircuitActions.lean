/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorCircuitData
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! Ungated exact two-fixer full tensor circuit assembly. All source bindings remain explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Distinct genuine coordinate Hadamards commute as actual real operators. -/
theorem generatedTenth_two_fixer_tensor_hadamard_commute (k l : Fin 12) :
    Commute (generatedNinthLowerSpinHadamard k) (generatedNinthLowerSpinHadamard l) := by
  by_cases hkl : k = l
  · subst l
    exact Commute.refl _
  change generatedNinthLowerSpinHadamard k * generatedNinthLowerSpinHadamard l =
    generatedNinthLowerSpinHadamard l * generatedNinthLowerSpinHadamard k
  apply Subtype.ext
  apply LinearEquiv.ext
  intro f
  funext t
  change (generatedNinthLowerSpinHadamard k).val
    ((generatedNinthLowerSpinHadamard l).val f) t =
      (generatedNinthLowerSpinHadamard l).val ((generatedNinthLowerSpinHadamard k).val f) t
  have hk : (t + Pi.single l 1 : SpinIndex) k = t k := by simp [hkl]
  have hl : (t + Pi.single k 1 : SpinIndex) l = t l := by simp [Ne.symm hkl]
  have hv : t + Pi.single k 1 + Pi.single l 1 = t + Pi.single l 1 + Pi.single k 1 := by abel
  simp only [generatedNinth_lower_spin_hadamard_apply, hk, hl]
  rw [hv]
  ring

private theorem hadamard_pairwise (w : List (Fin 12)) :
    (w.map generatedNinthLowerSpinHadamard).Pairwise Commute := by
  induction w with
  | nil => simp
  | cons k w ih =>
    simp only [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih⟩
    intro x hx
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
    exact generatedTenth_two_fixer_tensor_hadamard_commute k l

private theorem pair_prod (w : List (Fin 12 × Fin 12)) :
    ((w.flatMap (fun p => [p.1, p.2])).map generatedNinthLowerSpinHadamard).prod =
      (w.map generatedTwelfthSpinTensorPair).prod := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [ih]
    rfl

set_option maxHeartbeats 1000000 in
-- Only the two complete original lists of at most10 actual Fourier coordinates are checked here.
/-- The ascending cached pair chain is a permutation of all actual original Fourier factors. -/
theorem generatedTenth_two_fixer_tensor_pair_permutation : ∀ g : Fin 2,
    (generatedTenthTwoFixerTensorHadamardWord g).Perm
      ((generatedTenthTwoFixerTensorPairs g).reverse.flatMap (fun p => [p.1, p.2])) := by
  decide +kernel

/-- Genuine commutation identifies the complete ascending packed chain with the original spin word.
-/
theorem generatedTenth_two_fixer_tensor_pair_word (g : Fin 2) :
    ((generatedTenthTwoFixerTensorHadamardWord g).map generatedNinthLowerSpinHadamard).prod =
      (((generatedTenthTwoFixerTensorPairs g).reverse.map generatedTwelfthSpinTensorPair).prod) :=
        by
  have h := (generatedTenth_two_fixer_tensor_pair_permutation g).map generatedNinthLowerSpinHadamard
  exact (h.prod_eq' (hadamard_pairwise _)).trans (pair_prod _)

/-- The actual compact source factors into its genuine pre, complete pair chain, and post. -/
theorem generatedTenth_two_fixer_tensor_factorization (g : Fin 2) :
    generatedTenthTwoFixerTensorSpin g = generatedTenthTwoFixerTensorPost g *
      (((generatedTenthTwoFixerTensorPairs g).reverse.map generatedTwelfthSpinTensorPair).prod) *
        generatedTenthTwoFixerTensorPre g := by
  have h : generatedTenthTwoFixerTensorSpin g = generatedTenthTwoFixerTensorPost g *
      ((generatedTenthTwoFixerTensorHadamardWord g).map generatedNinthLowerSpinHadamard).prod *
        generatedTenthTwoFixerTensorPre g := by
    fin_cases g <;> simp [generatedTenthTwoFixerTensorSpin, generatedTenthTwoFixerTensorPost,
      generatedTenthTwoFixerTensorPre, generatedTenthTwoFixerTensorHadamardWord,
      generatedTenthTwoFixerTensorFirstPhase, generatedTenthTwoFixerTensorSecondPhase,
      generatedTenthTwoFixerTensorPauli, generatedTenthTwoFixerTensorLeft,
      generatedTenthTwoFixerTensorRight, generatedTenthAxisLowerRecoveryCompactSpin,
      generatedTenthAxisLowerRecoveryJointCompactSpin, mul_assoc]
  rw [h, generatedTenth_two_fixer_tensor_pair_word]

/-- The original pre source evaluator binds the genuine entire real spin operator. -/
theorem generatedTenth_two_fixer_tensor_pre_embed (g : Fin 2) (v : NortonUIntegerVector) :
    (generatedTenthTwoFixerTensorPre g).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedTenthTwoFixerTensorPreInteger g v) := by
  ext t
  simp only [generatedTenthTwoFixerTensorPreInteger, nortonUIntegerEmbed,
    nortonUIntegerLabel_inverse]
  change qSign (monsterMonomialQuadratic (generatedTenthTwoFixerTensorSecondPhase g) t) *
    (v (nortonUIntegerLabel ((generatedTenthTwoFixerTensorRight g).symm t)) : ℝ) = _
  rw [Int.cast_mul, generatedAxisGlobalIntSign_real]

/-- The original post evaluator binds the actual complete central Pauli correction. -/
theorem generatedTenth_two_fixer_tensor_post_embed (g : Fin 2) (v : NortonUIntegerVector) :
    (generatedTenthTwoFixerTensorPost g).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedTenthTwoFixerTensorPostInteger g v) := by
  ext t
  simp only [generatedTenthTwoFixerTensorPostInteger, nortonUIntegerEmbed,
    nortonUIntegerLabel_inverse]
  change qSign (spinPhase (generatedTenthTwoFixerTensorPauli g) t) *
    (qSign (monsterMonomialQuadratic (generatedTenthTwoFixerTensorFirstPhase g)
      ((generatedTenthTwoFixerTensorLeft g).symm
        (t + spinTranslation (generatedTenthTwoFixerTensorPauli g)))) *
      (v (nortonUIntegerLabel ((generatedTenthTwoFixerTensorLeft g).symm
        (t + spinTranslation (generatedTenthTwoFixerTensorPauli g)))) : ℝ)) = _
  simp only [Int.cast_mul, generatedAxisGlobalIntSign_real]
  ring

set_option maxHeartbeats 2000000 in
-- The complete genuine pair replay unfolds the actual full tensor state evaluators.
/-- Complete Start, pair and Finish equations give the genuine whole spin column circuit. -/
theorem generatedTenth_two_fixer_tensor_column_circuit
    (hstart : GeneratedTenthTwoFixerTensorStartCondition)
    (hpairs : GeneratedTenthTwoFixerTensorPairCondition)
    (hfinish : GeneratedTenthTwoFixerTensorFinishCondition) (g : Fin 2) (j : Fin 24) :
    (generatedTenthTwoFixerTensorSpin g).val
      (nortonUIntegerEmbed (fun n => generatedTenthTwoFixerTensorSpatialInteger g n j)) =
        (generatedTenthTwoFixerTensorDenominator g : ℝ) •
          nortonUIntegerEmbed (fun n => generatedTenthTwoFixerTensorInput n j) := by
  rw [generatedTenth_two_fixer_tensor_factorization]
  change (generatedTenthTwoFixerTensorPost g).val
    ((((generatedTenthTwoFixerTensorPairs g).reverse.map generatedTwelfthSpinTensorPair).prod).val
      ((generatedTenthTwoFixerTensorPre g).val
        (nortonUIntegerEmbed (fun n => generatedTenthTwoFixerTensorSpatialInteger g n j)))) = _
  rw [generatedTenth_two_fixer_tensor_pre_embed]
  have hzero : nortonUIntegerEmbed (generatedTenthTwoFixerTensorPreInteger g
      (fun n => generatedTenthTwoFixerTensorSpatialInteger g n j)) =
        (generatedTenthTwoFixerTensorDenominator g : ℝ) •
          nortonUIntegerEmbed (fun n => generatedTenthTwoFixerTensorState g 0 n j) := by
    ext t
    simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast (hstart g j (nortonUIntegerLabel t)).symm
  rw [hzero, map_smul]
  have hstep : ∀ s p, (generatedTenthTwoFixerTensorPairs g)[s]? = some p → ∀ n,
      generatedTwelfthSpinTensorFourierInteger p.1
        (generatedTwelfthSpinTensorFourierInteger p.2
          (fun m => generatedTenthTwoFixerTensorState g s m j)) n =
            2 * generatedTenthTwoFixerTensorState g (s + 1) n j := by
    intro s p hp n
    exact hpairs g j s p hp n
  rw [generatedTwelfth_spin_tensor_pair_replay _
    (fun s n => generatedTenthTwoFixerTensorState g s n j)
    generatedTwelfth_spin_tensor_fourier_addresses hstep, map_smul,
    generatedTenth_two_fixer_tensor_post_embed]
  have hfinal : generatedTenthTwoFixerTensorPostInteger g
      (fun n => generatedTenthTwoFixerTensorState g
        (generatedTenthTwoFixerTensorPairs g).length n j) =
          (fun n => generatedTenthTwoFixerTensorInput n j) := by
    funext n
    exact (hfinish g j n).1.trans (hfinish g j n).2
  rw [hfinal]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
