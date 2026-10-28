/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactAnchorPair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactAnchorPair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactAnchorPair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactAnchorPair03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactAnchorPair04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactAnchorPair05

/-! Genuine full-Hadamard source factors give the exact compact delta anchor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000
open scoped BigOperators

/-- Every complete source Hadamard pair condition holds. -/
theorem generatedTenth_source_compact_anchor_all_pairs (p : Fin 6) :
    generatedTenthSourceCompactAnchorPairCondition p := by
  fin_cases p
  · exact generatedTenth_source_compact_anchor_pair_00
  · exact generatedTenth_source_compact_anchor_pair_01
  · exact generatedTenth_source_compact_anchor_pair_02
  · exact generatedTenth_source_compact_anchor_pair_03
  · exact generatedTenth_source_compact_anchor_pair_04
  · exact generatedTenth_source_compact_anchor_pair_05

private theorem source_compact_spin_chain_generic
    (w : Fin 6 → SpinHolomorph) (v : Fin 7 → SpinSpace)
    (hs : ∀ p : Fin 6, (w p).val (v p.castSucc) = v p.succ) :
    (generatedAxisGlobalWordChain
      (fun n => w ⟨n % 6, Nat.mod_lt _ (by decide)⟩) 6).val (v 0) = v 6 := by
  have hstep : ∀ n : ℕ, (hn : n ≤ 6) →
      (generatedAxisGlobalWordChain
        (fun m => w ⟨m % 6, Nat.mod_lt _ (by decide)⟩) n).val (v 0) =
      v ⟨n, by omega⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        change (1 : SpinSpace ≃ₗ[ℝ] SpinSpace) (v 0) = v 0
        rfl
    | succ n ih =>
        intro hn
        rw [generatedAxisGlobalWordChain]
        change (w ⟨n % 6, Nat.mod_lt _ (by decide)⟩).val
          ((generatedAxisGlobalWordChain
            (fun m => w ⟨m % 6, Nat.mod_lt _ (by decide)⟩) n).val (v 0)) = _
        rw [ih (by omega)]
        have hm : n % 6 = n := Nat.mod_eq_of_lt (by omega)
        have hs' := hs ⟨n, by omega⟩
        have hc : (⟨n, by omega⟩ : Fin 6).castSucc =
            (⟨n, by omega⟩ : Fin 7) := Fin.ext rfl
        have hn' : (⟨n, by omega⟩ : Fin 6).succ =
            (⟨n + 1, by omega⟩ : Fin 7) := Fin.ext rfl
        rw [hc, hn'] at hs'
        simpa only [hm] using hs' 
  exact hstep 6 (by omega)


/-- The entire original twelve-Hadamard word sends64delta to uniform1. -/
theorem generatedTenth_source_compact_anchor_uniform_scaled :
    generatedTenthSourceCompactAnchorWord.val
      ((64 : ℝ) • Pi.single (0 : SpinIndex) (1 : ℝ)) = fun _ => (1 : ℝ) := by
  have h := source_compact_spin_chain_generic
    generatedTenthSourceCompactAnchorPair
    (fun p => nortonUIntegerEmbed (generatedTenthSourceCompactAnchorPrefix p))
    (fun p => generatedTenth_source_compact_anchor_pair_actual p
      (generatedTenth_source_compact_anchor_all_pairs p))
  have hw : generatedTenthSourceCompactAnchorWord =
      generatedAxisGlobalWordChain (fun p => generatedTenthSourceCompactAnchorPair
        ⟨p % 6, Nat.mod_lt _ (by decide)⟩) 6 := by
    unfold generatedTenthSourceCompactAnchorWord
    rfl
  rw [← hw, generatedTenth_source_compact_anchor_prefix_initial,
    generatedTenth_source_compact_anchor_prefix_final] at h
  exact h

/-- Every original full-Hadamard delta output is exactly+1/64. -/
theorem generatedTenth_source_compact_anchor_uniform :
    generatedTenthSourceCompactAnchorWord.val (Pi.single (0 : SpinIndex) (1 : ℝ)) =
      fun _ => (1 / 64 : ℝ) := by
  have h := generatedTenth_source_compact_anchor_uniform_scaled
  rw [map_smul] at h
  funext t
  have ht := congrFun h t
  simp only [Pi.smul_apply, smul_eq_mul] at ht
  linarith

private theorem permutation_delta (E : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    (monsterMonomialPermutationHolomorph E).val (Pi.single (0 : SpinIndex) (1 : ℝ)) =
      Pi.single (0 : SpinIndex) (1 : ℝ) := by
  funext t
  have hz : E.symm t = 0 ↔ t = 0 := by
    constructor
    · intro h
      have hh := congrArg E h
      simpa only [LinearEquiv.apply_symm_apply, map_zero] using hh
    · intro h
      rw [h, map_zero]
  change ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace) (E.symm t) =
    ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace) t
  simp [Pi.single_apply, hz]

private theorem diagonal_delta (M : Fin 12 → Fin 12 → ZMod 2) :
    (monsterMonomialDiagonalHolomorph M).val (Pi.single (0 : SpinIndex) (1 : ℝ)) =
      Pi.single (0 : SpinIndex) (1 : ℝ) := by
  funext t
  change qSign (monsterMonomialQuadratic M t) *
    ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace) t =
      ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace) t
  by_cases ht : t = 0
  · subst t
    simp [monsterMonomialQuadratic, qSign]
  · simp [ht]

/-- The complete source compact spin coefficient uses its actual Pauli and quadratic signs. -/
theorem generatedTenth_source_compact_anchor_spin :
    (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val
      (Pi.single (0 : SpinIndex) (1 : ℝ)) (golayLabelCoefficients 0) = 1 / 64 := by
  have hword := generatedTenth_source_compact_anchor_uniform
  rw [generatedTenth_source_compact_anchor_word_eq] at hword
  have hphase : spinPhase (generatedTenthAxisLowerRecoverySourceCompactPauli 0)
      (golayLabelCoefficients 0) +
    monsterMonomialQuadratic
      (generatedTwelfthSpinCompactPhase
        (generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows 0))
      ((generatedTenthAxisLowerRecoverySourceCompactLeft 0).symm
        (golayLabelCoefficients 0 +
          spinTranslation (generatedTenthAxisLowerRecoverySourceCompactPauli 0))) = 0 := by
    decide +kernel
  change (spinRepresentation (generatedTenthAxisLowerRecoverySourceCompactPauli 0))
    ((monsterMonomialPermutationHolomorph
      (generatedTenthAxisLowerRecoverySourceCompactLeft 0)).val
      ((monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
        (generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows 0))).val
        ((((generatedTenthAxisLowerRecoverySourceCompactHadamardWord 0).map
          generatedNinthLowerSpinHadamard).prod).val
          ((monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
            (generatedTenthAxisLowerRecoverySourceCompactSecondPhaseRows 0))).val
            ((monsterMonomialPermutationHolomorph
              (generatedTenthAxisLowerRecoverySourceCompactRight 0)).val
              (Pi.single (0 : SpinIndex) (1 : ℝ))))))) (golayLabelCoefficients 0) = _
  rw [permutation_delta, diagonal_delta, hword]
  change qSign (spinPhase (generatedTenthAxisLowerRecoverySourceCompactPauli 0)
    (golayLabelCoefficients 0)) *
    (qSign (monsterMonomialQuadratic (generatedTwelfthSpinCompactPhase
      (generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows 0))
      ((generatedTenthAxisLowerRecoverySourceCompactLeft 0).symm
        (golayLabelCoefficients 0 +
          spinTranslation (generatedTenthAxisLowerRecoverySourceCompactPauli 0)))) *
        (1 / 64)) = 1 / 64
  rw [← mul_assoc, ← qSign_add, hphase, qSign_zero, one_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
