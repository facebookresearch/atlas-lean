/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSupportCount

/-! Whole actual source and target octad short packets for the zero bridge. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

/-- The original source2818 and target780 octads retain their certified encoder addresses. -/
def generatedFeasibleContainingZeroOutsideAnchorEndOctad : Fin 2 → Fin 14 := ![10, 6]

/-- The source and fully corrected target root packets are the first and fourth stages. -/
def generatedFeasibleContainingZeroOutsideAnchorEndStage : Fin 2 → Fin 4 := ![0, 3]

/-- Unit coefficients of a positive original octad axis on its actual preferred labels. -/
def generatedFeasibleContainingZeroOutsideAnchorReferenceCoefficient :
    GeneratedFeasibleContainingZeroOutsideAnchorLabel → ℤ
  | Sum.inl (s, _) => if s = 0 then 1 else -1
  | Sum.inr (_, e) =>
      -(if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then 1 else -1)

/-- Every bounded root packet lists distinct preferred labels, including all signs. -/
theorem generatedFeasibleContainingZeroOutsideAnchorRoot_nodup : ∀ k : Fin 4,
    List.Nodup (List.ofFn (generatedFeasibleContainingZeroOutsideAnchorRoot k)) := by
  decide +kernel

/-- The computed support predicate is decided by its two physical bits or its octad address. -/
instance generatedFeasibleContainingZeroOutsideAnchorSupportDecidable (j : Fin 14) :
    (r : GeneratedFeasibleContainingZeroOutsideAnchorLabel) →
      Decidable (generatedFeasibleContainingZeroOutsideAnchorSupport j r)
  | Sum.inl (_, p) => inferInstanceAs (Decidable
      ((golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j).val).testBit
        (generatedAxisGlobalPairCoordinates p).1.val = true ∧
      (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j).val).testBit
        (generatedAxisGlobalPairCoordinates p).2.val = true))
  | Sum.inr (k, _) => inferInstanceAs (Decidable (k = j))

/-- Every source and target address lies in the entire actual octad support. -/
theorem generatedFeasibleContainingZeroOutsideAnchorEnd_support : ∀ k : Fin 2, ∀ n : Fin 120,
    generatedFeasibleContainingZeroOutsideAnchorSupport
      (generatedFeasibleContainingZeroOutsideAnchorEndOctad k)
      (generatedFeasibleContainingZeroOutsideAnchorRoot
        (generatedFeasibleContainingZeroOutsideAnchorEndStage k) n) := by decide +kernel

/-- Each source and target coefficient is the exact original unit Fourier sign. -/
theorem generatedFeasibleContainingZeroOutsideAnchorEnd_coefficient : ∀ k : Fin 2, ∀ n : Fin 120,
    generatedFeasibleContainingZeroOutsideAnchorCoefficient
      (generatedFeasibleContainingZeroOutsideAnchorEndStage k) n =
        generatedFeasibleContainingZeroOutsideAnchorReferenceCoefficient
          (generatedFeasibleContainingZeroOutsideAnchorRoot
            (generatedFeasibleContainingZeroOutsideAnchorEndStage k) n) := by decide +kernel

/-- The actual positive octad Fourier row retains its full original preferred sign. -/
theorem generatedFeasibleContainingZeroOutsideAnchor_octad_coefficient
    (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) 0))).2.1
      (Sum.inr (Sum.inl (o, e))) =
        -(if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then (1 : ℝ) else -1) := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change (trialityOctadAction
    ((trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) 0)).2.2.1 o) e) = _
  have hrow : (trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) 0)).2.2.1 o =
      (-8 : ℝ) • Pi.single 0 1 := by
    funext t
    by_cases ht : t = 0 <;> simp [conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, Pi.single_apply, ht, qSign_zero]
  rw [hrow, map_smul]
  simp [trialityOctadAction, LinearEquiv.trans_apply, trialityHadamardEquiv,
    trialitySignEquiv, trialityNormalizedHadamard, trialityHadamard,
    trialityEvenMask, trialityBitWeight8, Matrix.mulVec, dotProduct]
  split_ifs <;> norm_num

/-- Physical cached reference signs are exactly the entire actual source coefficients. -/
theorem generatedFeasibleContainingZeroOutsideAnchorReferenceCoefficient_actual
    (j : Fin 14) (r : GeneratedFeasibleContainingZeroOutsideAnchorLabel)
    (hr : generatedFeasibleContainingZeroOutsideAnchorSupport j r) :
    (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFeasibleContainingZeroOutsideAnchorOctad j, 0))) 0))).2.1
        (generatedFeasibleContainingZeroOutsideAnchorIndex r) =
      (generatedFeasibleContainingZeroOutsideAnchorReferenceCoefficient r : ℝ) := by
  rcases r with ⟨s, p⟩ | ⟨k, e⟩
  · change _ = ((if s = 0 then 1 else -1 : ℤ) : ℝ)
    rw [generatedFeasibleContainingZeroOutsideAnchorIndex,
      generatedAxis_triality_octad_pair_coordinate]
    change _ ∧ _ at hr
    rw [generatedAxisGlobalPairCoordinates_actual] at hr
    have hmask : griessOctadSignMask
        (generatedFeasibleContainingZeroOutsideAnchorOctad j) 0 = 0 := by
      simp [griessOctadSignMask, trialityEvenMask, trialityBitWeight8]
    simp only [griessShortVector, griessShortIntegral,
      generatedFeasibleContainingZeroOutsideAnchorOctad_label, hmask, Nat.zero_testBit,
      Bool.false_eq_true, ite_false, hr.1, hr.2, ite_true]
    have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    split_ifs <;> norm_num
    all_goals field_simp; nlinarith
  · change k = j at hr
    subst k
    rw [generatedFeasibleContainingZeroOutsideAnchorIndex,
      generatedFeasibleContainingZeroOutsideAnchor_octad_coefficient]
    simp only [generatedFeasibleContainingZeroOutsideAnchorReferenceCoefficient,
      apply_ite, Int.cast_neg, Int.cast_one]
    split_ifs <;> norm_num

/-- Every actual source or target supported short label occurs in its full120-address packet. -/
theorem generatedFeasibleContainingZeroOutsideAnchorEnd_cover (k : Fin 2)
    (r : GriessShortIndex)
    (hr : generatedOctadShortSupport
      (generatedFeasibleContainingZeroOutsideAnchorOctad
        (generatedFeasibleContainingZeroOutsideAnchorEndOctad k)) r) :
    ∃ n : Fin 120,
      generatedFeasibleContainingZeroOutsideAnchorIndex
        (generatedFeasibleContainingZeroOutsideAnchorRoot
          (generatedFeasibleContainingZeroOutsideAnchorEndStage k) n) = r := by
  let S := {s : GriessShortIndex // generatedOctadShortSupport
    (generatedFeasibleContainingZeroOutsideAnchorOctad
      (generatedFeasibleContainingZeroOutsideAnchorEndOctad k)) s}
  let f : Fin 120 → S := fun n => ⟨generatedFeasibleContainingZeroOutsideAnchorIndex
    (generatedFeasibleContainingZeroOutsideAnchorRoot
      (generatedFeasibleContainingZeroOutsideAnchorEndStage k) n),
      (generatedFeasibleContainingZeroOutsideAnchorSupport_actual _ _).mp
        (generatedFeasibleContainingZeroOutsideAnchorEnd_support k n)⟩
  have hf : Function.Injective f := by
    intro i j h
    apply (List.nodup_ofFn.mp (generatedFeasibleContainingZeroOutsideAnchorRoot_nodup
      (generatedFeasibleContainingZeroOutsideAnchorEndStage k)))
    apply generatedFeasibleContainingZeroOutsideAnchorIndex_injective
    exact congrArg Subtype.val h
  have hs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, by
      change Nat.card (Fin 120) = Nat.card S
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, generatedOctad_short_support_card]⟩).2
  obtain ⟨n, hn⟩ := hs ⟨r, hr⟩
  exact ⟨n, congrArg Subtype.val hn⟩

/-- All actual short coordinates of both endpoints are their full finite preferred packets. -/
theorem generatedFeasibleContainingZeroOutsideAnchorEnd_short (k : Fin 2) :
    (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFeasibleContainingZeroOutsideAnchorOctad
        (generatedFeasibleContainingZeroOutsideAnchorEndOctad k), 0))) 0))).2.1 =
      ∑ n : Fin 120,
        (generatedFeasibleContainingZeroOutsideAnchorCoefficient
          (generatedFeasibleContainingZeroOutsideAnchorEndStage k) n : ℝ) •
            Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex
              (generatedFeasibleContainingZeroOutsideAnchorRoot
                (generatedFeasibleContainingZeroOutsideAnchorEndStage k) n)) (1 : ℝ) := by
  let j := generatedFeasibleContainingZeroOutsideAnchorEndOctad k
  let t := generatedFeasibleContainingZeroOutsideAnchorEndStage k
  have hi : Function.Injective (fun n => generatedFeasibleContainingZeroOutsideAnchorIndex
      (generatedFeasibleContainingZeroOutsideAnchorRoot t n)) :=
    generatedFeasibleContainingZeroOutsideAnchorIndex_injective.comp
      (List.nodup_ofFn.mp (generatedFeasibleContainingZeroOutsideAnchorRoot_nodup t))
  funext r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hr : generatedOctadShortSupport
      (generatedFeasibleContainingZeroOutsideAnchorOctad j) r
  · obtain ⟨n, rfl⟩ := generatedFeasibleContainingZeroOutsideAnchorEnd_cover k r hr
    rw [Finset.sum_eq_single n]
    · rw [Pi.single_eq_same, mul_one,
        generatedFeasibleContainingZeroOutsideAnchorEnd_coefficient]
      exact generatedFeasibleContainingZeroOutsideAnchorReferenceCoefficient_actual _ _
        (generatedFeasibleContainingZeroOutsideAnchorEnd_support k n)
    · intro m _ hmn
      rw [Pi.single_eq_of_ne (Ne.symm (hi.ne hmn)), mul_zero]
    · simp
  · rw [generatedAxis_triality_octad_unsupported_zero _ _ _ _ hr]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro n _
    have hn : r ≠ generatedFeasibleContainingZeroOutsideAnchorIndex
        (generatedFeasibleContainingZeroOutsideAnchorRoot t n) := by
      intro he
      apply hr
      rw [he]
      exact (generatedFeasibleContainingZeroOutsideAnchorSupport_actual _ _).mp
        (generatedFeasibleContainingZeroOutsideAnchorEnd_support k n)
    rw [Pi.single_eq_of_ne hn, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
