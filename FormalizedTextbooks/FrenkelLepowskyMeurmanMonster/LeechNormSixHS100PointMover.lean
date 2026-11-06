/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100PointMoverData

/-! A literal original Conway word fixes the complete canonical flag and moves its positive pair. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The actual original permutations evaluated from the four literal generator words. -/
def leechNormSixHS100PointMoverPermutation (k : Fin 4) : golayAutomorphismSubgroup :=
  golayGeneratingWord (leechNormSixHS100PointMoverPermutationWords k)

/-- The certified arrays are the actual physical inverse permutations of the literal original words. -/
theorem leechNormSixHS100PointMover_permutation_inverse (k : Fin 4) (i : Fin 24) :
    (leechNormSixHS100PointMoverPermutation k).val.symm i =
      leechNormSixHS100PointMoverPermutationInverse k i := by
  apply (leechNormSixHS100PointMoverPermutation k).val.injective
  rw [Equiv.apply_symm_apply]
  change i = (golayGeneratingWord (leechNormSixHS100PointMoverPermutationWords k)).val
    (leechNormSixHS100PointMoverPermutationInverse k i)
  rw [leechRootedA2GeneratingWord_apply, leechNormSixHS100PointMover_permutation_certificate]

/-- Every original permutation step retains its full actual integer coordinate action. -/
theorem leechNormSixHS100PointMover_permutation_action (k : Fin 4) (u : leechIntegral) :
    (leechIntegralAction (golayPermutationIsometry (leechNormSixHS100PointMoverPermutation k)) u).val =
      fun i => u.val (leechNormSixHS100PointMoverPermutationInverse k i) := by
  rw [leechNormSixHS100Permutation_action]
  funext i
  exact congrArg u.val (leechNormSixHS100PointMover_permutation_inverse k i)

/-- The nine chronological steps use only original Mathieu permutations, actual Golay signs, and original Xi. -/
def leechNormSixHS100PointMoverStep (s : Fin 9) : leechIsomSubgroup :=
  match s.val with
  | 0 => golayPermutationIsometry (leechNormSixHS100PointMoverPermutation 0)
  | 1 => golaySignIsometry (leechNormSixHS100PointMoverSign 2816)
  | 2 => co1XiIsometry
  | 3 => co1XiIsometry
  | 4 => golayPermutationIsometry (leechNormSixHS100PointMoverPermutation 1)
  | 5 => co1XiIsometry
  | 6 => golayPermutationIsometry (leechNormSixHS100PointMoverPermutation 2)
  | 7 => golaySignIsometry (leechNormSixHS100PointMoverSign 1)
  | _ => golayPermutationIsometry (leechNormSixHS100PointMoverPermutation 3)

/-- The original actions agree with every complete integer step and its original Xi denominator. -/
theorem leechNormSixHS100PointMover_step_action (s : Fin 9) (u : leechIntegral) :
    leechNormSixHS100PointMoverStepScale s •
      (leechIntegralAction (leechNormSixHS100PointMoverStep s) u).val =
        leechNormSixHS100PointMoverStepNumerator s u.val := by
  fin_cases s
  · simpa [leechNormSixHS100PointMoverStepScale, leechNormSixHS100PointMoverStep,
      leechNormSixHS100PointMoverStepNumerator] using leechNormSixHS100PointMover_permutation_action 0 u
  · simpa [leechNormSixHS100PointMoverStepScale, leechNormSixHS100PointMoverStep,
      leechNormSixHS100PointMoverStepNumerator] using leechIntegralAction_golaySign (leechNormSixHS100PointMoverSign 2816) u
  · exact co1Xi_integral_double u
  · exact co1Xi_integral_double u
  · simpa [leechNormSixHS100PointMoverStepScale, leechNormSixHS100PointMoverStep,
      leechNormSixHS100PointMoverStepNumerator] using leechNormSixHS100PointMover_permutation_action 1 u
  · exact co1Xi_integral_double u
  · simpa [leechNormSixHS100PointMoverStepScale, leechNormSixHS100PointMoverStep,
      leechNormSixHS100PointMoverStepNumerator] using leechNormSixHS100PointMover_permutation_action 2 u
  · simpa [leechNormSixHS100PointMoverStepScale, leechNormSixHS100PointMoverStep,
      leechNormSixHS100PointMoverStepNumerator] using leechIntegralAction_golaySign (leechNormSixHS100PointMoverSign 1) u
  · simpa [leechNormSixHS100PointMoverStepScale, leechNormSixHS100PointMoverStep,
      leechNormSixHS100PointMoverStepNumerator] using leechNormSixHS100PointMover_permutation_action 3 u

/-- Successive original group products realize the literal chronological Conway word. -/
def leechNormSixHS100PointMoverPrefix : ℕ → leechIsomSubgroup
  | 0 => 1
  | n + 1 => if h : n < 9 then
      leechNormSixHS100PointMoverStep ⟨n, h⟩ * leechNormSixHS100PointMoverPrefix n
    else leechNormSixHS100PointMoverPrefix n

/-- The three original physical vectors whose complete images certify the point mover. -/
def leechNormSixHS100PointMoverSource (k : Fin 3) : leechIntegral :=
  match k.val with
  | 0 => leechNormSixHS100Root
  | 1 => leechNormSixHS100Companion
  | _ => leechNormSixHS100Pair

/-- All initial data are exactly the original full integral vectors. -/
theorem leechNormSixHS100PointMover_source_initial (k : Fin 3) :
    (leechNormSixHS100PointMoverSource k).val = leechNormSixHS100PointMoverVectorData 0 k := by
  fin_cases k
  · exact leechNormSixHS100PointMover_vector_initial.1.symm
  · exact leechNormSixHS100PointMover_vector_initial.2.1.symm
  · exact leechNormSixHS100PointMover_vector_initial.2.2.symm

/-- Every prefix has every original coordinate recorded by the exact vector certificates. -/
theorem leechNormSixHS100PointMover_prefix_coordinates (n : ℕ) (hn : n < 10) (k : Fin 3) :
    (leechIntegralAction (leechNormSixHS100PointMoverPrefix n)
      (leechNormSixHS100PointMoverSource k)).val = leechNormSixHS100PointMoverVectorData ⟨n, hn⟩ k := by
  induction n with
  | zero =>
      change (leechIntegralAction 1 (leechNormSixHS100PointMoverSource k)).val = _
      rw [map_one]
      exact leechNormSixHS100PointMover_source_initial k
  | succ n ih =>
      have h9 : n < 9 := by omega
      have h10 : n < 10 := by omega
      let s : Fin 9 := ⟨n, h9⟩
      rw [leechNormSixHS100PointMoverPrefix, dite_eq_left h9]
      change (leechIntegralAction
        (leechNormSixHS100PointMoverStep s * leechNormSixHS100PointMoverPrefix n)
        (leechNormSixHS100PointMoverSource k)).val = _
      rw [map_mul, LinearEquiv.mul_apply]
      have h := leechNormSixHS100PointMover_step_action s
        (leechIntegralAction (leechNormSixHS100PointMoverPrefix n) (leechNormSixHS100PointMoverSource k))
      rw [ih h10] at h
      have hd := leechNormSixHS100PointMover_vector_step s k
      have he := h.trans hd
      have hindex : s.succ = (⟨n + 1, hn⟩ : Fin 10) := rfl
      rw [hindex] at he
      have hm : leechNormSixHS100PointMoverStepScale s = 1 ∨
          leechNormSixHS100PointMoverStepScale s = 2 := by
        unfold leechNormSixHS100PointMoverStepScale
        split_ifs <;> simp
      funext i
      have hi := congrFun he i
      rcases hm with hm | hm <;> rw [hm] at hi <;>
        simp only [Pi.smul_apply, nsmul_eq_mul] at hi <;> omega

/-- The literal original nine-step Conway point mover. -/
def leechNormSixHS100PointMover : leechIsomSubgroup := leechNormSixHS100PointMoverPrefix 9

/-- The actual point mover is the displayed literal nine-factor original Conway word. -/
theorem leechNormSixHS100PointMover_literal_word :
    leechNormSixHS100PointMover =
      golayPermutationIsometry (leechNormSixHS100PointMoverPermutation 3) *
      golaySignIsometry (leechNormSixHS100PointMoverSign 1) *
      golayPermutationIsometry (leechNormSixHS100PointMoverPermutation 2) * co1XiIsometry *
      golayPermutationIsometry (leechNormSixHS100PointMoverPermutation 1) *
      co1XiIsometry * co1XiIsometry *
      golaySignIsometry (leechNormSixHS100PointMoverSign 2816) *
      golayPermutationIsometry (leechNormSixHS100PointMoverPermutation 0) := by
  simp [leechNormSixHS100PointMover, leechNormSixHS100PointMoverPrefix,
    leechNormSixHS100PointMoverStep, mul_assoc]

/-- The entire original root is fixed by the literal Conway word. -/
theorem leechNormSixHS100PointMover_root_fixed :
    leechIntegralAction leechNormSixHS100PointMover leechNormSixHS100Root = leechNormSixHS100Root := by
  apply Subtype.ext
  exact (leechNormSixHS100PointMover_prefix_coordinates 9 (by decide) 0).trans
    leechNormSixHS100PointMover_vector_final.1

/-- The entire original norm-six companion is fixed by the same literal Conway word. -/
theorem leechNormSixHS100PointMover_companion_fixed :
    leechIntegralAction leechNormSixHS100PointMover leechNormSixHS100Companion =
      leechNormSixHS100Companion := by
  apply Subtype.ext
  exact (leechNormSixHS100PointMover_prefix_coordinates 9 (by decide) 1).trans
    leechNormSixHS100PointMover_vector_final.2.1

/-- Every original positive-pair coordinate is sent to the displayed genuine positive-octad coordinates. -/
theorem leechNormSixHS100PointMover_pair_coordinates :
    (leechIntegralAction leechNormSixHS100PointMover leechNormSixHS100Pair).val =
      leechNormSixHS100PointMoverPairImage :=
  (leechNormSixHS100PointMover_prefix_coordinates 9 (by decide) 2).trans
    leechNormSixHS100PointMover_vector_final.2.2

/-- The literal original Conway word lies in the actual simultaneous flag stabilizer. -/
def leechNormSixHS100PointMoverElement :
    leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion :=
  ⟨leechNormSixHS100PointMover, (leechNormSixActualPairStabilizer_mem _ _ _).mpr
    ⟨leechNormSixHS100PointMover_root_fixed, leechNormSixHS100PointMover_companion_fixed⟩⟩

/-- The actual original positive pair is moved by the literal original flag-stabilizing word. -/
theorem leechNormSixHS100PointMover_moves_pair :
    leechNormSixHS100PointMoverElement • leechNormSixHS100PairPoint ≠ leechNormSixHS100PairPoint := by
  intro h
  have he := congrArg (fun z => z.val.val 0) h
  change (leechIntegralAction leechNormSixHS100PointMover leechNormSixHS100Pair).val 0 =
    leechNormSixHS100Pair.val 0 at he
  rw [leechNormSixHS100PointMover_pair_coordinates] at he
  norm_num [leechNormSixHS100PointMoverPairImage, leechNormSixHS100Pair,
    leechNormSixHS100PairIntegral] at he

/-- The original Mathieu point subgroup and this literal original word generate the whole actual flag stabilizer. -/
theorem leechNormSixHS100PointMover_generates :
    leechNormSixHS100PairPointStabilizer ⊔ Subgroup.zpowers leechNormSixHS100PointMoverElement = ⊤ :=
  leechNormSixHS100PointStabilizer_generate leechNormSixHS100PointMoverElement
    leechNormSixHS100PointMover_moves_pair

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
