/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddPairCharacters

/-! Common eigenvectors of actual minus-pair operators have a single lower spin label. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem sign_injective : Function.Injective qSign := by
  intro a b h
  have he : qSign (a + b) = 1 := by rw [qSign_add, h, qSign_sq]
  have hab := (qSign_eq_one_iff _).mp he
  have haa : ∀ c : ZMod 2, c + c = 0 := by decide +kernel
  exact add_left_cancel ((haa a).trans hab.symm)

/-- Two nonzero coordinates of a common actual minus-pair eigenvector have the same lower label. -/
theorem generatedOddSpin_common_eigen_support (v : SpinSpace) (a : Fin 276 → ℝ)
    (h : ∀ p, spinOperator (griessShortQ (Sum.inl (0, p))) v = a p • v)
    (t u : SpinIndex) (ht : v t ≠ 0) (hu : v u ≠ 0) :
    generatedOddSpinLow t = generatedOddSpinLow u := by
  apply generatedOddSpin_pair_characters_separate
  intro p
  have hchar (s : SpinIndex) (hs : v s ≠ 0) :
      qSign (golayEncoder s (griessCoordinatePair p).1 +
        golayEncoder s (griessCoordinatePair p).2) = a p := by
    have he := congrFun (h p) s
    rw [spinOperator_griessPairMinus] at he
    exact mul_right_cancel₀ hs he
  exact sign_injective ((hchar t ht).trans (hchar u hu).symm)

/-- Every coordinate outside that one lower label vanishes. -/
theorem generatedOddSpin_common_eigen_zero (v : SpinSpace) (a : Fin 276 → ℝ)
    (h : ∀ p, spinOperator (griessShortQ (Sum.inl (0, p))) v = a p • v)
    (u : SpinIndex) (hu : v u ≠ 0) (t : SpinIndex)
    (ht : generatedOddSpinLow t ≠ generatedOddSpinLow u) : v t = 0 := by
  by_contra hv
  exact ht (generatedOddSpin_common_eigen_support v a h t u hv hu)

/-- A spin coordinate is reconstructed from its actual lower label and final bit. -/
theorem generatedOddSpinInsert_reconstruct (t : SpinIndex) :
    generatedOddSpinInsert (generatedOddSpinLow t) (t 11) = t := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · change Fin.snoc (α := fun _ : Fin 12 => ZMod 2) (generatedOddSpinLow t) (t 11)
      (Fin.last 11) = t (Fin.last 11)
    exact Fin.snoc_last _ _
  · change Fin.snoc (α := fun _ : Fin 12 => ZMod 2) (generatedOddSpinLow t) (t 11)
      i.castSucc = t i.castSucc
    exact Fin.snoc_castSucc _ _ i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
