/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Freivalds' finite rejection pairing

MIT 6.046J Spring 2015 Lecture 6, printed page 2, uses a nonzero product
discrepancy to reject at least half of the complete binary assignments.
All matrices and arithmetic here are over `ZMod 2` by intentional GF(2) specialization (see
`Freivalds.Basic`); the lecture itself only takes the seed vector binary over a general
coefficient domain.
Translation by a nonzero discrepancy column injects seeds accepted by the
actual executor into seeds it rejects. No error-probability premise is used.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.Matrix

private theorem discrepancy_column {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (wrong : freivaldsMatrix A * freivaldsMatrix B ≠ freivaldsMatrix C) :
    ∃ j, (freivaldsMatrix A * freivaldsMatrix B - freivaldsMatrix C).mulVec
      (Pi.single j 1) ≠ 0 := by
  classical
  let D := freivaldsMatrix A * freivaldsMatrix B - freivaldsMatrix C
  have hD : D ≠ 0 := sub_ne_zero.mpr wrong
  have nonzero : ∃ i j, D i j ≠ 0 := by
    by_contra missing
    apply hD
    funext i j
    by_contra entry
    exact missing ⟨i, j, entry⟩
  obtain ⟨i, j, hij⟩ := nonzero
  refine ⟨j, ?_⟩
  intro hzero
  have entry := congrFun hzero i
  rw [_root_.Matrix.mulVec_single_one] at entry
  exact hij entry

private theorem translated_rejects {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n) (j : Fin n)
    (witness : (freivaldsMatrix A * freivaldsMatrix B - freivaldsMatrix C).mulVec
      (Pi.single j 1) ≠ 0)
    (r : Fin n → ZMod 2) (accepted : (freivaldsTrial A B C r).ret = true) :
    ¬ (freivaldsTrial A B C (r + Pi.single j 1)).ret = true := by
  intro both
  have original := (freivaldsTrial_accept_discrepancy_iff A B C r).mp accepted
  have translated := (freivaldsTrial_accept_discrepancy_iff A B C _).mp both
  rw [_root_.Matrix.mulVec_add, original, zero_add] at translated
  exact witness translated

/-- **Soundness of the Freivalds trial.** Let $A$, $B$, $C$ be $n \times n$ matrices over
$\mathbb{F}_2$ with $AB \ne C$. Then twice the number of seeds $r \in \mathbb{F}_2^n$ on which the
Freivalds trial returns true is at most the number of all seeds in $\mathbb{F}_2^n$; that is, at
most half of the seeds accept.

Acceptance is the return value of the same charged run whose cost is counted. -/
theorem freivaldsTrial_acceptanceCard_bound {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (wrong : freivaldsMatrix A * freivaldsMatrix B ≠ freivaldsMatrix C) :
    2 * Fintype.card {r : Fin n → ZMod 2 // (freivaldsTrial A B C r).ret = true} ≤
      Fintype.card (Fin n → ZMod 2) := by
  classical
  obtain ⟨j, witness⟩ := discrepancy_column A B C wrong
  let p := fun r : Fin n → ZMod 2 => (freivaldsTrial A B C r).ret = true
  let shift : {r // p r} → {r // ¬ p r} := fun accepted =>
    ⟨accepted.val + Pi.single j 1,
      translated_rejects A B C j witness accepted.val accepted.property⟩
  have injective : Function.Injective shift := by
    intro first second equal
    apply Subtype.ext
    exact add_right_cancel (congrArg Subtype.val equal)
  have comparison := Fintype.card_le_of_injective shift injective
  have complement := Fintype.card_subtype_compl p
  have subset := Fintype.card_subtype_le p
  change Fintype.card {r // p r} ≤ Fintype.card {r // ¬ p r} at comparison
  change 2 * Fintype.card {r // p r} ≤ Fintype.card (Fin n → ZMod 2)
  omega

end Cslib.Algorithms.Lean.Matrix
