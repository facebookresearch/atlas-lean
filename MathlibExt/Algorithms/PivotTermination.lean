/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Pivot termination from a potential

If every non-fixed step strictly increases a bounded
natural-valued potential, iteration reaches a fixed point.
The lexicographic potential for Bland's rule is not
included here.
-/

@[expose] public section

/-- Termination of pivot iteration from a bounded,
strictly increasing potential (ALG-30b anti-cycling
core). If every non-fixed step strictly increases a
natural-valued potential bounded by `B`, the iterates of
`step` from any start reach a fixed point within `B + 1`
steps. Bland's rule supplies such a potential through
its lexicographic objective; that construction is
downstream. -/
theorem iterate_fixed_of_potential {S : Type*} (step : S → S)
    (Φ : S → ℕ) (B : ℕ)
    (hbound : ∀ s, Φ s ≤ B)
    (hincrease : ∀ s, step s ≠ s → Φ s < Φ (step s))
    (s : S) :
    ∃ k ≤ B + 1, step^[k + 1] s = step^[k] s := by
  by_contra h
  have hne : ∀ k, k ≤ B + 1 → step^[k + 1] s ≠ step^[k] s := by
    intro k hk heq
    exact h ⟨k, hk, heq⟩
  have hgrow : ∀ k, k ≤ B + 1 → Φ s + k ≤ Φ (step^[k] s) := by
    intro k
    induction k with
    | zero =>
      intro _
      show Φ s + 0 ≤ Φ s
      omega
    | succ n ih =>
      intro hle
      have hle' : n ≤ B + 1 := by omega
      have ihn := ih hle'
      have hstep : step^[n.succ] s = step (step^[n] s) :=
        Function.iterate_succ_apply' step n s
      have h1 : step (step^[n] s) ≠ step^[n] s := by
        have h2 : step^[n.succ] s ≠ step^[n] s := hne n hle'
        rw [hstep] at h2
        exact h2
      have hlt := hincrease _ h1
      have hgoal : Φ s + n.succ ≤ Φ (step^[n.succ] s) := by
        rw [hstep]
        omega
      exact hgoal
  have hbig := hgrow (B + 1) le_rfl
  have hle := hbound (step^[B + 1] s)
  omega

end
