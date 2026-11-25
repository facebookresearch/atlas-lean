/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.StorageDeficitWalk

/-!
# Active-storage capacity certificate

## i. Overview

A reservoir with capacity `C`, required releases `R t` and
inflows `Q t` over `n` steps, starting full and spilling
surplus: `S 0 = C`, `S (t + 1) = min C (S t + Q t - R t)`.
Spill is applied at the end of the step, after the release;
a negative `S t` is a shortfall (the release could not be
met). The trajectory is capacity minus the Lindley deficit
walk `K t = requiredStorageAt R Q t` of
`PhyslibExt.EarthScience.StorageDeficitWalk`, so feasibility
(`0 ≤ S t` for `t ≤ n`) holds exactly when `C` is at least
`worstRequiredStorage R Q = max_t K_t`, the least feasible
capacity. No sign hypothesis on `Q`, `R`, or `C` is needed;
`0 ≤ C` follows from either side of the equivalence. Times
run over `0 ≤ t ≤ n`, deficits over `0 ≤ t < n`. Cyclic
steady state is not included: a certificate for one cycle
does not cover repetitions.

## ii. Key results

- `EarthScience.storage_eq_capacity_sub_requiredStorageAt`:
  `S t = C - K t` for `t ≤ n`.
- `EarthScience.storage_feasible_iff`: feasibility is
  exactly `worstRequiredStorage R Q ≤ C`.

## iii. Table of contents

- A. Transported deficit-walk results
- B. Storage trajectory and feasibility

## iv. References

- `PhyslibExt.EarthScience.StorageDeficitWalk` for the
  deficit walk, its step rule, and its worst value.
- W. Rippl, "The capacity of storage-reservoirs for
  water-supply", *Minutes of the Proceedings of the
  Institution of Civil Engineers* 71 (1883), 270-278.
-/

@[expose] public section

open List

namespace EarthScience

/-! ## A. Transported deficit-walk results -/

/-- The spill-capped storage trajectory is capacity minus the
deficit walk. -/
private theorem storage_eq_capacity_sub_requiredStorageAt_of {n : ℕ}
    (hzero : ∀ (R Q : Fin n → ℝ), requiredStorageAt R Q 0 = 0)
    (hsucc : ∀ (R Q : Fin n → ℝ) {t : ℕ} (ht : t < n),
      requiredStorageAt R Q (t + 1)
        = max 0 (requiredStorageAt R Q t
            + (R ⟨t, ht⟩ - Q ⟨t, ht⟩)))
    (R Q : Fin n → ℝ) (C : ℝ) (S : ℕ → ℝ) (h0 : S 0 = C)
    (hstep : ∀ t (ht : t < n),
      S (t + 1) = min C (S t + Q ⟨t, ht⟩ - R ⟨t, ht⟩)) :
    ∀ t ≤ n, S t = C - requiredStorageAt R Q t := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [h0, hzero R Q, sub_zero]
  | succ t ih =>
    intro ht
    have htn : t < n := Nat.lt_of_succ_le ht
    have hle : t ≤ n := Nat.le_of_succ_le ht
    rw [hstep t htn, ih hle, hsucc R Q htn]
    have hX : C - requiredStorageAt R Q t + Q ⟨t, htn⟩ - R ⟨t, htn⟩
        = C - (requiredStorageAt R Q t + (R ⟨t, htn⟩ - Q ⟨t, htn⟩)) := by ring
    rw [hX]
    have hmin := min_sub_sub_left C 0
      (requiredStorageAt R Q t + (R ⟨t, htn⟩ - Q ⟨t, htn⟩))
    rw [sub_zero] at hmin
    exact hmin

/-- Feasibility of the trajectory is exactly `C` at least the
worst required storage. -/
private theorem storage_feasible_iff_of {n : ℕ}
    (hzero : ∀ (R Q : Fin n → ℝ), requiredStorageAt R Q 0 = 0)
    (hsucc : ∀ (R Q : Fin n → ℝ) {t : ℕ} (ht : t < n),
      requiredStorageAt R Q (t + 1)
        = max 0 (requiredStorageAt R Q t
            + (R ⟨t, ht⟩ - Q ⟨t, ht⟩)))
    (hworst : ∀ (R Q : Fin n → ℝ),
      (∀ t, requiredStorageAt R Q t ≤ worstRequiredStorage R Q)
        ∧ ∃ t ≤ n, requiredStorageAt R Q t
            = worstRequiredStorage R Q)
    (R Q : Fin n → ℝ) (C : ℝ) (S : ℕ → ℝ) (h0 : S 0 = C)
    (hstep : ∀ t (ht : t < n),
      S (t + 1) = min C (S t + Q ⟨t, ht⟩ - R ⟨t, ht⟩)) :
    (∀ t ≤ n, 0 ≤ S t) ↔ worstRequiredStorage R Q ≤ C := by
  have hid :=
    storage_eq_capacity_sub_requiredStorageAt_of hzero hsucc R Q C S h0 hstep
  obtain ⟨hle, t0, ht0n, ht0eq⟩ := hworst R Q
  constructor
  · intro hfeas
    have h0le := hfeas t0 ht0n
    rw [hid t0 ht0n, ht0eq] at h0le
    linarith
  · intro hWC t ht
    rw [hid t ht]
    have hKt := hle t
    linarith

/-! ## B. Storage trajectory and feasibility -/

/-- The spill-capped storage trajectory is capacity minus
the deficit walk. -/
theorem storage_eq_capacity_sub_requiredStorageAt {n : ℕ}
    (R Q : Fin n → ℝ) (C : ℝ) (S : ℕ → ℝ) (h0 : S 0 = C)
    (hstep : ∀ t (ht : t < n),
      S (t + 1) = min C (S t + Q ⟨t, ht⟩ - R ⟨t, ht⟩)) :
    ∀ t ≤ n, S t = C - requiredStorageAt R Q t :=
  storage_eq_capacity_sub_requiredStorageAt_of
    (fun R Q => requiredStorageAt_zero R Q)
    (fun R Q _t ht => requiredStorageAt_succ R Q ht)
    R Q C S h0 hstep

/-- Feasibility of the trajectory is exactly `C` at least
the worst required storage, which is therefore the least
feasible capacity. -/
theorem storage_feasible_iff {n : ℕ}
    (R Q : Fin n → ℝ) (C : ℝ) (S : ℕ → ℝ) (h0 : S 0 = C)
    (hstep : ∀ t (ht : t < n),
      S (t + 1) = min C (S t + Q ⟨t, ht⟩ - R ⟨t, ht⟩)) :
    (∀ t ≤ n, 0 ≤ S t) ↔ worstRequiredStorage R Q ≤ C :=
  storage_feasible_iff_of
    (fun R Q => requiredStorageAt_zero R Q)
    (fun R Q _t ht => requiredStorageAt_succ R Q ht)
    (fun R Q => requiredStorageAt_le_worst_and_exists_eq R Q)
    R Q C S h0 hstep

end EarthScience
