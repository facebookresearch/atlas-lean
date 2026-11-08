/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT
public import Init.Data.Vector.Lemmas
public import Mathlib.Algebra.Group.Monoid
import Init.Data.List.TakeDrop

/-! # Values written by the actual running-twiddle butterfly loop -/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

variable {R : Type u} [CommRing R]

/-- The actual butterfly writes the sum into its lower output position. -/
theorem fftButterfly_ret_low {m : Nat} (omega : R) (q r : Vector R m)
    (state : R × Vector R (m * 2)) (k : Fin m) :
    (fftButterfly omega q r state k).ret.2[k.val]'(by have h := k.isLt; omega) =
      q[k.val] + state.1 * r[k.val] := by
  rcases state with ⟨w, out⟩
  have hm : m ≠ 0 := by have h := k.isLt; omega
  simp [fftButterfly, hm]

/-- The actual butterfly writes the difference into its upper output position. -/
theorem fftButterfly_ret_high {m : Nat} (omega : R) (q r : Vector R m)
    (state : R × Vector R (m * 2)) (k : Fin m) :
    (fftButterfly omega q r state k).ret.2[k.val + m]'(by have h := k.isLt; omega) =
      q[k.val] - state.1 * r[k.val] := by
  rcases state with ⟨w, out⟩
  simp [fftButterfly]

/-- Each actual butterfly preserves all positions outside its two writes. -/
theorem fftButterfly_ret_other {m : Nat} (omega : R) (q r : Vector R m)
    (state : R × Vector R (m * 2)) (k : Fin m) (i : Fin (m * 2))
    (hlo : i.val ≠ k.val) (hhi : i.val ≠ k.val + m) :
    (fftButterfly omega q r state k).ret.2[i.val] = state.2[i.val] := by
  rcases state with ⟨w, out⟩
  simp [fftButterfly, Ne.symm hlo, Ne.symm hhi]

private theorem fftButterflies_prefix_step {m : Nat} (omega : R) (q r : Vector R m)
    (out : Vector R (m * 2)) (j : Nat) (hj : j < m) :
    (((List.finRange m).take (j + 1)).foldlM (fftButterfly omega q r) (1, out)).ret =
      (fftButterfly omega q r
        (((List.finRange m).take j).foldlM (fftButterfly omega q r) (1, out)).ret
        ⟨j, hj⟩).ret := by
  rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldlM_append]
  simp [List.getElem_finRange, List.foldlM_cons]

private theorem fftButterflies_prefix_ret {m : Nat} (omega : R) (q r : Vector R m)
    (out : Vector R (m * 2)) (j : Nat) (hj : j ≤ m) :
    let actual := (((List.finRange m).take j).foldlM (fftButterfly omega q r) (1, out)).ret
    actual.1 = omega ^ j ∧ ∀ k : Fin m,
      actual.2[k.val]'(by have h := k.isLt; omega) =
        (if k.val < j then q[k.val] + omega ^ k.val * r[k.val]
          else out[k.val]'(by have h := k.isLt; omega)) ∧
      actual.2[k.val + m]'(by have h := k.isLt; omega) =
        (if k.val < j then q[k.val] - omega ^ k.val * r[k.val]
          else out[k.val + m]'(by have h := k.isLt; omega)) := by
  dsimp only
  induction j with
  | zero => simp
  | succ j ih =>
      have hjlt : j < m := by omega
      obtain ⟨hw, hc⟩ := ih (by omega)
      rw [fftButterflies_prefix_step omega q r out j hjlt]
      constructor
      · change
          (((List.finRange m).take j).foldlM (fftButterfly omega q r) (1, out)).ret.1 *
            omega = omega ^ (j + 1)
        rw [hw, pow_succ]
      · intro k
        obtain ⟨hlo, hhi⟩ := hc k
        by_cases hkj : k.val = j
        · have hk : k = ⟨j, hjlt⟩ := Fin.ext hkj
          subst k
          constructor
          · rw [fftButterfly_ret_low, hw]
            simp
          · rw [fftButterfly_ret_high, hw]
            simp
        · have hLow := fftButterfly_ret_other omega q r
            (((List.finRange m).take j).foldlM (fftButterfly omega q r) (1, out)).ret
            ⟨j, hjlt⟩ ⟨k.val, by have h := k.isLt; omega⟩ hkj
            (by change k.val ≠ j + m; have h := k.isLt; omega)
          have hHigh := fftButterfly_ret_other omega q r
            (((List.finRange m).take j).foldlM (fftButterfly omega q r) (1, out)).ret
            ⟨j, hjlt⟩ ⟨k.val + m, by have h := k.isLt; omega⟩
            (by change k.val + m ≠ j; have h := k.isLt; omega)
            (by change k.val + m ≠ j + m; omega)
          have hlt : (k.val < j + 1) ↔ k.val < j := by omega
          constructor
          · rw [hLow, hlo]
            simp only [hlt]
          · rw [hHigh, hhi]
            simp only [hlt]

/-- The actual loop writes every butterfly pair with its iteratively advanced twiddle. -/
theorem fftButterflies_ret {m : Nat} (omega : R) (q r : Vector R m)
    (out : Vector R (m * 2)) :
    (fftButterflies omega q r out).ret.1 = omega ^ m ∧ ∀ k : Fin m,
      (fftButterflies omega q r out).ret.2[k.val]'(by have h := k.isLt; omega) =
        q[k.val] + omega ^ k.val * r[k.val] ∧
      (fftButterflies omega q r out).ret.2[k.val + m]'(by have h := k.isLt; omega) =
        q[k.val] - omega ^ k.val * r[k.val] := by
  have h := fftButterflies_prefix_ret omega q r out m (Nat.le_refl m)
  have htake : (List.finRange m).take m = List.finRange m := by
    simpa only [List.length_finRange] using (List.take_length (l := List.finRange m))
  dsimp only at h
  rw [htake] at h
  constructor
  · simpa only [fftButterflies] using h.1
  · intro k
    simpa [fftButterflies, k.isLt] using h.2 k

end Cslib.Algorithms.Lean.TimeM
