/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.TopRow
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.JordanParity
import Mathlib.Algebra.BigOperators.Pi
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# West runs along the top row

For a closed walk without right turns, a north step arriving at the top row is followed by a west
step, and a west step on the top row is followed by another west step or by a south step. Hence
the walk leaves a top corner by a run of west steps that ends with a south step.

## Main results

* `StatMech.Onsager.SingleTopRunProof.top_arrival_west`: arriving at the top row from below,
  the walk turns west.
* `StatMech.Onsager.SingleTopRunProof.exists_west_run_end`: the west run from a top corner ends
  with a south step.
* `StatMech.Onsager.SingleTopRunProof.singleTopRun_of_runCoversTop`: a run covering the top row
  gives `StatMech.Onsager.TopRow.SingleTopRun`.
-/

@[expose] public section

namespace StatMech.Onsager.SingleTopRunProof
open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity
open Fin.NatCast
variable {n : ℕ} [NeZero n]

/-- In a closed walk without right turns, a north step arriving at a highest vertex is followed by a
  west step. -/
theorem top_arrival_west (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    {M v : Fin n} (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
    (hv : (pos d v).2 = (pos d M).2) (harr : d (v - 1) = 1) :
    d v = 2 := by
  have hne1 : d v ≠ 1 := StatMech.Onsager.TopRow.top_out_ne_N d hclosed hmax hv
  have hrf := hreflexfree (v - 1)
  rw [sub_add_cancel, harr] at hrf
  rcases hrf with h | h
  · rw [sub_eq_zero] at h; exact absurd h hne1
  · rw [sub_eq_iff_eq_add] at h; rw [h]; decide

/-- A west step on the top row is followed by a west or a south step, and stays on the top row. -/
theorem top_west_next (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    {M v : Fin n} (_hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
    (hv : (pos d v).2 = (pos d M).2) (hw : d v = 2) :
    (pos d (v + 1)).2 = (pos d M).2 ∧ (d (v + 1) = 2 ∨ d (v + 1) = 3) := by
  have hhoriz : isHorizEdge (d v) := Or.inr hw
  have hyconst : (pos d (v + 1)).2 = (pos d v).2 := horiz_y_const d hclosed v hhoriz
  refine ⟨by rw [hyconst, hv], ?_⟩
  have hrf := hreflexfree v
  rw [hw] at hrf
  rcases hrf with h | h
  · left; rw [sub_eq_zero] at h; exact h
  · right; rw [sub_eq_iff_eq_add] at h; rw [h]; decide

/-- A closed walk does not consist of west steps only. -/
theorem exists_step_ne_west (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (M : Fin n) :
    ∃ i : ℕ, d (M + (Nat.cast i : Fin n)) ≠ 2 := by
  by_contra hcon
  push Not at hcon
  have hkey : ∀ k : Fin n, d k = 2 := by
    intro k
    have h1 : ((k - M).val : Fin n) = k - M := Fin.cast_val_eq_self _
    have h2 : M + ((k - M).val : Fin n) = k := by rw [h1]; abel
    have h3 := hcon ((k - M).val)
    rwa [h2] at h3
  have hfstsum : (∑ i : Fin n, stepOf (d i)).1 = 0 := by rw [hclosed, Prod.fst_zero]
  have hfstsum2 : (∑ i : Fin n, stepOf (d i)).1 = ∑ i : Fin n, (stepOf (d i)).1 :=
    Prod.fst_sum
  have hval : (∑ i : Fin n, (stepOf (d i)).1) = -(n : ℤ) := by
    have hcong : (∑ i : Fin n, (stepOf (d i)).1) = ∑ _i : Fin n, (-1 : ℤ) :=
      Finset.sum_congr rfl (fun k _ => by rw [hkey k]; rfl)
    rw [hcong, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg,
      mul_one]
  rw [hfstsum2, hval] at hfstsum
  have hn : (n : ℤ) = 0 := by linarith
  exact (NeZero.ne n) (by exact_mod_cast hn)

/-- From a highest vertex where the walk turns west, it makes `J ≥ 1` west steps and then a south
  step. -/
theorem exists_west_run_end (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (M : Fin n) (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2) (hout : d M = 2) :
    ∃ J : ℕ, 1 ≤ J ∧ (∀ i : ℕ, i < J → d (M + (Nat.cast i : Fin n)) = 2) ∧
      d (M + (Nat.cast J : Fin n)) = 3 := by
  classical
  have hex : ∃ i : ℕ, d (M + (Nat.cast i : Fin n)) ≠ 2 := exists_step_ne_west d hclosed M
  obtain ⟨J, hJpos, hJmin, hJspec⟩ :
      ∃ J : ℕ, 1 ≤ J ∧ (∀ i : ℕ, i < J → d (M + (Nat.cast i : Fin n)) = 2) ∧
        d (M + (Nat.cast J : Fin n)) ≠ 2 := by
    refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · exfalso; have := Nat.find_spec hex; rw [h0] at this
        apply this; simpa using hout
      · exact hpos
    · intro i hi
      by_contra hne
      exact Nat.not_lt.2 (Nat.find_min' hex hne) hi
  refine ⟨J, hJpos, hJmin, ?_⟩
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, J = K + 1 := ⟨J - 1, by omega⟩
  have hcastsucc : (Nat.cast (K + 1) : Fin n) = (Nat.cast K : Fin n) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have hidx : M + (Nat.cast (K + 1) : Fin n) = (M + (Nat.cast K : Fin n)) + 1 := by
    rw [hcastsucc, add_assoc]
  have hrunpos : pos d (M + (Nat.cast K : Fin n)) = ((pos d M).1 - (K : ℤ), (pos d M).2) :=
    StatMech.Onsager.TopRow.forward_west_run d hclosed M K
      (fun i hi => hJmin i (by omega))
  have hKtop : (pos d (M + (Nat.cast K : Fin n))).2 = (pos d M).2 := by rw [hrunpos]
  have hKwest : d (M + (Nat.cast K : Fin n)) = 2 := hJmin K (by omega)
  have hnext := top_west_next d hclosed hreflexfree hmax hKtop hKwest
  have hcases := hnext.2
  rw [← hidx] at hcases
  rcases hcases with h | h
  · exact absurd h hJspec
  · exact h

/-- A west run from `M` whose vertices cover the top row is a single top run. -/
theorem singleTopRun_of_runCoversTop (d : Fin n → Fin 4) (M : Fin n) (J : ℕ)
    (hrun : ∀ i : ℕ, i < J → d (M + (Nat.cast i : Fin n)) = 2)
    (hcover : ∀ v : Fin n, (pos d v).2 = (pos d M).2 →
      ∃ i : ℕ, i ≤ J ∧ (pos d v).1 = (pos d M).1 - (i : ℤ)) :
    StatMech.Onsager.TopRow.SingleTopRun d M := by
  intro v hv
  obtain ⟨i, hiJ, hxi⟩ := hcover v hv
  exact ⟨i, fun i' hi' => hrun i' (lt_of_lt_of_le hi' hiJ), hxi⟩

end StatMech.Onsager.SingleTopRunProof
