/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Privacy.AboveThreshold

/-!
# Tests for AboveThreshold and sparse vector

Literal transcripts distinguish reusing a threshold from redrawing it at every query and
from retaining it across successes. The probability test distinguishes independent query
draws from reusing the first query noise on the second round.
-/

namespace CSLibExtTest.Privacy.AboveThresholdTests

open CSLibExt.Privacy.AboveThreshold MeasureTheory

private def tape (threshold query : ℕ → ℤ) : ℕ ⊕ ℕ → ℤ := Sum.elim threshold query

private def stream (scores : List ℤ) (h : List Bool) : Option (ℤ → ℤ) :=
  scores[h.length]?.map fun s x ↦ s + x

-- With threshold 5 both 2 and 3 miss; redrawing at query 1 would use 0 and hit early.
-- Equality at 5 ends the phase without releasing a bit for the trailing 100.
example : transcript (stream [2, 3, 4, 100]) 0 0
    (tape (fun i ↦ if i = 0 then 5 else 0) (fun i ↦ if i = 2 then 1 else 0)) 1 4 =
      [false, false, true] := by decide

-- A phase-1 threshold of 10 rejects the second query. Keeping the phase-0 threshold of 1
-- would instead stop at that query. The second equality hit exhausts the cutoff.
example : transcript (stream [1, 2, 10, 100]) 0 0
    (tape (fun i ↦ if i = 0 then 1 else 10) (fun _ ↦ 0)) 2 4 = [true, false, true] := by decide

private def analyst : List Bool → Option (ℤ → ℤ)
  | [] => some id
  | [true] => some (fun _ ↦ -1)
  | [false] => some (fun _ ↦ 1)
  | _ => none

-- Same analyst, draws and public threshold; different databases select different second queries.
example : transcript analyst 0 0 (fun _ ↦ 0) 2 5 = [true, false] := by decide
example : transcript analyst (-1) 0 (fun _ ↦ 0) 2 5 = [false, true] := by decide

example : transcript (stream [-1, -2]) 0 0 (fun _ ↦ 0) 1 7 = [false, false] := by decide
example : transcript (stream []) 0 0 (fun _ ↦ 0) 3 8 = [] := by decide
example : transcript analyst 0 0 (fun _ ↦ 0) 1 0 = [] := by decide
example : transcript analyst 0 0 (fun _ ↦ 0) 0 10 = [] := by decide
example (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    laplaceSparse (fun _ ↦ some id) 0 ε hε 0 n 3 = PMF.pure [] := rfl

-- At sensitivity one, ε = 4 and two phases give per-phase budget 2: threshold scale 1
-- but query scale 2, in the continuous real law (not an integer-noise approximation).
private noncomputable def calibrated : ℕ ⊕ ℕ → Measure ℝ :=
  Sum.elim (fun _ ↦ ProbabilityTheory.laplaceMeasure 0 1) (fun _ ↦ ProbabilityTheory.laplaceMeasure 0 2)

private instance (i : ℕ ⊕ ℕ) : IsProbabilityMeasure (calibrated i) := by
  cases i <;> apply ProbabilityTheory.isProbabilityMeasure_laplaceMeasure <;> norm_num

example {D : Type*} (next : List Bool → Option (D → ℝ)) (T : ℝ) (n : ℕ) (x : D) :
    laplaceSparse next T 4 (by norm_num) 2 n x = transcriptPMF calibrated next T 2 n x := by
  norm_num [laplaceSparse, calibrated, Cslib.Crypto.Privacy.laplaceMechanism]

private def askZero (_ : List Bool) : Option (Unit → ℝ) := some (fun _ ↦ 0)

-- No tape that reuses a single query draw can report a miss followed by a hit for identical
-- queries against the same threshold. This is independent of the common marginal law.
example (w : ℕ ⊕ ℕ → ℝ) (shared : w (.inr 1) = w (.inr 0)) :
    transcript askZero () 0 w 1 2 ≠ [false, true] := by
  by_cases hit : w (.inl 0) ≤ w (.inr 0) <;>
    simp [transcript, responses, answer, askZero, shared, hit]

-- In contrast, if threshold 0 and each of the query-noise values -1 and 1 have positive
-- probability on the indicated rounds, independent sampling gives this transcript positive mass.
example (μ : ℕ ⊕ ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (ht : 0 < μ (.inl 0) {0}) (ha : 0 < μ (.inr 0) {-1}) (hb : 0 < μ (.inr 1) {1}) :
    0 < transcriptPMF μ askZero 0 1 2 () [false, true] := by
  classical
  let I : Finset (ℕ ⊕ ℕ) := {.inl 0, .inr 0, .inr 1}
  let v : ℕ ⊕ ℕ → ℝ := Sum.elim (fun _ ↦ 0) (fun i ↦ if i = 0 then -1 else 1)
  let C := Set.pi (I : Set (ℕ ⊕ ℕ)) (fun i ↦ ({v i} : Set ℝ))
  have hc : 0 < Measure.infinitePi μ C := by
    rw [show C = _ from rfl, Measure.infinitePi_pi μ (fun _ _ ↦ measurableSet_singleton _)]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ht.ne'
    · exact ha.ne'
    · exact hb.ne'
  rw [transcriptPMF_apply]
  apply hc.trans_le (measure_mono ?_)
  intro w hw
  have t : w (.inl 0) = 0 := hw _ (by simp [I])
  have a : w (.inr 0) = -1 := hw _ (by simp [I])
  have b : w (.inr 1) = 1 := hw _ (by simp [I])
  change transcript askZero () 0 w 1 2 = _
  norm_num [transcript, responses, answer, askZero, t, a, b]

end CSLibExtTest.Privacy.AboveThresholdTests
