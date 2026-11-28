/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Privacy.Laplace
public import CSLibExt.Privacy.DifferentialPrivacy
public import Mathlib.Probability.ProductMeasure

/-!
# AboveThreshold and sparse vector transcripts

Dwork and Roth, *The Algorithmic Foundations of Differential Privacy* (2014), §3.6,
Algorithm 1 (p. 57) and Algorithm 2 (pp. 60–61). A policy sees only the chronological
list of answers. The mechanism sees a fixed database and two disjoint families of noise
coordinates: one indexed by **phase**, the other by **query**. A negative answer advances
only the query index; a positive advances both. AboveThreshold is the one-positive case.

`transcript` reads a supplied tape; advancing an index does not make arbitrary tape values
independent. Observations agree under truncation, even on a stream with no crossing.
`transcriptPMF` gives their law under independent real noises. For strictly positive `ε`,
`laplaceSparse` uses the book's sensitivity-one, pure-budget scales. These finite observations
do not assert a differential privacy bound or eventual stopping on an unbounded stream.
-/

@[expose] public section

namespace CSLibExt.Privacy.AboveThreshold

variable {D R : Type*}

section Path

variable [Add R] [LinearOrder R] (next : List Bool → Option (D → R)) (x : D) (T : R)
  (w : ℕ ⊕ ℕ → R)

/-- The next public answer after history `h`, or `none` when the analyst has no further query.
For a query `q`, compare `q x` plus query noise number `h.length` against `T` plus threshold
noise number `h.count true`. Equality is positive. The analyst receives neither noise. -/
def answer (h : List Bool) : Option Bool :=
  (next h).map fun q ↦ decide (T + w (.inl (h.count true)) ≤ q x + w (.inr h.length))

/-- Starting after the public history `h` with room for `c` more positives, emit at most `n`
further answers, in order, from the supplied tape `w`. Exhausting either bound or the analyst's
queries ends the computation. A positive advances the phase index; a negative keeps it fixed. -/
def responses : (n c : ℕ) → (h : List Bool) → List Bool
  | 0, _, _ | _ + 1, 0, _ => []
  | n + 1, c + 1, h =>
    match answer next x T w h with
    | none => []
    | some false => false :: responses n (c + 1) (h ++ [false])
    | some true => true :: responses n c (h ++ [true])

/-- The public sparse vector transcript on `x` up to horizon `n` and cutoff `c`, starting with
empty history. At `c = 1` this is AboveThreshold. At `c = 0` it asks no query. For any `c`,
the list may end before `n` if the analyst is exhausted or the last allowed hit occurs. -/
def transcript (c n : ℕ) : List Bool := responses next x T w n c []

/-- No answers are emitted once the positive budget has been used up, even on an infinite stream. -/
@[simp] theorem responses_zero_cutoff (n : ℕ) (h : List Bool) :
    responses next x T w n 0 h = [] := by cases n <;> rfl

/-- The number of positives in the newly emitted suffix is at most the remaining cutoff. -/
theorem count_true_responses_le (n c : ℕ) (h : List Bool) :
    (responses next x T w n c h).count true ≤ c := by
  induction n generalizing c h with
  | zero => simp [responses]
  | succ n ih =>
    cases c with
    | zero => simp
    | succ c =>
      simp only [responses]
      split
      · simp
      · simpa using ih (c + 1) (h ++ [false])
      · simpa using Nat.succ_le_succ (ih c (h ++ [true]))

/-- Taking the first `n` items of a longer observation gives exactly the observation at `n`,
including when the analyst has already stopped. No almost-sure stopping assumption is needed. -/
theorem take_responses (n k c : ℕ) (h : List Bool) :
    (responses next x T w (n + k) c h).take n = responses next x T w n c h := by
  induction n generalizing c h with
  | zero => simp [responses]
  | succ n ih =>
    cases c with
    | zero => simp
    | succ c =>
      simp only [Nat.succ_add, responses]
      split <;> simp [ih]

/-- Suppose the remaining positive budget is nonzero (`c + 1`) and the next `k` queries along
the all-negative continuation of `h` miss. The `k + n`-round run emits these `k` negatives,
then runs for up to `n` more rounds on the tail with the same budget and threshold coordinate. -/
theorem responses_after_misses (k n c : ℕ) (h : List Bool)
    (miss : ∀ j < k, answer next x T w (h ++ List.replicate j false) = some false) :
    responses next x T w (k + n) (c + 1) h = List.replicate k false ++
      responses next x T w n (c + 1) (h ++ List.replicate k false) := by
  induction k generalizing h with
  | zero => simp
  | succ k ih =>
    have first : answer next x T w h = some false := by simpa using miss 0 (by omega)
    have later (j : ℕ) (hj : j < k) :
        answer next x T w ((h ++ [false]) ++ List.replicate j false) = some false := by
      simpa [List.replicate_succ, List.append_assoc] using miss (j + 1) (by omega)
    simp only [Nat.succ_add, responses, first]
    rw [ih (h ++ [false]) later]
    simp [List.replicate_succ, List.append_assoc]

/-- If the first `k` answers are negative and the next noisy value reaches the noisy threshold,
AboveThreshold emits precisely `k` negatives and one positive, regardless of the unused horizon. -/
theorem transcript_first_hit (k extra : ℕ)
    (miss : ∀ j < k, answer next x T w (List.replicate j false) = some false)
    (hit : answer next x T w (List.replicate k false) = some true) :
    transcript next x T w 1 (k + (extra + 1)) = List.replicate k false ++ [true] := by
  unfold transcript
  rw [responses_after_misses next x T w k (extra + 1) 0 [] (by simpa using miss)]
  simp [responses, hit]

end Path

open MeasureTheory

/-- For a fixed database, public history and bounds, the newly emitted answers are a measurable
function of the real noise tape, with discrete finite transcripts. No regularity of the policy
as a function of databases is needed. -/
theorem measurable_responses (next : List Bool → Option (D → ℝ)) (x : D) (T : ℝ)
    (n c : ℕ) (h : List Bool) :
    @Measurable _ (List Bool) _ ⊤ (fun w ↦ responses next x T w n c h) := by
  let : MeasurableSpace (List Bool) := ⊤
  induction n generalizing c h with
  | zero => exact measurable_const
  | succ n ih =>
    cases c with
    | zero => exact measurable_const
    | succ c =>
      cases hq : next h with
      | none => simp [responses, answer, hq]
      | some q =>
        have hit := (measurable_of_countable (List.cons true)).comp (ih c (h ++ [true]))
        have miss := (measurable_of_countable (List.cons false)).comp (ih (c + 1) (h ++ [false]))
        have hs : MeasurableSet {w : ℕ ⊕ ℕ → ℝ |
          T + w (.inl (h.count true)) ≤ q x + w (.inr h.length)} :=
          measurableSet_le (measurable_const.add (measurable_pi_apply _))
            (measurable_const.add (measurable_pi_apply _))
        convert Measurable.ite hs hit miss using 1
        · funext w
          by_cases hw : T + w (.inl (h.count true)) ≤ q x + w (.inr h.length) <;>
            simp [responses, answer, hq, hw]
        · exact fun _ ↦ inferInstance

variable (μ : ℕ ⊕ ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
  (next : List Bool → Option (D → ℝ)) (T : ℝ) (c n : ℕ)

/-- The law of the sparse vector transcript on a fixed database `x`, up to `n` queries and `c`
positives. A policy seeing only past answers chooses `q`. Compare `q x` plus fresh query noise
with `T` plus the current phase noise. Emit `false` and reuse the threshold on a miss; emit
`true` on reaching or exceeding it, then restart on the remaining stream if budget remains.
At `c = 1` this stops at the first crossing; `c = 0` or an exhausted policy gives no further
answers. The noise coordinates are independent with marginals `μ` (`inl` for phases, `inr` for
queries). Neither database nor query space needs to be finite or carry a sigma-algebra. -/
noncomputable def transcriptPMF (x : D) : PMF (List Bool) :=
  letI : MeasurableSpace (List Bool) := ⊤
  let f := fun w ↦ transcript next x T w c n
  have hf : Measurable f := measurable_responses next x T n c []
  haveI := (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2
    (inferInstance : IsProbabilityMeasure (Measure.infinitePi μ))
  ((Measure.infinitePi μ).map f).toPMF

/-- The probability of any particular transcript is the product measure of the noise tapes
on which the stopped algorithm emits exactly that transcript. -/
theorem transcriptPMF_apply (x : D) (s : List Bool) :
    transcriptPMF μ next T c n x s =
      Measure.infinitePi μ {w | transcript next x T w c n = s} := by
  let : MeasurableSpace (List Bool) := ⊤
  have hf : Measurable (fun w ↦ transcript next x T w c n) := measurable_responses next x T n c []
  unfold transcriptPMF
  rw [Measure.toPMF_apply, Measure.map_apply hf (measurableSet_singleton s)]
  rfl

/-- The finite observation laws of sparse vector are consistent: deterministic post-processing
of an `(n + k)`-round transcript by taking at most `n` answers has exactly the `n`-round law,
as mechanisms on arbitrary databases. This also covers streams on which there is no last answer. -/
theorem postProcess_take_transcriptPMF (k : ℕ) :
    DifferentialPrivacy.postProcess (List.take n) (transcriptPMF μ next T c (n + k)) =
      transcriptPMF μ next T c n := by
  let : MeasurableSpace (List Bool) := ⊤
  funext x
  have ht := measurable_of_countable (List.take n (α := Bool))
  have hf : Measurable (fun w ↦ transcript next x T w c (n + k)) :=
    measurable_responses next x T (n + k) c []
  apply PMF.toMeasure_injective
  unfold DifferentialPrivacy.postProcess
  rw [← PMF.toMeasure_map _ _ ht]
  simp only [transcriptPMF, Measure.toPMF_toMeasure, Measure.map_map ht hf]
  congr 1
  funext w
  exact take_responses next x T w n k c []

/-- Dwork–Roth's pure-budget Sparse law for sensitivity-one queries requires `ε > 0` for every
cutoff `c`. At `c = 0` it returns the empty transcript. At `c > 0` the per-phase budget is `ε/c`:
the centered real Laplace scales are `2/(ε/c)` for the threshold and `4/(ε/c)` for each query.
The horizon `n` bounds the observation even if the analyst never stops and fewer than `c` hits
occur. The observation can end earlier at query exhaustion or the `c`-th hit. This is not an
integer noise law or a claim of privacy, accuracy or almost-sure termination. -/
noncomputable def laplaceSparse (next : List Bool → Option (D → ℝ)) (T ε : ℝ) (hε : 0 < ε)
    (c n : ℕ) (x : D) : PMF (List Bool) :=
  match c with
  | 0 => PMF.pure []
  | k + 1 =>
    let e := ε / (k + 1 : ℕ)
    have he : 0 < e := div_pos hε (by positivity)
    let noise (b : ℝ) (hb : 0 < b) :=
      Cslib.Crypto.Privacy.laplaceMechanism (fun _ : Unit ↦ 0) b hb ()
    let μ := Sum.elim (fun _ : ℕ ↦ noise (2 / e) (div_pos (by norm_num) he))
      (fun _ : ℕ ↦ noise (4 / e) (div_pos (by norm_num) he))
    haveI (i : ℕ ⊕ ℕ) : IsProbabilityMeasure (μ i) := by cases i <;> dsimp [μ, noise] <;>
      apply ProbabilityTheory.isProbabilityMeasure_laplaceMeasure <;> positivity
    transcriptPMF μ next T (k + 1) n x

end CSLibExt.Privacy.AboveThreshold
