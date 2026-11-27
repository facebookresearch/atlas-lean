/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Privacy.Exponential
public import CSLibExt.Crypto.Privacy.Laplace

/-!
# Tests for differential privacy

* A counting query on `n` rows has sensitivity `1` for `hammingAdj`, so the Laplace mechanism with
  scale `1 / ε` is `ε`-differentially private; post-processing it by squaring keeps the guarantee.
* The Laplace law, and every output of the Laplace mechanism, is a probability measure.
* The exponential mechanism with the score "is this my value" on `Fin 3` is `ε`-differentially
  private for any pair of databases; composing it with the Laplace count adds the epsilons.
* Basic composition of three Laplace counts, the vector Laplace mechanism, approximate
  composition and approximate group privacy.
* Group privacy and the histogram relation on small examples.
-/

@[expose] public section

namespace Cslib.Crypto.PrivacyTests

open MeasureTheory ProbabilityTheory Cslib.Crypto.Privacy
open scoped ENNReal

/-- Equal databases are neighbours, even with no rows. -/
example (S : Fin 0 → Bool) : hammingAdj S S := Or.inl rfl

/-- The number of `true` rows of a database of `n` booleans. -/
noncomputable def countTrue {n : ℕ} (S : Fin n → Bool) : ℝ :=
  ∑ i, if S i then 1 else 0

theorem countTrue_sensitivity {n : ℕ} {S S' : Fin n → Bool} (h : hammingAdj S S') :
    |countTrue S - countTrue S'| ≤ 1 := by
  obtain rfl | ⟨i, hi⟩ := h
  · simp
  have : countTrue S - countTrue S' =
      (if S i then (1 : ℝ) else 0) - (if S' i then 1 else 0) := by
    rw [countTrue, countTrue, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single i (fun j _ hj ↦ by simp [hi j hj]) (by simp)]
  rw [this]
  cases S i <;> cases S' i <;> norm_num

/-- The Laplace count is `ε`-differentially private. -/
example {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    DifferentiallyPrivate hammingAdj
      (laplaceMechanism (countTrue (n := n)) (1 / ε) (by positivity)) ε 0 :=
  laplaceMechanism_differentiallyPrivate one_pos hε fun _ _ h ↦ countTrue_sensitivity h

/-- Non-vacuity: the Laplace mechanism releases a sample, since each output law has total mass
one; a mechanism whose outputs were zero measures would satisfy every privacy bound. -/
example {n : ℕ} {ε : ℝ} (hε : 0 < ε) (S : Fin n → Bool) :
    laplaceMechanism (countTrue (n := n)) (1 / ε) (by positivity) S Set.univ = 1 :=
  measure_univ

/-- Post-processing the Laplace count by squaring keeps `ε`-differential privacy. -/
example {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    DifferentiallyPrivate hammingAdj
      (fun S ↦ (laplaceMechanism (countTrue (n := n)) (1 / ε) (by positivity) S).map
        fun z ↦ z ^ 2) ε 0 :=
  (laplaceMechanism_differentiallyPrivate one_pos hε fun _ _ h ↦ countTrue_sensitivity h).map
    (by fun_prop)

/-- The standard Laplace law has total mass one. -/
example : laplaceMeasure 0 1 Set.univ = 1 :=
  (isProbabilityMeasure_laplaceMeasure one_pos 0).measure_univ

/-- The score "is the output equal to the database" has sensitivity `1`. -/
noncomputable def matchScore (x r : Fin 3) : ℝ := if r = x then 1 else 0

theorem matchScore_sensitivity (x y r : Fin 3) : |matchScore x r - matchScore y r| ≤ 1 := by
  unfold matchScore
  split_ifs <;> norm_num

/-- The exponential mechanism with the match score is `ε`-differentially private for any two
databases. -/
example {ε : ℝ} (hε : 0 ≤ ε) :
    DifferentiallyPrivate (fun _ _ : Fin 3 ↦ True) (expMechanism ε 1 matchScore) ε 0 :=
  expMechanism_differentiallyPrivate hε one_pos fun x y _ r ↦ matchScore_sensitivity x y r

/-- The exponential mechanism outputs a law of total mass one. -/
example (ε : ℝ) (x : Fin 3) : expMechanism ε 1 matchScore x Set.univ = 1 :=
  (isProbabilityMeasure_expMechanism ε 1 matchScore x).measure_univ

/-- Utility: with `ε = 2`, the output scores `≤ 1 - (ln 3 + t)` with probability at most
`e^{-t}`. -/
example (x : Fin 3) (t : ℝ) :
    expMechanism 2 1 matchScore x
        {r | matchScore x r ≤ optUtility matchScore x - 2 * 1 / 2 * (Real.log 3 + t)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  simpa using expMechanism_utility_card (ε := 2) (Δ := 1) two_pos one_pos matchScore x t

/-- Releasing the Laplace count and an independent exponential-mechanism output is
`(ε₁ + ε₂)`-differentially private. -/
example {ε₁ ε₂ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 ≤ ε₂) :
    DifferentiallyPrivate (fun _ _ : Fin 3 ↦ True)
      (fun x ↦ (laplaceMechanism (fun x : Fin 3 ↦ (x : ℝ)) (2 / ε₁) (by positivity) x).prod
        (expMechanism ε₂ 1 matchScore x)) (ε₁ + ε₂) 0 := by
  refine DifferentiallyPrivate.prod
    (laplaceMechanism_differentiallyPrivate two_pos h₁ fun x y _ ↦ ?_)
    (expMechanism_differentiallyPrivate h₂ one_pos fun x y _ r ↦ matchScore_sensitivity x y r)
  fin_cases x <;> fin_cases y <;> norm_num

/-- Three independent releases of the Laplace count compose to `3ε` (basic composition). -/
example {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    DifferentiallyPrivate hammingAdj
      (fun S ↦ Measure.pi fun _ : Fin 3 ↦
        laplaceMechanism (countTrue (n := n)) (1 / ε) (by positivity) S)
      (3 * ε) 0 := by
  have h := differentiallyPrivate_pi (Ω := fun _ : Fin 3 ↦ ℝ)
    (M := fun _ ↦ laplaceMechanism (countTrue (n := n)) (1 / ε) (by positivity))
    (ε := fun _ ↦ ε)
    (δ := fun _ ↦ 0) fun _ ↦
      laplaceMechanism_differentiallyPrivate one_pos hε fun _ _ h ↦ countTrue_sensitivity h
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h

/-- Releasing the count on two coordinates with noise of scale `2 / ε` each is `ε`-private
(vector Laplace mechanism, `ℓ₁`-sensitivity `2`). -/
example {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    DifferentiallyPrivate hammingAdj
      (fun S ↦ Measure.pi fun _ : Fin 2 ↦ laplaceMeasure (countTrue (n := n) S) (2 / ε)) ε 0 := by
  refine laplaceMechanism_pi_differentiallyPrivate (f := fun S _ ↦ countTrue S) two_pos hε
    fun S S' h ↦ ?_
  simp only [Fin.sum_univ_two]
  linarith [countTrue_sensitivity h]

/-- Approximate composition: two `(ε, δ)`-private mechanisms with values in probability measures
compose to `(2ε, 2δ)`. -/
example {X Ω : Type*} [MeasurableSpace Ω] {Adj : X → X → Prop} {M : X → Measure Ω}
    [∀ x, IsProbabilityMeasure (M x)] {ε : ℝ} {δ : ℝ≥0∞} (h : DifferentiallyPrivate Adj M ε δ) :
    DifferentiallyPrivate Adj (fun x ↦ (M x).prod (M x)) (ε + ε) (δ + δ) :=
  h.prod_approx h

/-- Approximate group privacy for a group of size `2`: `(2ε, 2 e^ε δ)`. -/
example {X Ω : Type*} [MeasurableSpace Ω] {Adj : X → X → Prop} {M : X → Measure Ω} {ε : ℝ}
    {δ : ℝ≥0∞} (h : DifferentiallyPrivate Adj M ε δ) (hε : 0 ≤ ε) {z : ℕ → X}
    (hz : ∀ i < 2, Adj (z i) (z (i + 1))) {S : Set Ω} (hS : MeasurableSet S) :
    M (z 0) S ≤ ENNReal.ofReal (Real.exp (2 * ε)) * M (z 2) S +
      2 * ENNReal.ofReal (Real.exp ε) * δ := by
  have := h.group_approx hε hz hS
  norm_num at this
  exact this

/-- Histograms differing by one record in one bin are neighbours. -/
example : histogramAdj (fun i : Fin 2 ↦ if i = 0 then 3 else 1)
    (fun i : Fin 2 ↦ if i = 0 then 2 else 1) := by
  simp [histogramAdj, Fin.sum_univ_two]

/-- Group privacy: an `ε`-private mechanism on histograms satisfies the `2ε` bound for histograms
at `ℓ₁` distance `2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {M : (Fin 2 → ℕ) → Measure Ω} {ε : ℝ}
    (h : DifferentiallyPrivate histogramAdj M ε 0) {S : Set Ω} (hS : MeasurableSet S) :
    M (fun i ↦ if i = 0 then 3 else 1) S ≤
      ENNReal.ofReal (Real.exp (2 * ε)) * M (fun i ↦ if i = 0 then 2 else 0) S := by
  have := h.group_histogram (k := 2) (x := fun i ↦ if i = 0 then 3 else 1)
    (y := fun i ↦ if i = 0 then 2 else 0) (by simp [Fin.sum_univ_two]) hS
  simpa using this

/-! The exponential mechanism needs a nonempty range: on `Empty` it would be the zero measure,
which satisfies every privacy bound, so it does not elaborate. -/

/--
error: failed to synthesize instance of type class
  Nonempty Empty

Hint: Adding the command `deriving instance Nonempty for Empty` may allow Lean to derive the missing instance.
-/
#guard_msgs in
noncomputable example : MeasureTheory.Measure Empty :=
  expMechanism (X := Unit) 1 1 (fun _ r ↦ r.elim) ()

end Cslib.Crypto.PrivacyTests
