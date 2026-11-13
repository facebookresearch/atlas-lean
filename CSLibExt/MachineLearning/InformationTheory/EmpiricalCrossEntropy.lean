/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.FiniteEntropy

/-!
# Empirical cross-entropy of a fixed model on a finite sample

On a nonempty finite sample `S : Fin N → α`, the average surprisal of a fixed
model `q : PMF α` equals the cross-entropy of the empirical law `p̂` of the sample.
Hence it equals entropy plus divergence by the existing population identity
`InformationTheory.crossEntropy_eq_shannonEntropy_add_klDiv`; this file does not
reprove that decomposition, it only identifies its left-hand side on samples.

* `empiricalPMF`: the empirical law `p̂` (outcome frequencies `count / N`).
* `empiricalCrossEntropy_eq_avg_surprisal`: `H(p̂, q)` is the average surprisal
  `(∑ n, surprisal (q (S n))) / N`.
* `empiricalCrossEntropy_eq_top_iff`: the cross-entropy is infinite exactly when
  some sampled token has model probability `0` (both sides are `∞` in that case,
  per `InformationTheory.crossEntropy_eq_top_iff`).
* `empiricalCrossEntropy_eq_shannonEntropy_add_klDiv`: hence `H(p̂, q)` equals
  `H(p̂) + KL(p̂ ‖ q) / log 2`.

The Atlas `crossEntropy` uses logarithms base two, so values are in bits and
perplexity is `2 ^ H`. Perplexity comparisons require the same tokenization and
the same log base on both sides.

## References

* K. P. Murphy, *Probabilistic Machine Learning: An Introduction*, MIT Press,
  2022, §5.1.6.1, eqs. (5.37)-(5.41).
-/

@[expose] public section

namespace Cslib.MachineLearning.InformationTheory

open Real _root_.InformationTheory
open scoped ENNReal

/-- The **empirical law** `p̂` of a nonempty finite sample: outcome frequencies. -/
noncomputable def empiricalPMF {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ}
    (S : Fin N → α) (hN : N ≠ 0) : PMF α :=
  PMF.ofFintype (fun a => ((Finset.univ.filter (fun n => S n = a)).card : ℝ≥0∞)
    / (N : ℝ≥0∞)) (by
    have hmaps : Set.MapsTo S (↑(Finset.univ : Finset (Fin N)))
        (↑(Finset.univ : Finset α)) :=
      fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
    have hcard : ∑ a, (Finset.univ.filter (fun n => S n = a)).card = N := by
      have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
        (t := Finset.univ) (f := S) hmaps
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact h.symm
    have hsum : (∑ a, (((Finset.univ.filter (fun n => S n = a)).card : ℝ≥0∞)))
        = (N : ℝ≥0∞) := by
      rw [← Nat.cast_sum, hcard]
    have hNe : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN
    have hTop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hsum]
    exact ENNReal.mul_inv_cancel hNe hTop)

/-- Applying the empirical law counts occurrences. -/
@[simp] theorem empiricalPMF_apply {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ}
    (S : Fin N → α) (hN : N ≠ 0) (a : α) : (empiricalPMF S hN) a =
      ((Finset.univ.filter (fun n => S n = a)).card : ℝ≥0∞) / (N : ℝ≥0∞) := rfl

/-- On a nonempty sample, cross-entropy against the empirical law is the average
surprisal of the sample under the model. -/
theorem empiricalCrossEntropy_eq_avg_surprisal {α : Type*} [Fintype α]
    [DecidableEq α] {N : ℕ} (S : Fin N → α) (hN : N ≠ 0) (q : PMF α) :
    crossEntropy (empiricalPMF S hN) q =
      (∑ n, surprisal (q (S n))) / (N : ℝ≥0∞) := by
  have hbase : ∑ n : Fin N, surprisal (q (S n)) = ∑ a,
      (((Finset.univ.filter (fun n => S n = a)).card : ℝ≥0∞) * surprisal (q a)) := by
    have hinner : ∀ a, (∑ n ∈ Finset.univ.filter (fun n => S n = a),
        surprisal (q (S n)))
        = (((Finset.univ.filter (fun n => S n = a)).card : ℝ≥0∞)
          * surprisal (q a)) := by
      intro a
      have heq : ∀ n ∈ Finset.univ.filter (fun n => S n = a),
          surprisal (q (S n)) = surprisal (q a) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [hn.2]
      rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.univ (α := Fin N))
      (t := Finset.univ (α := α)) (fun n _ => Finset.mem_univ (S n))
      (fun n => surprisal (q (S n)))
    have hrewrite : (∑ a ∈ Finset.univ, ∑ n ∈ Finset.univ.filter
        (fun n => S n = a), surprisal (q (S n)))
        = ∑ a, (((Finset.univ.filter (fun n => S n = a)).card : ℝ≥0∞)
          * surprisal (q a)) :=
      Finset.sum_congr rfl (fun a _ => hinner a)
    rw [hrewrite] at hfib
    simpa using hfib.symm
  rw [crossEntropy]
  simp only [empiricalPMF_apply]
  have hterm : ∀ a : α, (((Finset.univ.filter (fun n => S n = a)).card : ℝ≥0∞)
      / (N : ℝ≥0∞) * surprisal (q a))
      = ((((Finset.univ.filter (fun n => S n = a)).card : ℝ≥0∞)
        * surprisal (q a)) * ((N : ℝ≥0∞)⁻¹)) := by
    intro a
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.sum_mul, ← hbase,
    div_eq_mul_inv]

/-- The empirical cross-entropy is infinite exactly when the model rules out a
sampled token; both sides are `∞` in that case. -/
theorem empiricalCrossEntropy_eq_top_iff {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (S : Fin N → α) (hN : N ≠ 0) (q : PMF α) :
    crossEntropy (empiricalPMF S hN) q = ∞ ↔ ∃ n, q (S n) = 0 := by
  have hNe : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN
  have hTop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hzero : ∀ a : α, (empiricalPMF S hN) a = 0 →
      (Finset.univ.filter (fun n => S n = a)).card = 0 := by
    intro a ha
    simp only [empiricalPMF_apply] at ha
    rw [ENNReal.div_eq_zero_iff] at ha
    rcases ha with ha | ha
    · exact Nat.cast_eq_zero.mp ha
    · exact absurd ha hTop
  have hne : ∀ a : α, (empiricalPMF S hN) a ≠ 0 →
      ∃ n, S n = a := by
    intro a ha
    by_contra hnone
    push Not at hnone
    have hcard : (Finset.univ.filter (fun n => S n = a)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro n _
      exact hnone n
    exact ha (by simp [empiricalPMF_apply, hcard])
  rw [crossEntropy_eq_top_iff]
  constructor
  · rintro ⟨a, hq, hp⟩
    obtain ⟨n, hn⟩ := hne a hp
    exact ⟨n, by rw [hn, hq]⟩
  · rintro ⟨n, hn⟩
    refine ⟨S n, hn, ?_⟩
    intro h0
    have hcard := hzero (S n) h0
    have hmem : n ∈ Finset.univ.filter (fun m => S m = S n) := by
      simp [Finset.mem_filter]
    have hneCard : (Finset.univ.filter (fun m => S m = S n)).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨n, hmem⟩
    exact hneCard hcard

/-- Hence the empirical cross-entropy equals entropy plus divergence: with no
support hypothesis, both sides are `∞` when `p̂` charges an outcome `q` rules out. -/
theorem empiricalCrossEntropy_eq_shannonEntropy_add_klDiv {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {N : ℕ} (S : Fin N → α) (hN : N ≠ 0) (q : PMF α) :
    crossEntropy (empiricalPMF S hN) q =
      ENNReal.ofReal (shannonEntropy (empiricalPMF S hN)) +
        klDiv (empiricalPMF S hN).toMeasure q.toMeasure /
          ENNReal.ofReal (Real.log 2) :=
  crossEntropy_eq_shannonEntropy_add_klDiv _ _

end Cslib.MachineLearning.InformationTheory
