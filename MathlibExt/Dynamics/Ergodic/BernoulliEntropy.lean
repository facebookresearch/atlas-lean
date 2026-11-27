/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.BernoulliShift
public import MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy
import Mathlib.Algebra.BigOperators.Fin

/-!
# Entropy of the time-zero partition of a Bernoulli shift

For the Bernoulli shift on a finite alphabet `S` with distribution `p`, the time-zero partition
`ξ = {[s] : s ∈ S}`, `[s] = {x | x 0 = s}`, refines under the shift into the partition into
cylinders of length `n`, whose atoms have measure `p(w₀) ⋯ p(w_{n-1})`. Its entropy is therefore
`n · H(p)`, so `h(σ, ξ) = H(p) = -∑ p(s) log p(s)`, and the Kolmogorov–Sinai entropy of the
Bernoulli shift is at least `H(p)`. This is the computation in the proof of O. Sarig, *Lecture
Notes on Ergodic Theory*, Proposition 4.6; the matching upper bound needs Sinai's generator
theorem (`MathlibExt.Dynamics.KolmogorovSinaiWanted.ksEntropy_bernoulliShift`).

## Main results

* `partitionEntropy_iterateJoin_timeZero`: `H(ξ ∨ σ⁻¹ξ ∨ ⋯ ∨ σ^{-(n-1)}ξ) = n · H(p)`.
* `entropyRel_timeZero`: `h(σ, ξ) = H(p)`.
* `ofReal_le_ksEntropy_shift`: `H(p) ≤ h(σ)`; in particular Bernoulli shifts with a
  non-degenerate distribution have positive entropy.
-/

@[expose] public section

namespace MathlibExt.Dynamics.Ergodic.BernoulliEntropy

open MeasureTheory Filter Topology
open MathlibExt.Dynamics.Ergodic.BernoulliShift MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy
open scoped ENNReal

variable {S : Type*}

/-- **Entropy of a product distribution on words.** If `a : S → ℝ` is a probability vector, then
`∑_{w ∈ Sⁿ} negMulLog (a(w₀) ⋯ a(w_{n-1})) = n · ∑_s negMulLog (a s)`: the entropy of `n`
independent letters is `n` times the entropy of one. -/
theorem sum_negMulLog_prod [Fintype S] {a : S → ℝ} (ha : ∑ s, a s = 1) (n : ℕ) :
    ∑ w : Fin n → S, Real.negMulLog (∏ k, a (w k)) = n * ∑ s, Real.negMulLog (a s) := by
  have hone : ∀ m : ℕ, ∑ w : Fin m → S, ∏ k, a (w k) = 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        ← Finset.mul_sum, ih, mul_one, ha]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hone, ih,
      ha]
    push_cast
    ring

variable [MeasurableSpace S]

/-- **Time-zero partition of the shift space.** The partition of `ℕ → S` into the cylinders
`[s] = {x | x 0 = s}`, `s ∈ S`, according to the symbol at time `0`. -/
def timeZeroPartition (s : S) : Set (ℕ → S) := {x | x 0 = s}

omit [MeasurableSpace S] in
/-- **Refinements of the time-zero partition are cylinders.** The atom of the word
`w : Fin n → S` in `ξ ∨ σ⁻¹ξ ∨ ⋯ ∨ σ^{-(n-1)}ξ` is the cylinder `{x | x k = w k for k < n}`. -/
theorem iterateJoin_timeZero (n : ℕ) (w : Fin n → S) :
    iterateJoin shift timeZeroPartition n w = {x | ∀ k : Fin n, x k = w k} := by
  ext x
  simp [iterateJoin, timeZeroPartition, shift_iterate_apply]

/-- **The time-zero partition is a measurable partition** of the shift space, for any measure. -/
theorem isMeasurablePartition_timeZero [MeasurableSingletonClass S]
    (μ : Measure (ℕ → S)) : IsMeasurablePartition μ (timeZeroPartition (S := S)) where
  measurableSet s := by
    change MeasurableSet ((fun x : ℕ → S => x 0) ⁻¹' {s})
    exact (measurable_pi_apply 0) (measurableSet_singleton s)
  aedisjoint s t hst := by
    have : timeZeroPartition s ∩ timeZeroPartition t = ∅ := by
      ext x
      simp only [timeZeroPartition, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hs ht
      exact hst ((show x 0 = s from hs).symm.trans ht)
    change μ (timeZeroPartition s ∩ timeZeroPartition t) = 0
    rw [this, measure_empty]
  measure_compl_iUnion := by
    have : (⋃ s, timeZeroPartition (S := S) s) = Set.univ :=
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x 0, rfl⟩
    rw [this, Set.compl_univ, measure_empty]

/-- **Measure of a cylinder under a product measure.** Under `p^ℕ`, the cylinder of the word
`w : Fin n → S` has measure `p {w 0} ⋯ p {w (n-1)}`. -/
theorem infinitePi_cylinder_word [MeasurableSingletonClass S] (p : Measure S)
    [IsProbabilityMeasure p] (n : ℕ) (w : Fin n → S) :
    (Measure.infinitePi fun _ : ℕ => p) {x | ∀ k : Fin n, x k = w k} = ∏ k, p {w k} := by
  classical
  set t : ℕ → Set S := fun i => if h : i < n then {w ⟨i, h⟩} else Set.univ
  have hset : {x : ℕ → S | ∀ k : Fin n, x k = w k} = Set.pi (Finset.range n : Set ℕ) t := by
    ext x
    constructor
    · intro hx i hi
      have hi' : i < n := by simpa using hi
      simp only [t, hi', dite_true]
      exact hx ⟨i, hi'⟩
    · intro hx k
      have := hx k (by simp)
      simpa [t, k.2] using this
  have ht : ∀ i ∈ Finset.range n, MeasurableSet (t i) := fun i _ => by
    simp only [t]; split_ifs
    · exact measurableSet_singleton _
    · exact MeasurableSet.univ
  rw [hset]
  refine (Measure.infinitePi_pi (μ := fun _ : ℕ => p) ht).trans ?_
  rw [← Fin.prod_univ_eq_prod_range (fun i => p (t i)) n]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [t, k.2]

variable [Fintype S] [MeasurableSingletonClass S]

/-- **Entropy of the refined time-zero partition.** For the Bernoulli shift with distribution
`p` on a finite alphabet, `H(ξ ∨ σ⁻¹ξ ∨ ⋯ ∨ σ^{-(n-1)}ξ) = n · H(p)` where
`H(p) = -∑ p(s) log p(s)` (the computation in the proof of O. Sarig, *Lecture Notes on Ergodic
Theory*, Proposition 4.6). -/
theorem partitionEntropy_iterateJoin_timeZero (p : Measure S) [IsProbabilityMeasure p]
    (n : ℕ) :
    partitionEntropy (Measure.infinitePi fun _ : ℕ => p)
        (iterateJoin shift timeZeroPartition n) =
      n * ∑ s, Real.negMulLog (p {s}).toReal := by
  have ha : ∑ s, (p {s}).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun s _ => measure_ne_top p _), sum_measure_singleton]
    simp
  rw [← sum_negMulLog_prod ha n]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [iterateJoin_timeZero, infinitePi_cylinder_word, ENNReal.toReal_prod]

/-- **Entropy of the Bernoulli shift relative to the time-zero partition.** For the Bernoulli
shift with distribution `p` on a finite alphabet and the time-zero partition `ξ`,
`h(σ, ξ) = H(p) = -∑ p(s) log p(s)`: the sequence `(1/n) H(ξ ∨ ⋯ ∨ σ^{-(n-1)}ξ)` is constant,
equal to `H(p)`, for `n ≥ 1`. -/
theorem entropyRel_timeZero (p : Measure S) [IsProbabilityMeasure p] :
    entropyRel (Measure.infinitePi fun _ : ℕ => p) shift timeZeroPartition =
      ENNReal.ofReal (∑ s, Real.negMulLog (p {s}).toReal) := by
  unfold entropyRel
  refine (tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn => ?_).limsup_eq
  rw [partitionEntropy_iterateJoin_timeZero, mul_div_cancel_left₀]
  exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)

/-- **Lower bound for the entropy of a Bernoulli shift.** The Kolmogorov–Sinai entropy of the
Bernoulli shift with distribution `p` on a finite alphabet is at least
`H(p) = -∑ p(s) log p(s)`. Equality holds by Sinai's generator theorem (O. Sarig, *Lecture
Notes on Ergodic Theory*, Proposition 4.6). -/
theorem ofReal_le_ksEntropy_shift (p : Measure S) [IsProbabilityMeasure p] :
    ENNReal.ofReal (∑ s, Real.negMulLog (p {s}).toReal) ≤
      ksEntropy (Measure.infinitePi fun _ : ℕ => p) shift := by
  classical
  set e := Fintype.equivFin S
  set ξ : Fin (Fintype.card S) → Set (ℕ → S) := fun i => timeZeroPartition (e.symm i)
  have hξ : IsMeasurablePartition (Measure.infinitePi fun _ : ℕ => p) ξ := by
    have h0 := isMeasurablePartition_timeZero (S := S) (Measure.infinitePi fun _ : ℕ => p)
    refine ⟨fun i => h0.measurableSet _, fun i j hij => h0.aedisjoint (e.symm.injective.ne hij), ?_⟩
    have : (⋃ i, ξ i) = ⋃ s, timeZeroPartition s :=
      e.symm.surjective.iUnion_comp (fun s => timeZeroPartition (S := S) s)
    rw [this]
    exact h0.measure_compl_iUnion
  have hrel : entropyRel (Measure.infinitePi fun _ : ℕ => p) shift ξ =
      entropyRel (Measure.infinitePi fun _ : ℕ => p) shift timeZeroPartition := by
    unfold entropyRel partitionEntropy
    congr 1
    funext n
    congr 2
    refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) e.symm) _ _ fun w => ?_
    simp only [iterateJoin, ξ, Equiv.arrowCongr_apply, Function.comp_apply, Function.comp_def]
    rfl
  rw [← entropyRel_timeZero, ← hrel]
  exact entropyRel_le_ksEntropy shift hξ

end MathlibExt.Dynamics.Ergodic.BernoulliEntropy
