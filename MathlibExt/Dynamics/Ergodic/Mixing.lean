/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Strong mixing

A probability-preserving map `T` is *(strongly) mixing* when every event `B`, pulled back by
`T^[n]`, becomes asymptotically independent of every event `A`:
`μ (A ∩ T^[n] ⁻¹' B) → μ A * μ B`. Mixing sits between ergodicity and the Kolmogorov and
Bernoulli properties in the hierarchy of statistical properties of a dynamical system.

## Main results

* `IsMixing`: the definition (O. Sarig, *Lecture Notes on Ergodic Theory*, Definition 1.5).
* `IsMixing.ergodic`: mixing implies ergodicity (Sarig, Proposition 1.2).
* `IsMixing.iterate`: every positive power of a mixing map is mixing, so mixing maps are
  totally ergodic (`IsMixing.ergodic_iterate`).

## References

* O. Sarig, *Lecture Notes on Ergodic Theory* (2023 version),
  https://www.weizmann.ac.il/math/sarigo/sites/math.sarigo/files/uploads/ergodicnotes.pdf
* I. P. Cornfeld, S. V. Fomin and Ya. G. Sinai, *Ergodic Theory*, Springer (1982).
-/

@[expose] public section

namespace MathlibExt.Dynamics.Ergodic.Mixing

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {T : α → α} {μ : Measure α}

/-- **Strong mixing.** A measure-preserving map `T` of `(α, μ)` is *mixing* (strongly mixing) if
for all measurable sets `A` and `B`, `μ (A ∩ T⁻ⁿ B) → μ A · μ B` as `n → ∞`: the event
`T⁻ⁿ B` is asymptotically independent of `A`. This is O. Sarig, *Lecture Notes on Ergodic
Theory*, Definition 1.5, stated there for probability-preserving transformations. -/
structure IsMixing (T : α → α) (μ : Measure α) : Prop where
  /-- A mixing map preserves the measure. -/
  measurePreserving : MeasurePreserving T μ μ
  /-- Asymptotic independence of `A` and `T⁻ⁿ B`. -/
  tendsto_measure_inter_preimage :
    ∀ ⦃A B : Set α⦄, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n : ℕ => μ (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (μ A * μ B))

/-- In a finite measure space, a set whose measure equals its own square has measure `0` or `1`. -/
private theorem eq_zero_or_one_of_eq_mul_self {a : ℝ≥0∞} (ha : a ≠ ∞) (h : a = a * a) :
    a = 0 ∨ a = 1 := by
  by_cases h0 : a = 0
  · exact Or.inl h0
  · right
    have : a * 1 = a * a := by rw [mul_one]; exact h
    exact ((ENNReal.mul_right_inj h0 ha).1 this).symm

/-- **Mixing implies ergodicity.** A mixing transformation of a probability space is ergodic:
an invariant set `E` satisfies `μ E = μ (E ∩ T⁻ⁿ E) → (μ E)²`, so `μ E ∈ {0, 1}`
(O. Sarig, *Lecture Notes on Ergodic Theory*, Proposition 1.2). -/
theorem IsMixing.ergodic [IsProbabilityMeasure μ] (h : IsMixing T μ) : Ergodic T μ := by
  refine Ergodic.of_preimage_eq h.measurePreserving fun s hs hTs => ?_
  have hiter : ∀ n : ℕ, T^[n] ⁻¹' s = s := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ, Set.preimage_comp, ih, hTs]
  have hconst : (fun n : ℕ => μ (s ∩ T^[n] ⁻¹' s)) = fun _ => μ s := by
    funext n; rw [hiter n, Set.inter_self]
  have hlim := h.tendsto_measure_inter_preimage hs hs
  rw [hconst] at hlim
  have hsq : μ s = μ s * μ s := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [Filter.eventuallyEmptyOrUniv_iff]
  rcases eq_zero_or_one_of_eq_mul_self (measure_ne_top μ s) hsq with h0 | h1
  · exact Or.inr (measure_eq_zero_iff_ae_notMem.1 h0)
  · refine Or.inl ?_
    have hc : μ sᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hs]; exact h1
    exact (measure_eq_zero_iff_ae_notMem.1 hc).mono fun x hx => by simpa using hx

/-- **Powers of a mixing map are mixing.** If `T` is mixing then so is `T^[k]` for every `k ≥ 1`:
the sequence `μ (A ∩ T^{-kn} B)` is a subsequence of `μ (A ∩ T^{-n} B)`. -/
theorem IsMixing.iterate (h : IsMixing T μ) {k : ℕ} (hk : 0 < k) : IsMixing T^[k] μ where
  measurePreserving := h.measurePreserving.iterate k
  tendsto_measure_inter_preimage A B hA hB := by
    have hsub : Tendsto (fun n : ℕ => k * n) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk) tendsto_id
    have := (h.tendsto_measure_inter_preimage hA hB).comp hsub
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, Function.iterate_mul]

/-- **Mixing maps are totally ergodic.** Every positive power `T^[k]` of a mixing transformation
of a probability space is ergodic. -/
theorem IsMixing.ergodic_iterate [IsProbabilityMeasure μ] (h : IsMixing T μ) {k : ℕ}
    (hk : 0 < k) : Ergodic T^[k] μ :=
  (h.iterate hk).ergodic

end MathlibExt.Dynamics.Ergodic.Mixing
