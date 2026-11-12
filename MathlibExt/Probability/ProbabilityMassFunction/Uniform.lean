/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying
-/
module

/- BACKPORT: Finite-set sampling adapted from Mathlib.Probability.Distributions.Uniform
at d13f23b723b8a846827a245b89c10fc7d3f11612.
See [BACKPORTS.md](../../../BACKPORTS.md). -/

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform probability mass functions

The finite-type construction uses the public `PMF.ofFintype` constructor.

These are `PMF`-valued samplers. Pinned Mathlib (v4.35) has no `PMF`-valued finite
uniform sampler: in `Mathlib.Probability.Distributions.Uniform`, the former `PMF` API was
retired in favour of the measure-valued
`MeasureTheory.Measure.uniformOfFinset : Finset α → Measure α`, and
`PMF.uniformOfFintype` survives only as a deprecated alias (since `2026-10-04`) for that
`Measure` construction — `#check @PMF.uniformOfFintype` gives
`{α : Type*} → [MeasurableSpace α] → Finset α → Measure α`, not a `PMF`. Consumers here
(e.g. `PMF.uniformFintype` in the dyadic Haar measure) need actual `PMF` values, hence
this backport; see [BACKPORTS.md](../../../BACKPORTS.md) for the removal condition.
-/

@[expose] public section

namespace PMF

open scoped ENNReal

variable {α : Type*}

/-- **Uniform distribution on a finite set.** For a nonempty finite subset $s$ of a type $\alpha$,
the uniform distribution on $s$ is the probability mass function on $\alpha$ that gives mass
$1/|s|$ to each element of $s$ and mass $0$ to every other element of $\alpha$. -/
noncomputable def uniformFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a => if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have h : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel h (ENNReal.natCast_ne_top s.card)
  · exact fun a ha => by simp only [ha, ite_false]

open scoped Classical in
@[simp] theorem uniformFinset_apply (s : Finset α) (hs : s.Nonempty) (a : α) :
    uniformFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := rfl

@[simp] theorem uniformFinset_apply_of_mem {s : Finset α} (hs : s.Nonempty)
    {a : α} (ha : a ∈ s) : uniformFinset s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  classical
  rw [uniformFinset_apply, if_pos ha]

/-- **Uniform distribution on a finite type.** For a nonempty finite type $\alpha$, the uniform
distribution on $\alpha$ is the probability mass function on $\alpha$ that gives mass $1/|\alpha|$
to every element of $\alpha$. -/
noncomputable def uniformFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  ofFintype (fun _ => (Fintype.card α : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero] using (Fintype.card_ne_zero (α := α))
    exact ENNReal.mul_inv_cancel h (ENNReal.natCast_ne_top (Fintype.card α)))

variable [Fintype α] [Nonempty α]

@[simp] theorem uniformFintype_apply (a : α) :
    uniformFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := rfl

/-- **Uniform distribution on the whole finite type.** For a nonempty finite type $\alpha$, the
uniform distribution on the finite set of all elements of $\alpha$ equals the uniform
distribution on $\alpha$. -/
@[simp] theorem uniformFinset_univ :
    uniformFinset (Finset.univ : Finset α) Finset.univ_nonempty = uniformFintype α := by
  ext a
  simp

/-- **Outer measure of an event under the uniform distribution.** Let $\alpha$ be a nonempty finite
type. For every subset $s \subseteq \alpha$, the outer measure associated to the uniform
distribution on $\alpha$ assigns to $s$ the value $|s| / |\alpha|$, computed in the extended
nonnegative reals. -/
theorem toOuterMeasure_uniformFintype_apply (s : Set α) [Fintype s] :
    (uniformFintype α).toOuterMeasure s =
      (Fintype.card s : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) := by
  classical
  rw [toOuterMeasure_apply_fintype]
  simp only [Set.indicator, uniformFintype_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    ← Fintype.card_subtype (fun a => a ∈ s), div_eq_mul_inv]

/-- **Probability of an event under the uniform distribution.** Let $\alpha$ be a nonempty finite
type carrying a σ-algebra. For every measurable set $s \subseteq \alpha$, the probability measure
associated to the uniform distribution on $\alpha$ gives $s$ the measure $|s| / |\alpha|$, computed
in the extended nonnegative reals. -/
theorem toMeasure_uniformFintype_apply (s : Set α) [MeasurableSpace α]
    (hs : MeasurableSet s) [Fintype s] :
    (uniformFintype α).toMeasure s =
      (Fintype.card s : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ hs).trans (toOuterMeasure_uniformFintype_apply s)

end PMF
