/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Law of total expectation for a finite partition

For a finite measure `μ` and an integrable real function `f`, the integral of `f` is the sum,
over the cells of a finite measurable partition, of the cell mass times the integral of `f`
against the elementary conditional measure `μ[|B]` (`ProbabilityTheory.cond`). A cell of
measure zero contributes `0`. The fibre form indexes the cells by a measurable random variable
with finitely many values; the partition form takes pairwise disjoint measurable sets covering
the space. Both follow from Mathlib's law of total probability
`ProbabilityTheory.sum_meas_smul_cond_fiber`.

## Main results

* `MathlibExt.Probability.TotalExpectation.integral_eq_sum_measureReal_mul_integral_cond_fiber`
* `MathlibExt.Probability.TotalExpectation.integral_eq_sum_measureReal_mul_integral_cond_partition`

## References

* G. Grimmett, D. Stirzaker, *Probability and Random Processes*, 3rd ed., Oxford University
  Press (2001), Section 3.7.

Atlas roadmap target M08.T03.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.TotalExpectation

/-- **Law of total expectation**, fibre form. For a finite measure `μ`, a measurable random
variable `X` with finitely many values and an integrable real `f`,
`E[f] = ∑ₓ P(X = x) · E[f | X = x]`, where `E[f | X = x]` is the integral against the
elementary conditional measure `μ[|X ← x]` (zero when `P(X = x) = 0`). -/
theorem integral_eq_sum_measureReal_mul_integral_cond_fiber {Ω α : Type*} [MeasurableSpace Ω]
    [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → α} (hX : Measurable X) {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∑ x, μ.real (X ⁻¹' {x}) * ∫ ω, f ω ∂μ[|X ← x] := by
  have hmeas : ∀ x : α, MeasurableSet (X ⁻¹' {x}) :=
    fun x => hX (measurableSet_singleton x)
  have hcell : ∀ x : α, μ (X ⁻¹' {x}) • μ[|X ⁻¹' {x}] = μ.restrict (X ⁻¹' {x}) := by
    intro x
    ext t ht
    rw [Measure.smul_apply, Measure.restrict_apply ht, smul_eq_mul, mul_comm,
      Set.inter_comm, cond_mul_eq_inter (hmeas x) t μ]
  have hint : ∀ x ∈ Finset.univ, Integrable f (μ (X ⁻¹' {x}) • μ[|X ⁻¹' {x}]) := by
    intro x _
    rw [hcell x]
    exact hf.restrict
  have hsum : ∑ x, μ (X ⁻¹' {x}) • μ[|X ⁻¹' {x}] = μ := sum_meas_smul_cond_fiber hX μ
  conv_lhs => rw [← hsum]
  rw [integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [integral_smul_measure, smul_eq_mul]
  rfl

/-- **Law of total expectation**, partition form. If the measurable sets `B i` (finitely many)
are pairwise disjoint and cover `Ω`, then `E[f] = ∑ᵢ P(Bᵢ) · E[f | Bᵢ]`. -/
theorem integral_eq_sum_measureReal_mul_integral_cond_partition {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsFiniteMeasure μ] {B : ι → Set Ω}
    (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Function.onFun Disjoint B))
    (hcover : ⋃ i, B i = Set.univ) {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∑ i, μ.real (B i) * ∫ ω, f ω ∂μ[|B i] := by
  let : MeasurableSpace ι := ⊤
  have : DiscreteMeasurableSpace ι := ⟨fun _ => trivial⟩
  have hex : ∀ ω : Ω, ∃ i, ω ∈ B i := by
    intro ω
    have hmem : ω ∈ ⋃ i, B i := by
      rw [hcover]
      exact Set.mem_univ ω
    exact Set.mem_iUnion.mp hmem
  have huniq : ∀ (ω : Ω) {i j : ι}, ω ∈ B i → ω ∈ B j → i = j := by
    intro ω i j hi hj
    by_contra hne
    exact (Set.disjoint_left.mp (hdisj hne) hi) hj
  set X : Ω → ι := fun ω => Classical.choose (hex ω)
  have hXmem : ∀ ω, ω ∈ B (X ω) := fun ω => Classical.choose_spec (hex ω)
  have hfib : ∀ i, X ⁻¹' {i} = B i := by
    intro i
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h]
      exact hXmem ω
    · intro h
      exact huniq ω (hXmem ω) h
  have hX : Measurable X := by
    apply measurable_to_countable
    intro y
    rw [hfib]
    exact hB (X y)
  have hmain := integral_eq_sum_measureReal_mul_integral_cond_fiber (X := X) hX hf
  simpa only [hfib] using hmain

end MathlibExt.Probability.TotalExpectation
