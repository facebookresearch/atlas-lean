/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesProductIntegral
public import MathlibExt.Analysis.StieltjesRSIntegral
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# The left-endpoint Riemann–Stieltjes integral

For an integrand `f` and an integrator `h` on `[a, b]`, the **left-endpoint Riemann–Stieltjes sum**
over a partition `a = x₀ < x₁ < ⋯ < xₙ = b` is `∑ₖ f(xₖ) (h(xₖ₊₁) - h(xₖ))`: every cell is tagged
at its left endpoint. The **left-endpoint integral** `∫ₐᵇ f dh` is the limit of these sums along
refinement of partitions. This is the integral the Duhamel operator of the product integral needs:
in `Ψ A B h t = ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t]` (Gill–Johansen 1990) the integrand
`s ↦ P(A)(0, s)` is a product over the open interval `(0, s)`, the left limit of the càdlàg
function `s ↦ P(A)(0, s]`. Evaluating that càdlàg function at left endpoints produces exactly
this left limit, while a càdlàg integrand and a càdlàg integrator with a common jump are
discontinuous from the same side.

With freely chosen tags the refinement integral (Apostol, Definition 7.1) does not exist when `f`
and `h` are discontinuous from the same side at the same point: for `f = h = 1_{[c, ∞)}` a tag
in the cell `[xₖ, xₖ₊₁] ∋ c` can sit on either side of `c`, so the sums oscillate between `0`
and `1`. Tagging at the left endpoint removes this freedom. For left-continuous `f` the
left-endpoint integral weights every jump of `h` at `c` by `f c`; for general `f` the jumps of
`h` from the left are weighted by the left limit `f(c-)` and those from the right by `f c`
(`hasLeftRSIntegral_ite_le`, `hasLeftRSIntegral_ite_lt`).

## Main definitions

* `leftSum f h P`: the left-endpoint sum `∑_{x ∈ P} f (prev P x) * (h x - h (prev P x))` over the
  cells of a finite set `P`; `rightSum h f P` is the right-endpoint sum of `h` against `f`.
* `leftPartitionSum f h a b s = leftSum f h (partitionPts a b s)`: the net of left-endpoint sums,
  indexed by finite sets `s : Finset ℝ` ordered by inclusion (refinement).
* `HasLeftRSIntegral f h a b I`, `LeftRSIntegrable f h a b`, `leftRSIntegral f h a b`: the
  integral as a limit along refinement (`leftRSIntegral` is `0` when the limit does not exist).

## Main results

* `HasLeftRSIntegral.unique`, `HasLeftRSIntegral.leftRSIntegral_eq`: uniqueness.
* `HasLeftRSIntegral.add_left`, `sub_left`, `smul_left`, `add_right`, `sub_right`, `smul_right`:
  bilinearity; `hasLeftRSIntegral_const`: `∫ₐᵇ k dh = k (h b - h a)`.
* `monotone_leftPartitionSum`, `hasLeftRSIntegral_of_monotoneOn`: for `f` and `h` monotone on
  `[a, b]` the sums increase under refinement, so the integral exists.
* `leftRSIntegrable_of_boundedVariationOn`: **existence** for `f` and `h` of bounded variation on
  `[a, b]`, with no continuity assumption on either.
* `leftRSIntegrable_of_uniform_approx`: **existence** for `f` of bounded variation and any `h`
  that is a uniform limit on `[a, b]` of functions of bounded variation (for instance step
  functions, so every regulated `h`); `leftRSIntegrable_of_continuousOn`: existence for
  continuous `h`.
* `HasLeftRSIntegral.tendsto_rightSum`: **integration by parts**: the right-endpoint sums of `h`
  against `f` converge to `f b h b - f a h a - ∫ₐᵇ f dh`.
* Bounds: `HasLeftRSIntegral.abs_le_of_isControl` / `abs_le_mul_variation` (`|∫ f dh| ≤ M V(h)`),
  `abs_le_of_monotoneOn` (`|∫ f dh| ≤ M (h b - h a)`), `abs_le_of_abs_le`
  (`|∫ f dh| ≤ B (2M + V(f))` for `|h| ≤ B`, no regularity of `h`), and
  `abs_sub_le_of_abs_sub_le`: Lipschitz dependence on the integrator in the uniform norm. All
  hold already for the sums (`abs_leftPartitionSum_le_of_isControl`, …).
* `hasLeftRSIntegral_ite_le`: against the step `1_{[c, ∞)}` the integral is the left limit
  `f(c-)`, hence `f c` for `f` left-continuous at `c`
  (`hasLeftRSIntegral_ite_le_of_continuousWithinAt`); `hasLeftRSIntegral_ite_lt`: against
  `1_{(c, ∞)}` it is `f c` for every `f`.
* `hasLeftRSIntegral_of_hasRSIntegral`: **agreement**: if the free-tag refinement integral
  `MathlibExt.Analysis.Integration.HasRSIntegral f h a b I` exists, the left-endpoint integral
  exists and equals `I`. `leftSum_image_points_eq_rsSum_leftTag` identifies the left-endpoint sum
  over the points of a partition with `rsSum` of its left tagging.
* `twoTagSum F G h P`: sums `∑ F(u) Δh G(x)` with `F` tagged at the left and `G` at the right
  endpoint of each cell, the shape of `duhamelSum` (`duhamelSum_eq_twoTagSum`;
  `twoTagSum_image_points` reads the tags off `Partition.leftTag` and `Partition.rightTag`).
  `twoTagSum_eq_leftSum_add` / `twoTagSum_eq_rightSum_sub` split it into the left- or
  right-endpoint sum of `F G` and a second-order term; `abs_twoTagSum_le_of_abs_le` bounds it by
  `‖h‖_∞ (2‖F‖‖G‖ + ‖G‖ V(F) + 3‖F‖ V(G))` uniformly in the partition, and
  `abs_twoTagSum_sub_le` gives Lipschitz dependence on `h`.

## Implementation notes

Partitions are the finite sets `partitionPts a b s` of the merged
`MathlibExt.Analysis.StieltjesProductIntegral`, whose `prev P x` is the
left endpoint of the cell ending at `x`; the net is indexed by `Finset ℝ` with `atTop`, so
"limit along refinement" is literal. This matches the indexing of that file's Duhamel sums
`duhamelSum`, whose first factor is evaluated at the left endpoint of each cell.

Existence for bounded variation needs no regularity: inserting a point `p` into the cell `(u, v]`
changes the sum by `(f p - f u) (h v - h p)` (`leftSum_insert_sub`), which is `≥ 0` when `f` and
`h` are monotone, so the sums form a monotone bounded net; the general case follows by Jordan
decomposition and bilinearity. Existence for uniform limits uses the sum-level bound
`|S(f, h) - S(f, g)| ≤ ‖h - g‖_∞ (2‖f‖_∞ + V(f))`, uniform in the partition, which transfers the
Cauchy property from `g` to `h`.

## Source receipt (reuse search, 2026-11-13)

Mathlib v4.35.0 has no one-dimensional Riemann–Stieltjes integral (its Stieltjes integrals are
Lebesgue integrals against `StieltjesFunction.measure`, which need a right-continuous monotone
integrator) and no notion of regulated function. Reused from the merged
`MathlibExt.Analysis.StieltjesProductIntegral`: `prev`, `partitionPts`, `exists_next`,
`partitionPts_induction`, `sum_cells_insert`, `sum_cells_eq_erase`, `sum_cells_partitionPts`
(telescoping), `IsControl` and `exists_control_of_boundedVariationOn`. Reused from Mathlib:
`LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn` (Jordan decomposition),
`tendsto_atTop_ciSup`, `exists_polynomial_near_of_continuousOn` (Weierstrass),
`Convex.lipschitzOnWith_of_nnnorm_deriv_le`, `LipschitzOnWith.locallyBoundedVariationOn`.
Reused from T125's `MathlibExt.Analysis.StieltjesRSIntegral` (the refinement integral with free
tags) and `MathlibExt.Analysis.Integration.RiemannPartition`: `Partition`, `Partition.leftTag`,
`Partition.ofFinset`, `Partition.pointSet_ofFinset`, `Partition.points_mem_Icc`,
`Partition.a_le_b`, `rsSum` and `HasRSIntegral`. Proved here: the left-endpoint sums and integral,
their bilinearity, the insertion formula, monotonicity, existence, summation by parts, the bounds,
the two step-integrator values, the bridge to T125's sums and integral, and the two-tag sums.

T125's uniform-norm bound `|∫ f dh| ≤ B (2M + V(f))` is proved here again for the left-endpoint
sums by the same Abel summation: the left-endpoint integral also exists where T125's does not,
so the bound cannot be transferred through `hasLeftRSIntegral_of_hasRSIntegral`.

## References

* T. M. Apostol, *Mathematical Analysis*, 2nd ed. (1974), Chapter 7: Definition 7.1 (refinement
  form of the Riemann–Stieltjes integral) and Theorem 7.6 (integration by parts).
* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward application in
  survival analysis*, Ann. Statist. 18 (1990), 1501–1555 (the Duhamel equation and its
  left-continuous integrand).
-/

open Finset Filter Topology

@[expose] public section

namespace MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous

open MathlibExt.Analysis.StieltjesProductIntegral

/-! ### Sums and the integral -/

/-- The **left-endpoint Riemann–Stieltjes sum** of `f` against `h` over the cells of the finite
set `P`: every cell `(prev P x, x]` is tagged at its left endpoint. The minimum of `P` contributes
`f x * (h x - h x) = 0`. -/
noncomputable def leftSum (f h : ℝ → ℝ) (P : Finset ℝ) : ℝ :=
  ∑ x ∈ P, f (prev P x) * (h x - h (prev P x))

/-- The **right-endpoint sum** `∑_{x ∈ P} h x * (f x - f (prev P x))` of `h` against `f`, the
partner of `leftSum f h P` in summation by parts. -/
noncomputable def rightSum (h f : ℝ → ℝ) (P : Finset ℝ) : ℝ :=
  ∑ x ∈ P, h x * (f x - f (prev P x))

/-- The net of left-endpoint sums over the partitions `partitionPts a b s` of `[a, b]`. -/
noncomputable def leftPartitionSum (f h : ℝ → ℝ) (a b : ℝ) (s : Finset ℝ) : ℝ :=
  leftSum f h (partitionPts a b s)

/-- `I` is the **left-endpoint Riemann–Stieltjes integral** of `f` against `h` on `[a, b]`: the
left-endpoint sums converge to `I` along refinement of partitions. -/
def HasLeftRSIntegral (f h : ℝ → ℝ) (a b I : ℝ) : Prop :=
  Tendsto (leftPartitionSum f h a b) atTop (𝓝 I)

/-- The left-endpoint integral of `f` against `h` on `[a, b]` exists. -/
def LeftRSIntegrable (f h : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ I, HasLeftRSIntegral f h a b I

/-- The left-endpoint integral of `f` against `h` on `[a, b]`, or `0` if it does not exist. -/
noncomputable def leftRSIntegral (f h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  limUnder atTop (leftPartitionSum f h a b)

variable {f g h k V W : ℝ → ℝ} {a b I J : ℝ}

theorem HasLeftRSIntegral.unique (hI : HasLeftRSIntegral f h a b I)
    (hJ : HasLeftRSIntegral f h a b J) : I = J :=
  tendsto_nhds_unique hI hJ

theorem HasLeftRSIntegral.leftRSIntegral_eq (hI : HasLeftRSIntegral f h a b I) :
    leftRSIntegral f h a b = I :=
  hI.limUnder_eq

theorem LeftRSIntegrable.hasLeftRSIntegral (hi : LeftRSIntegrable f h a b) :
    HasLeftRSIntegral f h a b (leftRSIntegral f h a b) :=
  tendsto_nhds_limUnder hi

/-! ### Bilinearity -/

section Linearity

variable (P : Finset ℝ)

theorem leftSum_add_left : leftSum (f + g) h P = leftSum f h P + leftSum g h P := by
  simp only [leftSum, Pi.add_apply, add_mul, sum_add_distrib]

theorem leftSum_sub_left : leftSum (f - g) h P = leftSum f h P - leftSum g h P := by
  simp only [leftSum, Pi.sub_apply, sub_mul, sum_sub_distrib]

theorem leftSum_smul_left (c : ℝ) : leftSum (c • f) h P = c * leftSum f h P := by
  simp only [leftSum, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

theorem leftSum_add_right : leftSum f (g + h) P = leftSum f g P + leftSum f h P := by
  simp only [leftSum, Pi.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

theorem leftSum_sub_right : leftSum f (g - h) P = leftSum f g P - leftSum f h P := by
  simp only [leftSum, Pi.sub_apply, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

theorem leftSum_smul_right (c : ℝ) : leftSum f (c • h) P = c * leftSum f h P := by
  simp only [leftSum, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

end Linearity

theorem HasLeftRSIntegral.add_left (hf : HasLeftRSIntegral f h a b I)
    (hg : HasLeftRSIntegral g h a b J) : HasLeftRSIntegral (f + g) h a b (I + J) := by
  have e : leftPartitionSum (f + g) h a b =
      fun s => leftPartitionSum f h a b s + leftPartitionSum g h a b s :=
    funext fun s => leftSum_add_left _
  rw [HasLeftRSIntegral, e]
  exact hf.add hg

theorem HasLeftRSIntegral.sub_left (hf : HasLeftRSIntegral f h a b I)
    (hg : HasLeftRSIntegral g h a b J) : HasLeftRSIntegral (f - g) h a b (I - J) := by
  have e : leftPartitionSum (f - g) h a b =
      fun s => leftPartitionSum f h a b s - leftPartitionSum g h a b s :=
    funext fun s => leftSum_sub_left _
  rw [HasLeftRSIntegral, e]
  exact hf.sub hg

theorem HasLeftRSIntegral.smul_left (c : ℝ) (hf : HasLeftRSIntegral f h a b I) :
    HasLeftRSIntegral (c • f) h a b (c * I) := by
  have e : leftPartitionSum (c • f) h a b = fun s => c * leftPartitionSum f h a b s :=
    funext fun s => leftSum_smul_left _ c
  rw [HasLeftRSIntegral, e]
  exact hf.const_mul c

theorem HasLeftRSIntegral.add_right (hg : HasLeftRSIntegral f g a b I)
    (hh : HasLeftRSIntegral f h a b J) : HasLeftRSIntegral f (g + h) a b (I + J) := by
  have e : leftPartitionSum f (g + h) a b =
      fun s => leftPartitionSum f g a b s + leftPartitionSum f h a b s :=
    funext fun s => leftSum_add_right _
  rw [HasLeftRSIntegral, e]
  exact hg.add hh

theorem HasLeftRSIntegral.sub_right (hg : HasLeftRSIntegral f g a b I)
    (hh : HasLeftRSIntegral f h a b J) : HasLeftRSIntegral f (g - h) a b (I - J) := by
  have e : leftPartitionSum f (g - h) a b =
      fun s => leftPartitionSum f g a b s - leftPartitionSum f h a b s :=
    funext fun s => leftSum_sub_right _
  rw [HasLeftRSIntegral, e]
  exact hg.sub hh

theorem HasLeftRSIntegral.smul_right (c : ℝ) (hh : HasLeftRSIntegral f h a b I) :
    HasLeftRSIntegral f (c • h) a b (c * I) := by
  have e : leftPartitionSum f (c • h) a b = fun s => c * leftPartitionSum f h a b s :=
    funext fun s => leftSum_smul_right _ c
  rw [HasLeftRSIntegral, e]
  exact hh.const_mul c

/-! ### Telescoping, constants, and summation by parts -/

/-- The increments of `h` over the cells of a partition of `[a, b]` add up to `h b - h a`. -/
theorem sum_increments_partitionPts (hab : a ≤ b) (h : ℝ → ℝ) (s : Finset ℝ) :
    ∑ x ∈ partitionPts a b s, (h x - h (prev (partitionPts a b s) x)) = h b - h a :=
  sum_cells_partitionPts hab (fun u x => h x - h u) (sub_self _) (fun _ _ _ _ _ _ _ => by ring) s

theorem leftPartitionSum_const (hab : a ≤ b) (c : ℝ) (h : ℝ → ℝ) (s : Finset ℝ) :
    leftPartitionSum (fun _ => c) h a b s = c * (h b - h a) := by
  rw [leftPartitionSum, leftSum, ← mul_sum, sum_increments_partitionPts hab h s]

/-- `∫ₐᵇ c dh = c (h b - h a)`. -/
theorem hasLeftRSIntegral_const (hab : a ≤ b) (c : ℝ) (h : ℝ → ℝ) :
    HasLeftRSIntegral (fun _ => c) h a b (c * (h b - h a)) := by
  rw [HasLeftRSIntegral, funext (leftPartitionSum_const hab c h)]
  exact tendsto_const_nhds

/-- **Summation by parts**: on every partition of `[a, b]` the left-endpoint sum of `f` against
`h` and the right-endpoint sum of `h` against `f` add up to `f b h b - f a h a`. -/
theorem leftPartitionSum_add_rightSum (hab : a ≤ b) (f h : ℝ → ℝ) (s : Finset ℝ) :
    leftPartitionSum f h a b s + rightSum h f (partitionPts a b s) = f b * h b - f a * h a := by
  rw [leftPartitionSum, leftSum, rightSum, ← sum_add_distrib,
    ← sum_cells_partitionPts hab (fun u x => f x * h x - f u * h u) (sub_self _)
      (fun _ _ _ _ _ _ _ => by ring) s]
  exact sum_congr rfl fun x _ => by ring

/-- **Integration by parts.** If `∫ₐᵇ f dh = I`, the right-endpoint sums of `h` against `f`
converge along refinement to `f b h b - f a h a - I`. -/
theorem HasLeftRSIntegral.tendsto_rightSum (hab : a ≤ b) (hI : HasLeftRSIntegral f h a b I) :
    Tendsto (fun s => rightSum h f (partitionPts a b s)) atTop
      (𝓝 (f b * h b - f a * h a - I)) := by
  have e : (fun s => rightSum h f (partitionPts a b s)) =
      fun s => (f b * h b - f a * h a) - leftPartitionSum f h a b s :=
    funext fun s => by rw [← leftPartitionSum_add_rightSum hab f h s]; ring
  rw [e]
  exact tendsto_const_nhds.sub hI

/-! ### Inserting a point -/

/-- **Insertion formula.** Inserting `p` into the cell `(u, v]` of `P` (with `u = prev P p`)
changes the left-endpoint sum by `(f p - f u) (h v - h p)`. -/
theorem leftSum_insert_sub (f h : ℝ → ℝ) {P : Finset ℝ} {p v : ℝ} (hp : p ∉ P) (hv : v ∈ P)
    (hpv : p < v) (hvmin : ∀ y ∈ P, p < y → v ≤ y) (hlow : ∃ y ∈ P, y < p) :
    leftSum f h (insert p P) - leftSum f h P = (f p - f (prev P p)) * (h v - h p) := by
  rw [leftSum, leftSum, sum_cells_insert hp hv hpv hvmin hlow (fun u x => f u * (h x - h u)),
    sum_cells_eq_erase hp hv hpv hvmin hlow (fun u x => f u * (h x - h u))]
  ring

/-- For `f` and `h` monotone on `[a, b]`, adding a point to the partition does not decrease the
left-endpoint sum. -/
theorem leftPartitionSum_le_insert (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b))
    (hh : MonotoneOn h (Set.Icc a b)) (s : Finset ℝ) (p : ℝ) :
    leftPartitionSum f h a b s ≤ leftPartitionSum f h a b (insert p s) := by
  by_cases hp : a < p ∧ p < b
  · rw [leftPartitionSum, leftPartitionSum, partitionPts_insert_of_mem hp.1 hp.2]
    by_cases hmem : p ∈ partitionPts a b s
    · rw [insert_eq_of_mem hmem]
    · obtain ⟨v, hv, hpv, hvmin⟩ := exists_next ⟨b, right_mem_partitionPts s, hp.2⟩
      have hlow : ∃ y ∈ partitionPts a b s, y < p := ⟨a, left_mem_partitionPts s, hp.1⟩
      have key := leftSum_insert_sub f h hmem hv hpv hvmin hlow
      obtain ⟨hu, hup, -⟩ := prev_spec hlow
      have huI := mem_Icc_of_mem_partitionPts hab hu
      have hvI := mem_Icc_of_mem_partitionPts hab hv
      have hpI : p ∈ Set.Icc a b := ⟨hp.1.le, hp.2.le⟩
      have h1 : f (prev (partitionPts a b s) p) ≤ f p := hf huI hpI hup.le
      have h2 : h p ≤ h v := hh hpI hvI hpv.le
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  · rw [leftPartitionSum, leftPartitionSum, partitionPts_insert_of_not_mem hp]

/-- For `f` and `h` monotone on `[a, b]`, the left-endpoint sums increase under refinement. -/
theorem monotone_leftPartitionSum (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b))
    (hh : MonotoneOn h (Set.Icc a b)) : Monotone (leftPartitionSum f h a b) := by
  intro s t hst
  have key : ∀ u : Finset ℝ, leftPartitionSum f h a b s ≤ leftPartitionSum f h a b (s ∪ u) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp
    | insert p u _ ih =>
      rw [union_insert]
      exact ih.trans (leftPartitionSum_le_insert hab hf hh _ p)
  have := key (t \ s)
  rwa [union_sdiff_of_subset hst] at this

/-- For `f` and `h` monotone on `[a, b]`, the left-endpoint sums are at most `f b (h b - h a)`. -/
theorem leftPartitionSum_le_of_monotoneOn (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b))
    (hh : MonotoneOn h (Set.Icc a b)) (s : Finset ℝ) :
    leftPartitionSum f h a b s ≤ f b * (h b - h a) := by
  rw [leftPartitionSum, leftSum, ← sum_increments_partitionPts hab h s, mul_sum]
  refine sum_le_sum fun x hx => ?_
  have hu := mem_Icc_of_mem_partitionPts hab (prev_mem hx)
  have hxI := mem_Icc_of_mem_partitionPts hab hx
  exact mul_le_mul_of_nonneg_right (hf hu ⟨hab, le_rfl⟩ hu.2)
    (sub_nonneg.2 (hh hu hxI (prev_le _ x)))

/-! ### Existence -/

/-- **Existence for monotone integrand and integrator**: the left-endpoint sums converge to their
supremum. -/
theorem hasLeftRSIntegral_of_monotoneOn (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b))
    (hh : MonotoneOn h (Set.Icc a b)) :
    HasLeftRSIntegral f h a b (⨆ s, leftPartitionSum f h a b s) :=
  tendsto_atTop_ciSup (monotone_leftPartitionSum hab hf hh)
    ⟨f b * (h b - h a), by rintro _ ⟨s, rfl⟩; exact leftPartitionSum_le_of_monotoneOn hab hf hh s⟩

/-- **Existence for bounded variation.** If `f` and `h` have bounded variation on `[a, b]`, the
left-endpoint integral `∫ₐᵇ f dh` exists. No continuity of `f` or `h` is assumed. -/
theorem leftRSIntegrable_of_boundedVariationOn (hab : a ≤ b)
    (hf : BoundedVariationOn f (Set.Icc a b)) (hh : BoundedVariationOn h (Set.Icc a b)) :
    LeftRSIntegrable f h a b := by
  obtain ⟨f₁, f₂, hf₁, hf₂, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  obtain ⟨h₁, h₂, hh₁, hh₂, rfl⟩ := hh.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  exact ⟨_, ((hasLeftRSIntegral_of_monotoneOn hab hf₁ hh₁).sub_right
      (hasLeftRSIntegral_of_monotoneOn hab hf₁ hh₂)).sub_left
    ((hasLeftRSIntegral_of_monotoneOn hab hf₂ hh₁).sub_right
      (hasLeftRSIntegral_of_monotoneOn hab hf₂ hh₂))⟩

/-! ### Bounds on the sums -/

/-- A sum over the cells of a partition with weights `t x` bounded by `M` and increments of a
function controlled by `V` is at most `M (V b - V a)` in absolute value. -/
theorem abs_sum_cells_mul_le (hab : a ≤ b) (hc : IsControl k V a b) (t : ℝ → ℝ) {M : ℝ}
    (s : Finset ℝ) (ht : ∀ x ∈ partitionPts a b s, |t x| ≤ M) :
    |∑ x ∈ partitionPts a b s, t x * (k x - k (prev (partitionPts a b s) x))| ≤
      M * (V b - V a) := by
  rw [← sum_increments_partitionPts hab V s, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x hx => ?_)
  have hu := mem_Icc_of_mem_partitionPts hab (prev_mem hx)
  have hxI := mem_Icc_of_mem_partitionPts hab hx
  rw [abs_mul]
  exact mul_le_mul (ht x hx) (hc x _ hu.1 (prev_le _ x) hxI.2) (abs_nonneg _)
    ((abs_nonneg _).trans (ht x hx))

/-- `|S(f, h)| ≤ M (V b - V a)` for `|f| ≤ M` on `[a, b]` and `h` controlled by `V`. -/
theorem abs_leftPartitionSum_le_of_isControl (hab : a ≤ b) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hc : IsControl h V a b) (s : Finset ℝ) :
    |leftPartitionSum f h a b s| ≤ M * (V b - V a) :=
  abs_sum_cells_mul_le hab hc _ s fun _ hx =>
    hM _ (mem_Icc_of_mem_partitionPts hab (prev_mem hx))

/-- **Uniform-norm bound** (summation by parts): `|S(f, h)| ≤ B (2M + (W b - W a))` for `|h| ≤ B`
and `|f| ≤ M` on `[a, b]` and `f` controlled by `W`. No regularity of `h` is used. -/
theorem abs_leftPartitionSum_le_of_abs_le (hab : a ≤ b) {B M : ℝ}
    (hB : ∀ x ∈ Set.Icc a b, |h x| ≤ B) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hc : IsControl f W a b) (s : Finset ℝ) :
    |leftPartitionSum f h a b s| ≤ B * (2 * M + (W b - W a)) := by
  have hid := leftPartitionSum_add_rightSum hab f h s
  have hR : |rightSum h f (partitionPts a b s)| ≤ B * (W b - W a) :=
    abs_sum_cells_mul_le hab hc h s fun x hx => hB x (mem_Icc_of_mem_partitionPts hab hx)
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hfa : |f a * h a| ≤ M * B := by
    rw [abs_mul]; exact mul_le_mul (hM a haI) (hB a haI) (abs_nonneg _) ((abs_nonneg _).trans
      (hM a haI))
  have hfb : |f b * h b| ≤ M * B := by
    rw [abs_mul]; exact mul_le_mul (hM b hbI) (hB b hbI) (abs_nonneg _) ((abs_nonneg _).trans
      (hM b hbI))
  have e : leftPartitionSum f h a b s =
      f b * h b - f a * h a - rightSum h f (partitionPts a b s) := by linarith
  rw [e, show B * (2 * M + (W b - W a)) = M * B + M * B + B * (W b - W a) by ring]
  have t1 := abs_sub (f b * h b - f a * h a) (rightSum h f (partitionPts a b s))
  have t2 := abs_sub (f b * h b) (f a * h a)
  linarith

/-- **Lipschitz dependence on the integrator**, uniformly in the partition:
`|S(f, h) - S(f, g)| ≤ B (2M + (W b - W a))` for `|h - g| ≤ B` and `|f| ≤ M` on `[a, b]` and `f`
controlled by `W`. -/
theorem abs_leftPartitionSum_sub_le (hab : a ≤ b) {B M : ℝ}
    (hB : ∀ x ∈ Set.Icc a b, |h x - g x| ≤ B) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hc : IsControl f W a b) (s : Finset ℝ) :
    |leftPartitionSum f h a b s - leftPartitionSum f g a b s| ≤ B * (2 * M + (W b - W a)) := by
  rw [leftPartitionSum, leftPartitionSum, ← leftSum_sub_right]
  exact abs_leftPartitionSum_le_of_abs_le (h := h - g) hab hB hM hc s

/-! ### Bounds on the integral -/

theorem HasLeftRSIntegral.abs_le_of_isControl (hI : HasLeftRSIntegral f h a b I) (hab : a ≤ b)
    {M : ℝ} (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hc : IsControl h V a b) :
    |I| ≤ M * (V b - V a) :=
  le_of_tendsto' hI.abs fun s => abs_leftPartitionSum_le_of_isControl hab hM hc s

/-- `|∫ₐᵇ f dh| ≤ M · V(h)` for `|f| ≤ M` on `[a, b]`, where `V(h)` is the variation of `h` on
`[a, b]`. -/
theorem HasLeftRSIntegral.abs_le_mul_variation (hI : HasLeftRSIntegral f h a b I) (hab : a ≤ b)
    (hh : BoundedVariationOn h (Set.Icc a b)) {M : ℝ} (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    |I| ≤ M * (eVariationOn h (Set.Icc a b)).toReal := by
  have := hI.abs_le_of_isControl hab hM (exists_control_of_boundedVariationOn hh)
  rwa [variationOnFromTo.self, sub_zero, variationOnFromTo.eq_of_le _ _ hab,
    Set.inter_self] at this

/-- `|∫ₐᵇ f dh| ≤ M (h b - h a)` for `|f| ≤ M` on `[a, b]` and `h` monotone on `[a, b]`. -/
theorem HasLeftRSIntegral.abs_le_of_monotoneOn (hI : HasLeftRSIntegral f h a b I) (hab : a ≤ b)
    (hh : MonotoneOn h (Set.Icc a b)) {M : ℝ} (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    |I| ≤ M * (h b - h a) :=
  hI.abs_le_of_isControl hab hM (isControl_self_of_monotoneOn hh)

/-- **Uniform-norm bound**: `|∫ₐᵇ f dh| ≤ B (2M + (W b - W a))` for `|h| ≤ B` and `|f| ≤ M` on
`[a, b]` and `f` controlled by `W`. -/
theorem HasLeftRSIntegral.abs_le_of_abs_le (hI : HasLeftRSIntegral f h a b I) (hab : a ≤ b)
    {B M : ℝ} (hB : ∀ x ∈ Set.Icc a b, |h x| ≤ B) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hc : IsControl f W a b) : |I| ≤ B * (2 * M + (W b - W a)) :=
  le_of_tendsto' hI.abs fun s => abs_leftPartitionSum_le_of_abs_le hab hB hM hc s

/-- **Lipschitz dependence on the integrator**: `|∫ f dh - ∫ f dg| ≤ B (2M + (W b - W a))` for
`|h - g| ≤ B` and `|f| ≤ M` on `[a, b]` and `f` controlled by `W`. -/
theorem HasLeftRSIntegral.abs_sub_le_of_abs_sub_le (hI : HasLeftRSIntegral f h a b I)
    (hJ : HasLeftRSIntegral f g a b J) (hab : a ≤ b) {B M : ℝ}
    (hB : ∀ x ∈ Set.Icc a b, |h x - g x| ≤ B) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hc : IsControl f W a b) : |I - J| ≤ B * (2 * M + (W b - W a)) :=
  le_of_tendsto' (hI.sub hJ).abs fun s => abs_leftPartitionSum_sub_le hab hB hM hc s

/-! ### Existence for uniform limits of integrators of bounded variation -/

/-- A function controlled by `W` on `[a, b]` is bounded there by `|f a| + (W b - W a)`. -/
theorem abs_le_of_isControl (hc : IsControl f W a b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |f x| ≤ |f a| + (W b - W a) := by
  have h1 := hc x a le_rfl hx.1 hx.2
  have h2 := hc.sub_nonneg hx.1 hx.2 le_rfl
  have h3 := abs_sub_abs_le_abs_sub (f x) (f a)
  linarith

/-- **Existence for regulated integrators.** If `f` has bounded variation on `[a, b]` and `h` is a
uniform limit on `[a, b]` of functions of bounded variation (for instance of step functions, which
makes `h` regulated), the left-endpoint integral `∫ₐᵇ f dh` exists. -/
theorem leftRSIntegrable_of_uniform_approx (hab : a ≤ b) (hf : BoundedVariationOn f (Set.Icc a b))
    (happrox : ∀ ε > 0, ∃ g : ℝ → ℝ, BoundedVariationOn g (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, |h x - g x| ≤ ε) :
    LeftRSIntegrable f h a b := by
  set W := variationOnFromTo f (Set.Icc a b) a
  have hc : IsControl f W a b := exists_control_of_boundedVariationOn hf
  set M := |f a| + (W b - W a)
  have hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M := fun x hx => abs_le_of_isControl hc hx
  have hW : 0 ≤ W b - W a := hc.sub_nonneg le_rfl hab le_rfl
  have hM0 : 0 ≤ M := add_nonneg (abs_nonneg _) hW
  set C := 2 * M + (W b - W a) + 1
  have hC : 0 < C := by positivity
  have hcauchy : CauchySeq (leftPartitionSum f h a b) := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨g, hg, hgh⟩ := happrox (ε / (4 * C)) (by positivity)
    obtain ⟨J, hJ⟩ := leftRSIntegrable_of_boundedVariationOn hab hf hg
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hJ.cauchySeq (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have e1 := abs_leftPartitionSum_sub_le hab hgh hM hc m
    have e2 := abs_leftPartitionSum_sub_le hab hgh hM hc n
    have e3 := hN m hm n hn
    rw [Real.dist_eq] at e3 ⊢
    have hle : ε / (4 * C) * (2 * M + (W b - W a)) ≤ ε / 4 := by
      have : ε / (4 * C) * (2 * M + (W b - W a)) ≤ ε / (4 * C) * C :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e : ε / (4 * C) * C = ε / 4 := by field_simp
      linarith
    have t1 := abs_sub_le (leftPartitionSum f h a b m) (leftPartitionSum f g a b m)
      (leftPartitionSum f h a b n)
    have t2 := abs_sub_le (leftPartitionSum f g a b m) (leftPartitionSum f g a b n)
      (leftPartitionSum f h a b n)
    rw [abs_sub_comm (leftPartitionSum f g a b n)] at t2
    linarith
  exact ⟨_, tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hcauchy)⟩

/-- A polynomial has bounded variation on every compact interval. -/
theorem boundedVariationOn_polynomial_eval (p : Polynomial ℝ) (hab : a ≤ b) :
    BoundedVariationOn (fun x => p.eval x) (Set.Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (p.derivative.continuous (R := ℝ)).continuousOn (s := Set.Icc a b)
  have hlip : LipschitzOnWith C.toNNReal (fun x => p.eval x) (Set.Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => p.differentiableAt)
      fun x hx => by
        rw [Polynomial.deriv]
        refine NNReal.coe_le_coe.1 ?_
        rw [coe_nnnorm, Real.coe_toNNReal']
        exact (hC x hx).trans (le_max_left _ _)
  have := hlip.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rwa [Set.inter_self] at this

/-- **Existence for continuous integrators.** If `f` has bounded variation and `h` is continuous
on `[a, b]`, the left-endpoint integral `∫ₐᵇ f dh` exists. -/
theorem leftRSIntegrable_of_continuousOn (hab : a ≤ b) (hf : BoundedVariationOn f (Set.Icc a b))
    (hh : ContinuousOn h (Set.Icc a b)) : LeftRSIntegrable f h a b := by
  refine leftRSIntegrable_of_uniform_approx hab hf fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b h hh ε hε
  refine ⟨fun x => p.eval x, boundedVariationOn_polynomial_eval p hab, fun x hx => ?_⟩
  rw [abs_sub_comm]
  exact (hp x hx).le

/-! ### Step integrators -/

/-- Against the step `1_{[c, ∞)}` with `a < c ≤ b`, the left-endpoint sum is `f` at the largest
partition point strictly below `c`. -/
theorem leftPartitionSum_ite_le (f : ℝ → ℝ) {c : ℝ} (hac : a < c) (hcb : c ≤ b)
    (s : Finset ℝ) :
    leftPartitionSum f (fun x => if c ≤ x then 1 else 0) a b s =
      f (prev (partitionPts a b s) c) := by
  set P := partitionPts a b s
  have hne : (P.filter (c ≤ ·)).Nonempty :=
    ⟨b, mem_filter.2 ⟨right_mem_partitionPts s, hcb⟩⟩
  obtain ⟨hqP, hcq⟩ := mem_filter.1 ((P.filter (c ≤ ·)).min'_mem hne)
  set q := (P.filter (c ≤ ·)).min' hne
  have hqmin : ∀ y ∈ P, c ≤ y → q ≤ y := fun y hy hcy => min'_le _ _ (mem_filter.2 ⟨hy, hcy⟩)
  obtain ⟨hpc, hpclt, hpcmax⟩ := prev_spec ⟨a, left_mem_partitionPts s, hac⟩
  have hprevq : prev P q = prev P c :=
    prev_eq_of hpc (hpclt.trans_le hcq) fun z hz hzq =>
      hpcmax z hz (lt_of_not_ge fun hcz => absurd (hqmin z hz hcz) (not_le.2 hzq))
  rw [leftPartitionSum, leftSum, sum_eq_single q]
  · rw [hprevq, ite_eq_left hcq, ite_eq_right (not_le.2 hpclt)]
    ring
  · intro x hx hxq
    by_cases hcx : c ≤ x
    · have hqx : q < x := lt_of_le_of_ne (hqmin x hx hcx) (Ne.symm hxq)
      have : c ≤ prev P x := hcq.trans ((prev_spec ⟨q, hqP, hqx⟩).2.2 q hqP hqx)
      rw [ite_eq_left hcx, ite_eq_left this, sub_self, mul_zero]
    · have : ¬c ≤ prev P x := fun h' => hcx (h'.trans (prev_le P x))
      rw [ite_eq_right hcx, ite_eq_right this, sub_self, mul_zero]
  · intro hq
    exact absurd hqP hq

/-- The largest partition point strictly below `c ∈ (a, b]` converges to `c` from the left along
refinement. -/
theorem tendsto_prev_partitionPts {c : ℝ} (hac : a < c) (hcb : c ≤ b) :
    Tendsto (fun s => prev (partitionPts a b s) c) atTop (𝓝[<] c) := by
  have hlt : ∀ s, prev (partitionPts a b s) c < c := fun s =>
    (prev_spec ⟨a, left_mem_partitionPts s, hac⟩).2.1
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hlt⟩
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => Eventually.of_forall fun s =>
    (hlt s).trans hu⟩
  obtain ⟨y, hy1, hy2⟩ := exists_between (max_lt hl hac)
  refine eventually_atTop.2 ⟨{y}, fun s hs => ?_⟩
  have hyP : y ∈ partitionPts a b s := mem_partitionPts.2 (Or.inr (Or.inr
    ⟨hs (mem_singleton_self y), (le_max_right _ _).trans_lt hy1, hy2.trans_le hcb⟩))
  exact ((le_max_left _ _).trans_lt hy1).trans_le
    ((prev_spec ⟨a, left_mem_partitionPts s, hac⟩).2.2 y hyP hy2)

/-- **A jump from the left is weighted by the left limit.** For `a < c ≤ b`, if `f` has left
limit `L` at `c`, then `∫ₐᵇ f d1_{[c, ∞)} = L`. -/
theorem hasLeftRSIntegral_ite_le {c L : ℝ} (hac : a < c) (hcb : c ≤ b)
    (hL : Tendsto f (𝓝[<] c) (𝓝 L)) :
    HasLeftRSIntegral f (fun x => if c ≤ x then 1 else 0) a b L := by
  rw [HasLeftRSIntegral, funext (leftPartitionSum_ite_le f hac hcb)]
  exact hL.comp (tendsto_prev_partitionPts hac hcb)

/-- For `f` left-continuous at `c ∈ (a, b]`, `∫ₐᵇ f d1_{[c, ∞)} = f c`. -/
theorem hasLeftRSIntegral_ite_le_of_continuousWithinAt {c : ℝ} (hac : a < c) (hcb : c ≤ b)
    (hf : ContinuousWithinAt f (Set.Iic c) c) :
    HasLeftRSIntegral f (fun x => if c ≤ x then 1 else 0) a b (f c) :=
  hasLeftRSIntegral_ite_le hac hcb (hf.mono Set.Iio_subset_Iic_self).tendsto

/-- Against the step `1_{(c, ∞)}` with `a ≤ c < b`, the left-endpoint sum is `f c` for every
partition containing `c`. -/
theorem leftPartitionSum_ite_lt (f : ℝ → ℝ) {c : ℝ} (hcb : c < b) {s : Finset ℝ}
    (hcP : c ∈ partitionPts a b s) :
    leftPartitionSum f (fun x => if c < x then 1 else 0) a b s = f c := by
  set P := partitionPts a b s
  have hne : (P.filter (c < ·)).Nonempty :=
    ⟨b, mem_filter.2 ⟨right_mem_partitionPts s, hcb⟩⟩
  obtain ⟨hqP, hcq⟩ := mem_filter.1 ((P.filter (c < ·)).min'_mem hne)
  set q := (P.filter (c < ·)).min' hne
  have hqmin : ∀ y ∈ P, c < y → q ≤ y := fun y hy hcy => min'_le _ _ (mem_filter.2 ⟨hy, hcy⟩)
  have hprevq : prev P q = c :=
    prev_eq_of hcP hcq fun z hz hzq =>
      le_of_not_gt fun hcz => absurd (hqmin z hz hcz) (not_le.2 hzq)
  rw [leftPartitionSum, leftSum, sum_eq_single q]
  · rw [hprevq, ite_eq_left hcq, ite_eq_right (lt_irrefl c)]
    ring
  · intro x hx hxq
    by_cases hcx : c < x
    · have hqx : q < x := lt_of_le_of_ne (hqmin x hx hcx) (Ne.symm hxq)
      have : c < prev P x := hcq.trans_le ((prev_spec ⟨q, hqP, hqx⟩).2.2 q hqP hqx)
      rw [ite_eq_left hcx, ite_eq_left this, sub_self, mul_zero]
    · have : ¬c < prev P x := fun h' => hcx (h'.trans_le (prev_le P x))
      rw [ite_eq_right hcx, ite_eq_right this, sub_self, mul_zero]
  · intro hq
    exact absurd hqP hq

/-- **A jump from the right is weighted by the value.** For `a ≤ c < b` and every `f`,
`∫ₐᵇ f d1_{(c, ∞)} = f c`. -/
theorem hasLeftRSIntegral_ite_lt {c : ℝ} (hac : a ≤ c) (hcb : c < b) :
    HasLeftRSIntegral f (fun x => if c < x then 1 else 0) a b (f c) := by
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨{c}, fun s hs => ?_⟩)
  have hcP : c ∈ partitionPts a b s := by
    rcases hac.eq_or_lt with rfl | hlt
    · exact left_mem_partitionPts s
    · exact mem_partitionPts.2 (Or.inr (Or.inr ⟨hs (mem_singleton_self c), hlt, hcb⟩))
  exact (leftPartitionSum_ite_lt f hcb hcP).symm

/-! ### Agreement with the free-tag refinement integral -/

/-- The first point of a partition `P` has no predecessor among the points of `P`. -/
theorem prev_image_points_zero (P : Integration.Partition a b) :
    prev (univ.image P.points) (P.points 0) = P.points 0 := by
  refine prev_eq_self ?_
  rintro ⟨z, hz, hzlt⟩
  obtain ⟨k, -, rfl⟩ := mem_image.1 hz
  exact absurd (P.ordered.lt_iff_lt.1 hzlt) (Fin.not_lt_zero k)

/-- Among the points of a partition `P`, the predecessor of `P.points i.succ` is
`P.points i.castSucc`. -/
theorem prev_image_points_succ (P : Integration.Partition a b) (i : Fin P.n) :
    prev (univ.image P.points) (P.points i.succ) = P.points i.castSucc := by
  refine prev_eq_of (mem_image_of_mem _ (mem_univ _)) (P.ordered Fin.castSucc_lt_succ) ?_
  intro z hz hzlt
  obtain ⟨k, -, rfl⟩ := mem_image.1 hz
  exact P.ordered.monotone (Fin.le_castSucc_iff.2 (P.ordered.lt_iff_lt.1 hzlt))

/-- The left-endpoint sum over the points of a partition `P` of `[a, b]` (the canonical
`MathlibExt.Analysis.Integration.Partition`) is the Riemann–Stieltjes sum `rsSum` of its
left-endpoint tagging `P.leftTag`. -/
theorem leftSum_image_points_eq_rsSum_leftTag (f h : ℝ → ℝ) (P : Integration.Partition a b) :
    leftSum f h (univ.image P.points) = Integration.rsSum f h P.leftTag := by
  rw [leftSum, sum_image fun x _ y _ hxy => P.ordered.injective hxy, Fin.sum_univ_succ,
    prev_image_points_zero, sub_self, mul_zero, zero_add]
  simp only [prev_image_points_succ]
  rfl

/-- **Agreement with the free-tag integral.** If `∫ₐᵇ f dh = I` in the refinement sense with
arbitrary tags (`MathlibExt.Analysis.Integration.HasRSIntegral`), then the left-endpoint
integral exists and equals `I`. The converse fails: for `f = h = 1_{[c, ∞)}` with `a < c < b`
the left-endpoint integral exists and the free-tag one does not. -/
theorem hasLeftRSIntegral_of_hasRSIntegral (hI : Integration.HasRSIntegral f h a b I) :
    HasLeftRSIntegral f h a b I := by
  rw [HasLeftRSIntegral, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hP⟩ := hI ε hε
  have hab : a ≤ b := P.a_le_b
  refine ⟨univ.image P.points, fun s hs => ?_⟩
  set Q := Integration.Partition.ofFinset (partitionPts a b s)
    (fun x hx => Set.mem_Icc.2 (mem_Icc_of_mem_partitionPts hab hx)) (left_mem_partitionPts s)
    (right_mem_partitionPts s) with hQdef
  have hQpts : univ.image Q.points = partitionPts a b s := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact Integration.Partition.pointSet_ofFinset _ _ _ _
  have hQP : Q.IsRefinement P := by
    rintro x ⟨i, rfl⟩
    have hx := Integration.Partition.points_mem_Icc P i
    have hmem : P.points i ∈ partitionPts a b s := by
      rcases hx.1.eq_or_lt with h1 | h1
      · rw [← h1]; exact left_mem_partitionPts s
      rcases hx.2.eq_or_lt with h2 | h2
      · rw [h2]; exact right_mem_partitionPts s
      exact mem_partitionPts.2 (Or.inr (Or.inr ⟨hs (mem_image_of_mem _ (mem_univ i)), h1, h2⟩))
    rw [hQdef, Integration.Partition.pointSet_ofFinset]
    exact hmem
  rw [Real.dist_eq, leftPartitionSum, ← hQpts, leftSum_image_points_eq_rsSum_leftTag]
  exact hP Q.leftTag hQP

/-! ### Sums with different tags for the two factors

The Duhamel sums `duhamelSum A B a b s` of `MathlibExt.Analysis.StieltjesProductIntegral` evaluate
the first factor `P(A)(a, ·]` at the left endpoint of each cell and the second factor `P(B)(·, b]`
at the right endpoint. `twoTagSum F G h P` is that shape for general `F`, `G`, `h`. It is the
left-endpoint sum of `F G` plus a second-order term `∑ F(u) ΔG Δh`, and the right-endpoint sum of
`F G` minus `∑ ΔF G(x) Δh`; the second-order terms are the products of jumps that make the two
taggings differ. Both decompositions give a bound uniform in the partition and linear in `‖h‖_∞`,
the estimate the continuity of `h ↦ Ψ(h)` in the uniform norm needs. -/

section TwoTag

variable {F G : ℝ → ℝ}

/-- The **two-tag sum** `∑_{x ∈ P} F (prev P x) * (h x - h (prev P x)) * G x`: on every cell
`(prev P x, x]` the factor `F` is tagged at the left endpoint and `G` at the right endpoint. -/
noncomputable def twoTagSum (F G h : ℝ → ℝ) (P : Finset ℝ) : ℝ :=
  ∑ x ∈ P, F (prev P x) * (h x - h (prev P x)) * G x

/-- The Duhamel sum is the two-tag sum of `P(A)(a, ·]` (left tags) and `P(B)(·, b]` (right tags)
against `B - A`. -/
theorem duhamelSum_eq_twoTagSum (A B : ℝ → ℝ) (a b : ℝ) (s : Finset ℝ) :
    duhamelSum A B a b s = twoTagSum (productIntegral A a) (fun x => productIntegral B x b)
      (B - A) (partitionPts a b s) := by
  rw [duhamelSum, twoTagSum]
  exact sum_congr rfl fun x _ => by simp only [Pi.sub_apply]; ring

/-- Over the points of a partition `P` of `[a, b]`, the two-tag sum evaluates `F` at the tags of
`P.leftTag` and `G` at the tags of `P.rightTag`. -/
theorem twoTagSum_image_points (F G h : ℝ → ℝ) (P : Integration.Partition a b) :
    twoTagSum F G h (univ.image P.points) = ∑ i : Fin P.n, F (P.leftTag.tags i) *
      (h (P.points i.succ) - h (P.points i.castSucc)) * G (P.rightTag.tags i) := by
  rw [twoTagSum, sum_image fun x _ y _ hxy => P.ordered.injective hxy, Fin.sum_univ_succ,
    prev_image_points_zero, sub_self, mul_zero, zero_mul, zero_add]
  simp only [prev_image_points_succ]
  rfl

theorem twoTagSum_sub_right (P : Finset ℝ) :
    twoTagSum F G (h - g) P = twoTagSum F G h P - twoTagSum F G g P := by
  simp only [twoTagSum, Pi.sub_apply, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- **Left decomposition**: the two-tag sum is the left-endpoint sum of `F G` plus the
second-order term `∑ F(u) Δh ΔG`. -/
theorem twoTagSum_eq_leftSum_add (F G h : ℝ → ℝ) (P : Finset ℝ) :
    twoTagSum F G h P = leftSum (F * G) h P +
      ∑ x ∈ P, F (prev P x) * (h x - h (prev P x)) * (G x - G (prev P x)) := by
  rw [twoTagSum, leftSum, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by simp only [Pi.mul_apply]; ring

/-- **Right decomposition**: the two-tag sum is the right-endpoint sum of `F G` minus the
second-order term `∑ G(x) Δh ΔF`. -/
theorem twoTagSum_eq_rightSum_sub (F G h : ℝ → ℝ) (P : Finset ℝ) :
    twoTagSum F G h P = rightSum (F * G) h P -
      ∑ x ∈ P, G x * (h x - h (prev P x)) * (F x - F (prev P x)) := by
  rw [twoTagSum, rightSum, ← sum_sub_distrib]
  exact sum_congr rfl fun x _ => by simp only [Pi.mul_apply]; ring

/-- A product of bounded functions with controls is controlled: for `|F| ≤ M`, `|G| ≤ N` on
`[a, b]`, `F` controlled by `V` and `G` by `W`, the product `F G` is controlled by `N V + M W`. -/
theorem isControl_mul {M N : ℝ} (hM : ∀ x ∈ Set.Icc a b, |F x| ≤ M)
    (hN : ∀ x ∈ Set.Icc a b, |G x| ≤ N) (hF : IsControl F V a b) (hG : IsControl G W a b) :
    IsControl (F * G) (fun t => N * V t + M * W t) a b := by
  intro x y hy hyx hx
  have hxI : x ∈ Set.Icc a b := ⟨hy.trans hyx, hx⟩
  have hyI : y ∈ Set.Icc a b := ⟨hy, hyx.trans hx⟩
  have e : (F * G) x - (F * G) y = (F x - F y) * G x + F y * (G x - G y) := by
    simp only [Pi.mul_apply]; ring
  rw [e]
  have h1 : |(F x - F y) * G x| ≤ (V x - V y) * N := by
    rw [abs_mul]
    exact mul_le_mul (hF x y hy hyx hx) (hN x hxI) (abs_nonneg _)
      (hF.sub_nonneg hy hyx hx)
  have h2 : |F y * (G x - G y)| ≤ M * (W x - W y) := by
    rw [abs_mul]
    exact mul_le_mul (hM y hyI) (hG x y hy hyx hx) (abs_nonneg _)
      ((abs_nonneg _).trans (hM y hyI))
  calc |(F x - F y) * G x + F y * (G x - G y)|
      ≤ |(F x - F y) * G x| + |F y * (G x - G y)| := abs_add_le _ _
    _ ≤ (V x - V y) * N + M * (W x - W y) := add_le_add h1 h2
    _ = (N * V x + M * W x) - (N * V y + M * W y) := by ring

/-- **Uniform-norm bound for the two-tag sum.** For `|h| ≤ B`, `|F| ≤ M`, `|G| ≤ N` on `[a, b]`,
`F` controlled by `V` and `G` by `W`, every two-tag sum over a partition of `[a, b]` satisfies
`|∑ F(u) Δh G(x)| ≤ B (2MN + N (V b - V a) + 3M (W b - W a))`. No regularity of `h` is used, and
`F`, `G`, `h` may jump on the same side at the same point. -/
theorem abs_twoTagSum_le_of_abs_le (hab : a ≤ b) {B M N : ℝ}
    (hB : ∀ x ∈ Set.Icc a b, |h x| ≤ B) (hM : ∀ x ∈ Set.Icc a b, |F x| ≤ M)
    (hN : ∀ x ∈ Set.Icc a b, |G x| ≤ N) (hF : IsControl F V a b) (hG : IsControl G W a b)
    (s : Finset ℝ) :
    |twoTagSum F G h (partitionPts a b s)| ≤
      B * (2 * M * N + N * (V b - V a) + 3 * M * (W b - W a)) := by
  set P := partitionPts a b s
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a haI)
  have hMN : ∀ x ∈ Set.Icc a b, |(F * G) x| ≤ M * N := fun x hx => by
    rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hM x hx) (hN x hx) (abs_nonneg _) hM0
  have hL := abs_leftPartitionSum_le_of_abs_le hab hB hMN (isControl_mul hM hN hF hG) s
  have hR : |∑ x ∈ P, F (prev P x) * (h x - h (prev P x)) * (G x - G (prev P x))| ≤
      M * (2 * B) * (W b - W a) :=
    abs_sum_cells_mul_le hab hG _ s fun x hx => by
      have hu := mem_Icc_of_mem_partitionPts hab (prev_mem hx)
      have hxI := mem_Icc_of_mem_partitionPts hab hx
      rw [abs_mul]
      refine mul_le_mul (hM _ hu) ((abs_sub _ _).trans ?_) (abs_nonneg _) hM0
      linarith [hB x hxI, hB _ hu]
  rw [twoTagSum_eq_leftSum_add]
  refine (abs_add_le _ _).trans ?_
  rw [leftPartitionSum] at hL
  calc |leftSum (F * G) h P| +
        |∑ x ∈ P, F (prev P x) * (h x - h (prev P x)) * (G x - G (prev P x))|
      ≤ B * (2 * (M * N) + ((N * V b + M * W b) - (N * V a + M * W a))) +
        M * (2 * B) * (W b - W a) := add_le_add hL hR
    _ = B * (2 * M * N + N * (V b - V a) + 3 * M * (W b - W a)) := by ring

/-- **Lipschitz dependence of the two-tag sum on the integrator**, uniformly in the partition:
for `|h - g| ≤ B` on `[a, b]`, `|S(F, G; h) - S(F, G; g)| ≤ B (2MN + N (V b - V a) +
3M (W b - W a))`. -/
theorem abs_twoTagSum_sub_le (hab : a ≤ b) {B M N : ℝ}
    (hB : ∀ x ∈ Set.Icc a b, |h x - g x| ≤ B) (hM : ∀ x ∈ Set.Icc a b, |F x| ≤ M)
    (hN : ∀ x ∈ Set.Icc a b, |G x| ≤ N) (hF : IsControl F V a b) (hG : IsControl G W a b)
    (s : Finset ℝ) :
    |twoTagSum F G h (partitionPts a b s) - twoTagSum F G g (partitionPts a b s)| ≤
      B * (2 * M * N + N * (V b - V a) + 3 * M * (W b - W a)) := by
  rw [← twoTagSum_sub_right]
  exact abs_twoTagSum_le_of_abs_le (h := h - g) hab hB hM hN hF hG s

end TwoTag

end MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
