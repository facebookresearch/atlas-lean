/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Data.Finset.SymmDiff

/-!
# F-statistics and admixture graphs

Patterson's f-statistics compare allele frequencies of populations. Allele frequencies are real
random variables `p : P → Ω → ℝ` on a measure space `(Ω, μ)`, where `P` indexes populations and
`ω : Ω` ranges over the randomness of the evolutionary process (and, in practice, over loci).
With `𝔼` denoting integration against `μ`,

* `f2 X Y = 𝔼[(p X - p Y) ^ 2]`,
* `f3 C A B = 𝔼[(p C - p A) * (p C - p B)]`,
* `f4 A B C D = 𝔼[(p A - p B) * (p C - p D)]`.

These are population-level (expected) quantities; no sampling-bias correction is involved.

## Model-free identities

All f-statistics are determined by `f2` (`f3_eq_f2`, `f4_eq_f2`) and `f2`, `f3` are special
cases of `f4` (`f2_eq_f4`, `f3_eq_f4`).

## The drift (admixture-graph) model

`DriftModel` states the admixture-graph model at the level of second moments, which is all
that f-statistics see. The frequency in population `X` is
`root + ∑ e, weight X e * incr e`, where `incr e` is the drift increment on edge `e` of the
graph, the increments are pairwise uncorrelated (`𝔼[incr e * incr f] = 0` for `e ≠ f`), and
the drift length of `e` is `len e = 𝔼[incr e ^ 2]` (measured in units of the second moment of
the frequency change, e.g. `≈ p₀ (1 - p₀) t / (2 N)` under pure drift). On an admixture graph
`weight X e` is the sum, over root-to-`X` paths through `e`, of the products of the admixture
proportions along the path; on a tree it is the `0`/`1` indicator of `e` lying on the
root-to-`X` lineage.

## Main results

* `f4_freq`: in the drift model `f4 A B C D` is the weighted overlap
  `∑ e, (w A e - w B e) * (w C e - w D e) * len e` of the paths `A–B` and `C–D`.
* `f2_eq_sum_symmDiff`: with binary (`0`/`1`) loadings, `f2` is the total drift length of the
  symmetric difference of the two lineage edge sets; when those sets are root-to-leaf paths of
  a tree, this is the additive tree distance.
* `f3_nonneg_of_hasBinaryLoadings`, `not_hasBinaryLoadings_of_f3_neg`: the three-population
  test. Every tree model has binary loadings, so a negative `f3 C A B` rules out every tree.
  (Binary loadings alone do not make a tree: see `HasBinaryLoadings`.)
* `f3_admixture`: if `C` is an `α : 1 - α` mixture of `A` and `B`, then
  `f3 C A B = -α (1 - α) f2 A B`; `f3_neg_of_admixture` gives the negative sign.
* `f3_admixture_drift`: drift on `C`'s private edge after admixture adds its length to `f3`.
* `f4_eq_zero_of_disjoint`: `f4` vanishes when the paths `A–B` and `C–D` share no edge.
* `f4_ratio`: f4-ratio estimation of an admixture proportion.
* `wahlund`: the Wahlund identity `H_T - H_S = 2 ∑ c i (q i - q̄) ^ 2`, so `F_ST ≥ 0`.

## References

* D. Reich, K. Thangaraj, N. Patterson, A. L. Price, L. Singh, *Reconstructing Indian
  population history*, Nature 461 (2009), 489–494.
* N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck,
  T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093.
* B. M. Peter, *Admixture, population structure, and F-statistics*, Genetics 202 (2016),
  1485–1501.
-/

@[expose] public section

open MeasureTheory
open scoped symmDiff

namespace MathlibExt.Biology.PopulationGenetics.FStatistics

variable {Ω P : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) (p : P → Ω → ℝ)

/-! ### Definitions and model-free identities -/

/-- The statistic `f2 X Y = 𝔼[(p X - p Y) ^ 2]`, the expected squared allele-frequency
difference between populations `X` and `Y`. -/
noncomputable def f2 (X Y : P) : ℝ := ∫ ω, (p X ω - p Y ω) ^ 2 ∂μ

/-- The statistic `f3 C A B = 𝔼[(p C - p A) * (p C - p B)]` of a target population `C` against
two source populations `A` and `B`. -/
noncomputable def f3 (C A B : P) : ℝ := ∫ ω, (p C ω - p A ω) * (p C ω - p B ω) ∂μ

/-- The statistic `f4 A B C D = 𝔼[(p A - p B) * (p C - p D)]`. -/
noncomputable def f4 (A B C D : P) : ℝ := ∫ ω, (p A ω - p B ω) * (p C ω - p D ω) ∂μ

variable {μ p}

/-- `f2 X X = 0`. -/
@[simp] theorem f2_self (X : P) : f2 μ p X X = 0 := by simp [f2]

/-- `f2` is symmetric. -/
theorem f2_comm (X Y : P) : f2 μ p X Y = f2 μ p Y X := by
  unfold f2
  congr 1 with ω
  ring

/-- `f2` is nonnegative. -/
theorem f2_nonneg (X Y : P) : 0 ≤ f2 μ p X Y :=
  integral_nonneg fun _ => sq_nonneg _

/-- `f4` is symmetric under exchanging the two pairs. -/
theorem f4_comm_pairs (A B C D : P) : f4 μ p A B C D = f4 μ p C D A B := by
  unfold f4
  congr 1 with ω
  ring

/-- `f4` changes sign when the first pair is swapped. -/
theorem f4_swap_left (A B C D : P) : f4 μ p A B C D = -f4 μ p B A C D := by
  unfold f4
  rw [← integral_neg]
  congr 1 with ω
  ring

/-- `f4` changes sign when the second pair is swapped. -/
theorem f4_swap_right (A B C D : P) : f4 μ p A B C D = -f4 μ p A B D C := by
  rw [f4_comm_pairs, f4_swap_left, f4_comm_pairs]

/-- `f2` is the special case `f4 A B A B`. -/
theorem f2_eq_f4 (A B : P) : f2 μ p A B = f4 μ p A B A B := by
  unfold f2 f4
  simp_rw [sq]

/-- `f3` is the special case `f4 C A C B`. -/
theorem f3_eq_f4 (C A B : P) : f3 μ p C A B = f4 μ p C A C B := rfl

/-- A difference of square-integrable frequencies has integrable square. -/
theorem integrable_sub_sq (hp : ∀ X, MemLp (p X) 2 μ) (X Y : P) :
    Integrable (fun ω => (p X ω - p Y ω) ^ 2) μ :=
  ((hp X).sub (hp Y)).integrable_sq

/-- `f3` in terms of `f2`: `f3 C A B = (f2 C A + f2 C B - f2 A B) / 2`. -/
theorem f3_eq_f2 (hp : ∀ X, MemLp (p X) 2 μ) (C A B : P) :
    f3 μ p C A B = (f2 μ p C A + f2 μ p C B - f2 μ p A B) / 2 := by
  unfold f3 f2
  have h1 : Integrable (fun ω => (p C ω - p A ω) ^ 2 + (p C ω - p B ω) ^ 2) μ :=
    (integrable_sub_sq hp C A).add (integrable_sub_sq hp C B)
  have h : ∀ ω, (p C ω - p A ω) * (p C ω - p B ω) =
      ((p C ω - p A ω) ^ 2 + (p C ω - p B ω) ^ 2 - (p A ω - p B ω) ^ 2) / 2 := fun ω => by
    ring
  simp_rw [h]
  rw [integral_div, integral_sub h1 (integrable_sub_sq hp A B),
    integral_add (integrable_sub_sq hp C A) (integrable_sub_sq hp C B)]

/-- `f4` in terms of `f2`: `f4 A B C D = (f2 A D + f2 B C - f2 A C - f2 B D) / 2`. -/
theorem f4_eq_f2 (hp : ∀ X, MemLp (p X) 2 μ) (A B C D : P) :
    f4 μ p A B C D = (f2 μ p A D + f2 μ p B C - f2 μ p A C - f2 μ p B D) / 2 := by
  unfold f4 f2
  have h1 : Integrable (fun ω => (p A ω - p D ω) ^ 2 + (p B ω - p C ω) ^ 2) μ :=
    (integrable_sub_sq hp A D).add (integrable_sub_sq hp B C)
  have h2 : Integrable
      (fun ω => (p A ω - p D ω) ^ 2 + (p B ω - p C ω) ^ 2 - (p A ω - p C ω) ^ 2) μ :=
    h1.sub (integrable_sub_sq hp A C)
  have h : ∀ ω, (p A ω - p B ω) * (p C ω - p D ω) = ((p A ω - p D ω) ^ 2 + (p B ω - p C ω) ^ 2
      - (p A ω - p C ω) ^ 2 - (p B ω - p D ω) ^ 2) / 2 := fun ω => by
    ring
  simp_rw [h]
  rw [integral_div, integral_sub h2 (integrable_sub_sq hp B D),
    integral_sub h1 (integrable_sub_sq hp A C),
    integral_add (integrable_sub_sq hp A D) (integrable_sub_sq hp B C)]

/-! ### The drift (admixture-graph) model -/

/-- The admixture-graph drift model, stated at the level of second moments.

The allele frequency of population `X` is `root + ∑ e, weight X e * incr e` (see
`DriftModel.freq`), where `E` is the (finite) set of edges of the graph.

* `root` is the ancestral (root) allele frequency;
* `incr e` is the drift increment (frequency change) along edge `e`;
* `len e` is the drift length of edge `e`, i.e. the second moment `𝔼[incr e ^ 2]`;
* `weight X e` is the probability that a lineage sampled in `X` traverses `e`: on an
  admixture graph it is the sum, over root-to-`X` paths through `e`, of the product of the
  admixture proportions on the path; on a tree it is the `0`/`1` indicator that `e` lies on
  the root-to-`X` lineage.

f-statistics depend only on second moments of frequency differences, in which the root
cancels, so only these are assumed: the increments are square integrable, pairwise
uncorrelated (the mixed second moments `𝔼[incr e * incr f]`, `e ≠ f`, vanish, as they do for
independent mean-zero drift on distinct edges), and `𝔼[incr e ^ 2] = len e`. -/
structure DriftModel (μ : Measure Ω) (E P : Type*) [Fintype E] where
  /-- Ancestral (root) allele frequency. -/
  root : Ω → ℝ
  /-- Drift increment along edge `e`. -/
  incr : E → Ω → ℝ
  /-- Drift length of edge `e`. -/
  len : E → ℝ
  /-- Probability that a lineage sampled in population `X` traverses edge `e`. -/
  weight : P → E → ℝ
  /-- The root frequency is square integrable. -/
  memLp_root : MemLp root 2 μ
  /-- Each drift increment is square integrable. -/
  memLp_incr : ∀ e, MemLp (incr e) 2 μ
  /-- Increments on distinct edges are uncorrelated. -/
  inner_incr : ∀ e f, e ≠ f → ∫ ω, incr e ω * incr f ω ∂μ = 0
  /-- The drift length of an edge is the second moment of its increment. -/
  sq_incr : ∀ e, ∫ ω, incr e ω ^ 2 ∂μ = len e

namespace DriftModel

variable {E : Type*} [Fintype E] (M : DriftModel μ E P)

/-- The allele frequency of population `X`: the root frequency plus the weighted sum of the
drift increments of the edges traversed by lineages from `X`. -/
def freq (X : P) : Ω → ℝ := fun ω => M.root ω + ∑ e, M.weight X e * M.incr e ω

/-- Drift lengths are nonnegative. -/
theorem len_nonneg (e : E) : 0 ≤ M.len e := by
  rw [← M.sq_incr e]
  exact integral_nonneg fun _ => sq_nonneg _

/-- A weighted sum of increments is square integrable. -/
theorem memLp_sum_incr (a : E → ℝ) : MemLp (fun ω => ∑ e, a e * M.incr e ω) 2 μ :=
  memLp_finsetSum _ fun e _ => (M.memLp_incr e).const_mul (a e)

/-- Population frequencies are square integrable. -/
theorem memLp_freq (X : P) : MemLp (M.freq X) 2 μ :=
  M.memLp_root.add (M.memLp_sum_incr (M.weight X))

/-- Bilinearity of the second moment of increments:
`𝔼[(∑ e, a e * incr e) * (∑ f, b f * incr f)] = ∑ e, a e * b e * len e`. -/
theorem integral_sum_mul_sum (a b : E → ℝ) :
    ∫ ω, (∑ e, a e * M.incr e ω) * (∑ f, b f * M.incr f ω) ∂μ = ∑ e, a e * b e * M.len e := by
  classical
  have hint : ∀ e f, Integrable (fun ω => a e * b f * (M.incr e ω * M.incr f ω)) μ :=
    fun e f => (((M.memLp_incr e).integrable_mul (M.memLp_incr f))).const_mul _
  simp_rw [Finset.sum_mul_sum]
  have : ∀ ω, ∑ e, ∑ f, a e * M.incr e ω * (b f * M.incr f ω) =
      ∑ e, ∑ f, a e * b f * (M.incr e ω * M.incr f ω) := fun ω => by
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
    ring
  simp_rw [this]
  rw [integral_finsetSum _ fun e _ => integrable_finsetSum _ fun f _ => hint e f]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finsetSum _ fun f _ => hint e f]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single e]
  · rw [← M.sq_incr e]
    simp_rw [sq]
  · intro f _ hfe
    rw [M.inner_incr e f (Ne.symm hfe), mul_zero]
  · simp

/-- `f4` in the drift model: the root cancels, and `f4 A B C D` is the drift length shared by
the paths `A–B` and `C–D`, weighted by `(w A e - w B e) * (w C e - w D e)`. -/
theorem f4_freq (A B C D : P) :
    f4 μ M.freq A B C D =
      ∑ e, (M.weight A e - M.weight B e) * (M.weight C e - M.weight D e) * M.len e := by
  have h : ∀ X Y : P, ∀ ω, M.freq X ω - M.freq Y ω =
      ∑ e, (M.weight X e - M.weight Y e) * M.incr e ω := fun X Y ω => by
    simp only [freq, sub_mul, Finset.sum_sub_distrib]
    ring
  unfold f4
  simp_rw [h]
  exact M.integral_sum_mul_sum _ _

/-- `f2` in the drift model: `f2 X Y = ∑ e, (w X e - w Y e) ^ 2 * len e`. -/
theorem f2_freq (X Y : P) :
    f2 μ M.freq X Y = ∑ e, (M.weight X e - M.weight Y e) ^ 2 * M.len e := by
  rw [f2_eq_f4, f4_freq]
  simp_rw [sq]

/-- `f3` in the drift model: `f3 C A B = ∑ e, (w C e - w A e) * (w C e - w B e) * len e`. -/
theorem f3_freq (C A B : P) :
    f3 μ M.freq C A B =
      ∑ e, (M.weight C e - M.weight A e) * (M.weight C e - M.weight B e) * M.len e := by
  rw [f3_eq_f4, f4_freq]

/-- `f4 A B C D = 0` when no edge contributes to both the `A–B` and the `C–D` path. On a tree
with split `AB | CD` the paths `A–B` and `C–D` share no edge, so this hypothesis holds. -/
theorem f4_eq_zero_of_disjoint {A B C D : P}
    (h : ∀ e, (M.weight A e - M.weight B e) * (M.weight C e - M.weight D e) = 0) :
    f4 μ M.freq A B C D = 0 := by
  simp [f4_freq, h]

/-- The model has binary loadings if every lineage weight is `0` or `1`.

Every tree model has binary loadings: there `weight X e` is the indicator of `e` lying on the
root-to-`X` path. The converse fails, since nothing forces the weight-`1` edge sets to be
compatible root-to-leaf paths: two edges of length `1` and four populations with weight
vectors `00`, `10`, `01`, `11` have binary loadings, but their `f2` distances form a square,
which violates the four-point condition of tree metrics. The results below use only the binary
values, so they apply to every tree. -/
def HasBinaryLoadings : Prop := ∀ X e, M.weight X e = 0 ∨ M.weight X e = 1

/-- The edges of weight `1` for population `X`; on a tree, the root-to-`X` lineage. -/
noncomputable def lineage (X : P) : Finset E :=
  haveI := Classical.decEq ℝ
  {e | M.weight X e = 1}

/-- With binary loadings `f3` is nonnegative; on a tree it is the drift length of the path from
`C` to the `A–B` path. -/
theorem f3_nonneg_of_hasBinaryLoadings (hM : M.HasBinaryLoadings) (C A B : P) :
    0 ≤ f3 μ M.freq C A B := by
  rw [f3_freq]
  refine Finset.sum_nonneg fun e _ => mul_nonneg ?_ (M.len_nonneg e)
  rcases hM C e with hC | hC <;> rcases hM A e with hA | hA <;> rcases hM B e with hB | hB <;>
    norm_num [hA, hB, hC]

/-- With binary loadings `f2 X Y` is the total drift length of the edges in exactly one of the
weight-`1` edge sets of `X` and `Y`. On a tree, where these sets are the root-to-`X` and
root-to-`Y` paths, this is the additive tree distance between `X` and `Y`. -/
theorem f2_eq_sum_symmDiff [DecidableEq E] (hM : M.HasBinaryLoadings) (X Y : P) :
    f2 μ M.freq X Y = ∑ e ∈ M.lineage X ∆ M.lineage Y, M.len e := by
  rw [f2_freq, ← Finset.univ_inter (M.lineage X ∆ M.lineage Y), ← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases hM X e with hX | hX <;> rcases hM Y e with hY | hY <;>
    simp [lineage, Finset.mem_symmDiff, hX, hY]

/-- Three-population test: a negative `f3 C A B` is incompatible with binary loadings, hence
with every tree model. -/
theorem not_hasBinaryLoadings_of_f3_neg {C A B : P} (h : f3 μ M.freq C A B < 0) :
    ¬ M.HasBinaryLoadings :=
  fun hM => (M.f3_nonneg_of_hasBinaryLoadings hM C A B).not_gt h

/-- If `C` is a mixture of `A` and `B` in proportions `α : 1 - α` (with no subsequent drift),
then `f3 C A B = -α (1 - α) f2 A B`. -/
theorem f3_admixture {A B C : P} {α : ℝ}
    (h : M.weight C = α • M.weight A + (1 - α) • M.weight B) :
    f3 μ M.freq C A B = -(α * (1 - α)) * f2 μ M.freq A B := by
  rw [f3_freq, f2_freq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [h]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Admixture followed by drift: if `C` is an `α : 1 - α` mixture of `A` and `B` that then
drifts along a private edge `c` (not traversed by `A` or `B`), then
`f3 C A B = len c - α (1 - α) f2 A B`; post-admixture drift can mask the admixture signal. -/
theorem f3_admixture_drift [DecidableEq E] {A B C : P} {α : ℝ} {c : E}
    (h : M.weight C = α • M.weight A + (1 - α) • M.weight B + Pi.single c 1)
    (hA : M.weight A c = 0) (hB : M.weight B c = 0) :
    f3 μ M.freq C A B = M.len c - α * (1 - α) * f2 μ M.freq A B := by
  rw [f3_freq, f2_freq, Finset.mul_sum]
  have key : ∀ e, (M.weight C e - M.weight A e) * (M.weight C e - M.weight B e) * M.len e =
      (Pi.single c (M.len c) : E → ℝ) e -
        α * (1 - α) * ((M.weight A e - M.weight B e) ^ 2 * M.len e) := fun e => by
    rw [h]
    by_cases he : e = c
    · subst he
      simp [hA, hB]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, he, ite_false]
      ring
  simp_rw [key, Finset.sum_sub_distrib]
  simp

/-- Three-population test, converse direction: a nondegenerate pure admixture
(`0 < α < 1`, `f2 A B > 0`) yields a negative `f3 C A B`. -/
theorem f3_neg_of_admixture {A B C : P} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAB : 0 < f2 μ M.freq A B) (h : M.weight C = α • M.weight A + (1 - α) • M.weight B) :
    f3 μ M.freq C A B < 0 := by
  rw [M.f3_admixture h]
  have : 0 < α * (1 - α) := mul_pos hα0 (by linarith)
  nlinarith

/-- If `X` is an `α : 1 - α` mixture of `Y` and `C`, then `f4 A O X C = α * f4 A O Y C`
(bilinearity of `f4`, together with `f4 A O C C = 0`). -/
theorem f4_admixture_right {A O X Y C : P} {α : ℝ}
    (h : M.weight X = α • M.weight Y + (1 - α) • M.weight C) :
    f4 μ M.freq A O X C = α * f4 μ M.freq A O Y C := by
  rw [f4_freq, f4_freq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [h]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- f4-ratio estimation (Patterson et al. 2012). Let `X` be an `α : 1 - α` mixture of a
source lineage `Y` and of `C`, where `Y` is unsampled but sister to the sampled population `B`
relative to the `A–O` path, so that `f4 A O Y C = f4 A O B C`. If this value is nonzero, the
ratio `f4 A O X C / f4 A O B C` of two estimable statistics recovers the admixture
proportion `α`. -/
theorem f4_ratio {A O X Y B C : P} {α : ℝ}
    (h : M.weight X = α • M.weight Y + (1 - α) • M.weight C)
    (hYB : f4 μ M.freq A O Y C = f4 μ M.freq A O B C) (hB : f4 μ M.freq A O B C ≠ 0) :
    f4 μ M.freq A O X C / f4 μ M.freq A O B C = α := by
  rw [M.f4_admixture_right h, hYB, mul_div_assoc, div_self hB, mul_one]

end DriftModel

/-! ### The Wahlund effect -/

section Wahlund

variable {ι : Type*} [Fintype ι] (c q : ι → ℝ)

/-- Mean allele frequency `q̄ = ∑ i, c i * q i` of a population made of subpopulations with
weights `c i` and allele frequencies `q i`. -/
def meanFreq : ℝ := ∑ i, c i * q i

/-- Mean within-subpopulation (Hardy–Weinberg) heterozygosity `H_S = ∑ i, c i * 2 q i (1 - q i)`.
-/
def hetSub : ℝ := ∑ i, c i * (2 * q i * (1 - q i))

/-- Total heterozygosity `H_T = 2 q̄ (1 - q̄)` expected under random mating of the pooled
population. -/
def hetTotal : ℝ := 2 * meanFreq c q * (1 - meanFreq c q)

/-- Wahlund identity: for weights summing to `1`, `H_T - H_S = 2 ∑ i, c i * (q i - q̄) ^ 2`,
twice the weighted variance of subpopulation frequencies. -/
theorem wahlund (hc : ∑ i, c i = 1) :
    hetTotal c q - hetSub c q = 2 * ∑ i, c i * (q i - meanFreq c q) ^ 2 := by
  have h1 : ∀ i, c i * (q i - meanFreq c q) ^ 2 =
      c i * q i ^ 2 - 2 * meanFreq c q * (c i * q i) + meanFreq c q ^ 2 * c i := fun i => by
    ring
  have h2 : ∀ i, c i * (2 * q i * (1 - q i)) = 2 * (c i * q i) - 2 * (c i * q i ^ 2) :=
    fun i => by ring
  simp only [hetTotal, hetSub, h1, h2, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hc]
  unfold meanFreq
  ring

/-- The Wahlund effect: with nonnegative weights summing to `1`, subdivision lowers
heterozygosity, `H_S ≤ H_T`. -/
theorem hetSub_le_hetTotal (hc0 : ∀ i, 0 ≤ c i) (hc : ∑ i, c i = 1) :
    hetSub c q ≤ hetTotal c q := by
  have := wahlund c q hc
  have : 0 ≤ ∑ i, c i * (q i - meanFreq c q) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc0 i) (sq_nonneg _)
  linarith

/-- `F_ST = (H_T - H_S) / H_T` is nonnegative for nonnegative weights summing to `1`. The ratio
is defined only when `H_T > 0` (at a fixed allele `H_T = H_S = 0`), so that is assumed. -/
theorem fst_nonneg (hc0 : ∀ i, 0 ≤ c i) (hc : ∑ i, c i = 1) (hT : 0 < hetTotal c q) :
    0 ≤ (hetTotal c q - hetSub c q) / hetTotal c q :=
  div_nonneg (sub_nonneg.2 (hetSub_le_hetTotal c q hc0 hc)) hT.le

end Wahlund

end MathlibExt.Biology.PopulationGenetics.FStatistics
