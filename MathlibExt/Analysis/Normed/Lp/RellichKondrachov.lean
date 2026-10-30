/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Lp.Compactness
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Sequences
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A weighted sequence model of Rellich–Kondrachov compactness

For suitable bounded domains `Ω`, the classical **Rellich–Kondrachov
theorem** gives compactness of the Sobolev embedding `H¹(Ω) ↪ L²(Ω)`;
the bounded domain and boundary regularity hypotheses matter.

Here we prove a specific one dimensional weighted sequence space analogue
in `ℓ²(ℕ, 𝕜)`, with weights `1 + n ^ 2`. The weight forces uniformly small
tails, and the canonical `ℓ^p` compactness criterion applies to the norm
bound and the tail estimate. The formalized objects are scalar sequences
indexed by `ℕ`; Sobolev spaces on domains provide the classical motivation.

Concretely, for `𝕜 = ℝ` or `ℂ`, we show that the set

```
rellichBall M = {x : ℓ²(ℕ, 𝕜) | ∀ F : Finset ℕ, ∑ n ∈ F, (1 + n ^ 2) * ‖x n‖ ^ 2 ≤ M ^ 2}
```

is totally bounded, closed, compact, and sequentially compact in `ℓ²(ℕ, 𝕜)`.
The finite-sum form of the defining bound is used instead of a `tsum`
bound, so no summability hypothesis is needed in the definition (for
nonnegative terms the two forms are equivalent). The canonical truncation
`lpTrunc 2` satisfies the weighted tail estimate `norm_sub_lpTrunc_sq_le`.

Companion to the `L^p`-space and compact-operator material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`.
Not one of the 72 v1 targets. Classical background: see e.g.
L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010,
Section 5.7, Theorem 1 (Rellich–Kondrachov), or H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Springer, 2011, Theorem 9.16.
-/

namespace MathlibExt.Analysis.Normed.Lp.RellichKondrachov

open scoped lp ENNReal Topology
open MathlibExt.Analysis.Normed.Lp.Compactness
open MathlibExt.Analysis.Normed.Lp.SchauderBasis

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Rellich weight `1 + n ^ 2`. -/
def rellichWeight (n : ℕ) : ℝ := 1 + (n : ℝ) ^ 2

theorem rellichWeight_nonneg (n : ℕ) : 0 ≤ rellichWeight n := by
  unfold rellichWeight
  positivity

theorem rellichWeight_pos (n : ℕ) : 0 < rellichWeight n := by
  unfold rellichWeight
  positivity

theorem one_le_rellichWeight (n : ℕ) : 1 ≤ rellichWeight n := by
  unfold rellichWeight
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem rellichWeight_mono {m n : ℕ} (h : m ≤ n) : rellichWeight m ≤ rellichWeight n := by
  unfold rellichWeight
  have h2 : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr h) 2
  linarith

/-- Membership in the Rellich ball: every finite weighted partial sum is
bounded by `M ^ 2`. -/
def memRellichBall (x : ℓ²(ℕ, 𝕜)) (M : ℝ) : Prop :=
  ∀ F : Finset ℕ, ∑ n ∈ F, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 ≤ M ^ 2

/-- The Rellich ball of radius `M`: sequences in `ℓ²(ℕ, 𝕜)` whose weighted
`ℓ²` energy is at most `M ^ 2`. -/
def rellichBall (M : ℝ) : Set (ℓ²(ℕ, 𝕜)) := {x | memRellichBall x M}

/-- The coercion of `(2 : ℝ≥0∞)` to `ℝ` is `2`. -/
private theorem toReal_two : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by simp

theorem summable_norm_sq (x : ℓ²(ℕ, 𝕜)) :
    Summable fun n => ‖(x : ℕ → 𝕜) n‖ ^ 2 := by
  have h := (lp.memℓp x).summable (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num)
  simpa only [toReal_two, Real.rpow_two] using h

/-- The `ℓ²` norm squared is the sum of the squared coordinate norms. -/
theorem norm_sq_eq_tsum (x : ℓ²(ℕ, 𝕜)) :
    ‖x‖ ^ 2 = ∑' n, ‖(x : ℕ → 𝕜) n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
    (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num) x
  simpa only [toReal_two, Real.rpow_two] using h

theorem summable_weighted {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hx : memRellichBall x M) :
    Summable fun n => rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 :=
  summable_of_sum_le (fun n => mul_nonneg (rellichWeight_nonneg n) (sq_nonneg _)) hx

theorem tsum_weighted_le {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hx : memRellichBall x M) :
    ∑' n, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 ≤ M ^ 2 :=
  Real.tsum_le_of_sum_le (fun n => mul_nonneg (rellichWeight_nonneg n) (sq_nonneg _)) hx

theorem norm_sq_le_of_memRellichBall {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hx : memRellichBall x M) :
    ‖x‖ ^ 2 ≤ M ^ 2 := by
  rw [norm_sq_eq_tsum]
  exact (summable_norm_sq x).tsum_le_of_sum_le fun F =>
    (Finset.sum_le_sum fun n _ =>
      le_mul_of_one_le_left (sq_nonneg _) (one_le_rellichWeight n)).trans (hx F)

theorem norm_le_of_memRellichBall {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hM : 0 ≤ M)
    (hx : memRellichBall x M) : ‖x‖ ≤ M := by
  have h := norm_sq_le_of_memRellichBall hx
  calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt h
    _ = M := Real.sqrt_sq hM

/-- If `x` is supported in a finite set `S` and its weighted sum over `S` is
at most `M ^ 2`, then `x` lies in the Rellich ball. -/
theorem memRellichBall_of_support {x : ℓ²(ℕ, 𝕜)} {S : Finset ℕ} {M : ℝ}
    (hS : ∀ n, (x : ℕ → 𝕜) n ≠ 0 → n ∈ S)
    (h : ∑ n ∈ S, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 ≤ M ^ 2) :
    memRellichBall x M := by
  intro F
  calc ∑ n ∈ F, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2
      = ∑ n ∈ F ∩ S, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 := by
        apply (Finset.sum_subset Finset.inter_subset_left _).symm
        intro n hnF hnnotin
        have hnS : n ∉ S := fun h => hnnotin (Finset.mem_inter.mpr ⟨hnF, h⟩)
        have hxn : (x : ℕ → 𝕜) n = 0 := by
          by_contra hne
          exact hnS (hS n hne)
        simp [hxn]
    _ ≤ ∑ n ∈ S, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          fun n _ _ => mul_nonneg (rellichWeight_nonneg n) (sq_nonneg _)
    _ ≤ M ^ 2 := h

/-- The tail norm identity: the distance from `x` to its truncation is the
`ℓ²` norm of the tail. -/
theorem norm_sub_lpTrunc_sq_eq {x : ℓ²(ℕ, 𝕜)} (N : ℕ) :
    ‖x - lpTrunc 2 N x‖ ^ 2 = ∑' n, ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 := by
  change ‖x - (∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → 𝕜) i))‖ ^ 2 = _
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.norm_sub_norm_compl_sub_single hp x (Finset.range N)
  have h2 := (summable_norm_sq x).sum_add_tsum_nat_add N
  have h3 := norm_sq_eq_tsum x
  simp only [toReal_two, Real.rpow_two] at h1
  linarith

/-- The tail estimate: the squared distance from `x` to its truncation is at
most `M ^ 2 / (1 + N ^ 2)`. -/
theorem norm_sub_lpTrunc_sq_le {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hx : memRellichBall x M)
    (N : ℕ) : ‖x - lpTrunc 2 N x‖ ^ 2 ≤ M ^ 2 / rellichWeight N := by
  rw [norm_sub_lpTrunc_sq_eq]
  have hw : Summable fun n => rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 :=
    summable_weighted hx
  have hinj : Function.Injective (· + N : ℕ → ℕ) := fun a b h => Nat.add_right_cancel h
  have hshift : Summable fun n => rellichWeight (n + N) * ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 :=
    hw.comp_injective hinj
  have hshift_unweighted : Summable fun n => ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 :=
    (summable_norm_sq x).comp_injective hinj
  have hle1 : ∑' n, ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 ≤
      ∑' n, (rellichWeight (n + N) * ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2) / rellichWeight N := by
    refine hshift_unweighted.tsum_le_tsum (fun n => ?_) (hshift.div_const _)
    rw [le_div_iff₀ (rellichWeight_pos N)]
    calc ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 * rellichWeight N
        ≤ ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 * rellichWeight (n + N) :=
          mul_le_mul_of_nonneg_left (rellichWeight_mono (Nat.le_add_left N n)) (sq_nonneg _)
      _ = rellichWeight (n + N) * ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 := mul_comm _ _
  have hle2 : ∑' n, (rellichWeight (n + N) * ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2) /
        rellichWeight N ≤ M ^ 2 / rellichWeight N := by
    rw [tsum_div_const]
    apply div_le_div_of_nonneg_right _ (rellichWeight_nonneg N)
    have hsplit := hw.sum_add_tsum_nat_add N
    have hfin : 0 ≤ ∑ i ∈ Finset.range N,
        rellichWeight i * ‖(x : ℕ → 𝕜) i‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (rellichWeight_nonneg i) (sq_nonneg _)
    have htot := tsum_weighted_le hx
    linarith
  exact hle1.trans hle2

/-- Canonical truncations land in the span of the first `N` basis vectors. -/
theorem lpTrunc_mem_span (N : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    lpTrunc 2 N x ∈ Submodule.span 𝕜
      ((fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜)) ''
        (Finset.range N : Set ℕ)) := by
  rw [lpTrunc_eq_lpSchauderBasis_proj (by norm_num)]
  have h := LinearMap.mem_range_self
    ((lpSchauderBasis (𝕜 := 𝕜) (p := 2) (by norm_num)).proj N).toLinearMap x
  rw [SchauderBasis.range_proj_eq_span] at h
  exact h

/-- The Rellich ball only depends on `|M|`, since the bound is on `M ^ 2`. -/
theorem rellichBall_abs (M : ℝ) :
    rellichBall (𝕜 := 𝕜) M = rellichBall (𝕜 := 𝕜) |M| := by
  ext x
  simp only [rellichBall, Set.mem_ofPred_eq, memRellichBall, sq_abs]

/-- The weighted tail bound is smaller than any positive squared tolerance. -/
private theorem exists_tail_bound_lt (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, M ^ 2 / rellichWeight N < ε ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|M| / ε)
  have hN' : |M| < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  have hsq : M ^ 2 < ((N : ℝ) * ε) ^ 2 := by
    apply sq_lt_sq.mpr
    simpa only [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) hε.le)] using hN'
  refine ⟨N, ?_⟩
  rw [div_lt_iff₀ (rellichWeight_pos N)]
  unfold rellichWeight
  nlinarith [sq_nonneg ε]

/-- **Rellich–Kondrachov, total boundedness form.** The Rellich ball is
totally bounded in `ℓ²(ℕ, 𝕜)`. -/
theorem totallyBounded_rellichBall (M : ℝ) :
    TotallyBounded (rellichBall (𝕜 := 𝕜) M) := by
  rw [rellichBall_abs]
  refine (totallyBounded_iff_bounded_and_uniformTailVanishing (p := 2) (by norm_num)).mpr
    ⟨?_, ?_⟩
  · exact isBounded_iff_forall_norm_le.mpr ⟨|M|, fun x hx =>
      norm_le_of_memRellichBall (abs_nonneg _) hx⟩
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_tail_bound_lt |M| hε
    refine ⟨N, fun x hx => ?_⟩
    have hlt := lt_of_le_of_lt (norm_sub_lpTrunc_sq_le hx N) hN
    have habs := sq_lt_sq.mp hlt
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hε] at habs

/-- **Rellich–Kondrachov, closedness form.** The Rellich ball is closed. -/
theorem isClosed_rellichBall (M : ℝ) : IsClosed (rellichBall (𝕜 := 𝕜) M) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u y hu hlim
  show memRellichBall y M
  intro F
  have hcoord : ∀ n : ℕ, Filter.Tendsto
      (fun k => ((u k : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) n) Filter.atTop (𝓝 ((y : ℕ → 𝕜) n)) := by
    intro n
    have h0 : Filter.Tendsto (fun k => ‖u k - y‖) Filter.atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hlim
    have hbound : ∀ k, ‖((u k : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) n - (y : ℕ → 𝕜) n‖ ≤ ‖u k - y‖ := by
      intro k
      have h := lp.norm_apply_le_norm (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (u k - y) n
      simpa [lp.coeFn_sub, Pi.sub_apply] using h
    have hsqueeze : Filter.Tendsto
        (fun k => ‖((u k : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) n - (y : ℕ → 𝕜) n‖)
        Filter.atTop (𝓝 0) :=
      squeeze_zero (fun k => norm_nonneg _) hbound h0
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hsqueeze
  have hsum : Filter.Tendsto
      (fun k => ∑ n ∈ F, rellichWeight n * ‖((u k : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) n‖ ^ 2)
      Filter.atTop (𝓝 (∑ n ∈ F, rellichWeight n * ‖(y : ℕ → 𝕜) n‖ ^ 2)) := by
    apply tendsto_finsetSum
    intro n _
    exact ((hcoord n).norm.pow 2).const_mul (rellichWeight n)
  exact le_of_tendsto_of_tendsto' hsum tendsto_const_nhds (fun k => hu k F)

/-- **Rellich–Kondrachov, compactness form.** The Rellich ball is compact in
`ℓ²(ℕ, 𝕜)`. -/
theorem isCompact_rellichBall (M : ℝ) : IsCompact (rellichBall (𝕜 := 𝕜) M) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨totallyBounded_rellichBall M, (isClosed_rellichBall M).isComplete⟩

/-- **Rellich–Kondrachov, sequential form.** Every sequence in the Rellich
ball has a subsequence converging in `ℓ²(ℕ, 𝕜)` to a point of the ball. -/
theorem exists_subseq_tendsto_of_memRellichBall (M : ℝ) {u : ℕ → ℓ²(ℕ, 𝕜)}
    (hu : ∀ n, u n ∈ rellichBall (𝕜 := 𝕜) M) :
    ∃ y ∈ rellichBall (𝕜 := 𝕜) M, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 y) := by
  obtain ⟨y, hy, φ, hφ, hlim⟩ := (isCompact_rellichBall M).tendsto_subseq hu
  exact ⟨y, hy, φ, hφ, hlim⟩

end MathlibExt.Analysis.Normed.Lp.RellichKondrachov
