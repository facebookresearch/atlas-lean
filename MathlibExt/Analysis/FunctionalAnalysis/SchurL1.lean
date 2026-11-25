/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

import MathlibExt.Analysis.Normed.Lp.DualC0
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Schur's theorem: weak convergence implies norm convergence in `ℓ¹`

Schur's theorem (J. Schur, 1921, "Über lineare Transformationen in der
Theorie der unendlichen Reihen", Crelle's Journal) says that `ℓ¹` is the
only `ℓᵖ` space with this property: a sequence that converges weakly in
`ℓ¹(ℕ, 𝕜)` already converges in norm. The other `ℓᵖ` spaces do not have
it (the moving bump `eₙ` in `ℓ²` converges weakly to `0` but `‖eₙ‖ = 1`).

The proof is the classical gliding-hump argument. If the norms do not go
to `0`, some `ε > 0` is a frequent lower bound for them; since the
coordinates converge to `0`, one can inductively choose a subsequence and
increasing cutoffs so that each chosen term concentrates its mass on one
disjoint block. The bounded sequence which is the pointwise conjugate sign
of the chosen term on its block then defines a continuous functional on
`ℓ¹` (via `l1DualOfBounded`) whose values on the subsequence stay at
least `ε / 2` away from `0`, contradicting weak convergence to `0`.

This is a companion to the weak-convergence material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and its
Riesz-representation section (batch 38 proved the general facts that
weakly convergent sequences in a normed space are bounded and that the
norm is weakly lower semicontinuous); the new content is the `ℓ¹`
gliding-hump argument itself, which is neither in the pinned Mathlib nor
in base MathlibExt. It is not one of the 72 v1 targets: v1 never discusses
`ℓ¹` weak convergence.

## Main declarations

* `schur_tendsto_of_weak_tendsto` : weak convergence in `ℓ¹` implies norm
  convergence.
* `schur_tendsto_norm_sub_of_weak_tendsto` : the corresponding
  `‖x n - x₀‖ → 0` form.
* `l1DualOfBounded` : the functional on `ℓ¹` given by pairing with a
  bounded sequence.
-/

@[expose] public section

open Filter Finset
open MathlibExt.Analysis.Normed.Lp.DualC0 (summable_norm_lp_one)
open scoped Topology ENNReal

namespace MathlibExt.Analysis.FunctionalAnalysis.SchurL1

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The $\ell^1$ norm is the sum of the coordinate norms.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. Every $x \in \ell^1(\mathbb{N}, \mathbb{K})$ satisfies
$\|x\| = \sum_{i=0}^{\infty} |x_i|$. -/
theorem l1_norm_eq_tsum (x : lp (fun _ : ℕ => 𝕜) 1) : ‖x‖ = ∑' i, ‖x i‖ := by
  have h1 : (1 : ℝ≥0∞).toReal = 1 := ENNReal.toReal_one
  rw [lp.norm_eq_tsum_rpow (by rw [h1]; norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal) x, h1]
  simp [Real.rpow_one]

/-- **The pairing of $\ell^1$ with sequences bounded by $1$ is summable.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$. If $y : \mathbb{N} \to \mathbb{K}$ satisfies $\|y_i\| \le 1$ for
every $i$ and $x \in \ell^1(\mathbb{N}, \mathbb{K})$, then the series $\sum_i y_i x_i$ is
summable. -/
theorem summable_bounded_mul_l1 (y : ℕ → 𝕜) (hy : ∀ i, ‖y i‖ ≤ 1)
    (x : lp (fun _ : ℕ => 𝕜) 1) : Summable fun i => y i * x i := by
  apply Summable.of_norm_bounded (summable_norm_lp_one x)
  intro i
  rw [norm_mul]
  calc ‖y i‖ * ‖x i‖ ≤ 1 * ‖x i‖ := by gcongr; exact hy i
    _ = ‖x i‖ := one_mul _

/-- **Pairing $\ell^1$ with a sequence bounded by one.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $(y_i)_{i \in \mathbb{N}}$ be a sequence in $\mathbb{K}$ with
$|y_i| \le 1$ for every $i$. The pairing with $y$ is the continuous linear functional
$\ell^1(\mathbb{N}, \mathbb{K}) \to \mathbb{K}$ given by $x \mapsto \sum_{i=0}^{\infty} y_i x_i$. -/
noncomputable def l1DualOfBounded (y : ℕ → 𝕜) (hy : ∀ i, ‖y i‖ ≤ 1) :
    lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, y i * x i
      map_add' := fun x z => by
        rw [← Summable.tsum_add (summable_bounded_mul_l1 y hy x) (summable_bounded_mul_l1 y hy z)]
        exact tsum_congr fun i => by simp [mul_add]
      map_smul' := fun c x => by
        rw [smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun i => by simp [smul_eq_mul, mul_left_comm] }
    1
    (fun x => by
      rw [one_mul]
      calc ‖∑' i, y i * x i‖ ≤ ∑' i, ‖y i * x i‖ :=
            norm_tsum_le_tsum_norm (summable_bounded_mul_l1 y hy x).norm
        _ ≤ ∑' i, ‖x i‖ :=
            Summable.tsum_le_tsum (fun i => by
              rw [norm_mul]
              calc ‖y i‖ * ‖x i‖ ≤ 1 * ‖x i‖ := by gcongr; exact hy i
                _ = ‖x i‖ := one_mul _)
              (summable_bounded_mul_l1 y hy x).norm (summable_norm_lp_one x)
        _ = ‖x‖ := (l1_norm_eq_tsum x).symm)

@[simp]
theorem l1DualOfBounded_apply (y : ℕ → 𝕜) (hy : ∀ i, ‖y i‖ ≤ 1)
    (x : lp (fun _ : ℕ => 𝕜) 1) : l1DualOfBounded y hy x = ∑' i, y i * x i :=
  rfl

/-- **Pairing with a sequence bounded by one has norm at most one.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, and let $(y_i)_{i \in \mathbb{N}}$ be a sequence in $\mathbb{K}$
with $|y_i| \le 1$ for every $i$. The continuous linear functional
$x \mapsto \sum_{i=0}^{\infty} y_i x_i$ on $\ell^1(\mathbb{N}, \mathbb{K})$ has operator norm at
most $1$. -/
theorem norm_l1DualOfBounded_le (y : ℕ → 𝕜) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ‖l1DualOfBounded y hy‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [l1DualOfBounded_apply, one_mul]
    calc ‖∑' i, y i * x i‖ ≤ ∑' i, ‖y i * x i‖ :=
          norm_tsum_le_tsum_norm (summable_bounded_mul_l1 y hy x).norm
      _ ≤ ∑' i, ‖x i‖ :=
          Summable.tsum_le_tsum (fun i => by
            rw [norm_mul]
            calc ‖y i‖ * ‖x i‖ ≤ 1 * ‖x i‖ := by gcongr; exact hy i
              _ = ‖x i‖ := one_mul _)
            (summable_bounded_mul_l1 y hy x).norm (summable_norm_lp_one x)
      _ = ‖x‖ := (l1_norm_eq_tsum x).symm)

/-- **Splitting a series into a head, a middle block and a tail.** Let $\mathbb{K}$ be $\mathbb{R}$
or $\mathbb{C}$, let $h : \mathbb{N} \to \mathbb{K}$ be summable and let $a \le b$ be natural
numbers. Then $\sum_{i=0}^{\infty} h(i)$ equals
$\sum_{i < a} h(i) + \sum_{a \le i < b} h(i) + \sum_{j=0}^{\infty} h(j + b)$. -/
theorem tsum_split3 {h : ℕ → 𝕜} (hs : Summable h) {a b : ℕ} (hab : a ≤ b) :
    ∑' i, h i = (∑ i ∈ Finset.range a, h i) + (∑ i ∈ Finset.Ico a b, h i) +
      ∑' j, h (j + b) := by
  have h1 := hs.sum_add_tsum_nat_add b
  have h2 := Finset.sum_range_add_sum_Ico h hab
  rw [← h1, ← h2]

/-- **Tails of an $\ell^1$ sequence are absolutely summable.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. For every $x \in \ell^1(\mathbb{N}, \mathbb{K})$ and every $b \in \mathbb{N}$, the
series $\sum_{j=0}^{\infty} \|x_{j+b}\|$ is summable. -/
theorem summable_norm_shift (x : lp (fun _ : ℕ => 𝕜) 1) (b : ℕ) :
    Summable fun j => ‖x (j + b)‖ :=
  (summable_nat_add_iff (f := fun i => ‖x i‖) b).mpr (summable_norm_lp_one x)

/-- **Tail of the norm series of an $\ell^1$ sequence.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. For every $x \in \ell^1(\mathbb{N}, \mathbb{K})$ and every $b \in \mathbb{N}$,
$\sum_{j=0}^{\infty} \|x_{j+b}\| = \|x\| - \sum_{i < b} \|x_i\|$, where $\|x\|$ is the $\ell^1$
norm of $x$. -/
theorem tail_tsum_norm (x : lp (fun _ : ℕ => 𝕜) 1) (b : ℕ) :
    ∑' j, ‖x (j + b)‖ = ‖x‖ - ∑ i ∈ Finset.range b, ‖x i‖ := by
  have h1 := (summable_norm_lp_one x).sum_add_tsum_nat_add b
  have h2 := (l1_norm_eq_tsum x).symm
  linarith

/-- **Block index for a cutoff sequence.** Let $M : \mathbb{N} \to \mathbb{N}$ be such that
every $i \in \mathbb{N}$ satisfies $i < M(k + 1)$ for some $k$. The block index of
$i \in \mathbb{N}$ is the least $k$ with $i < M(k + 1)$.

When $M$ is monotone and $M(0) = 0$, the block index of $i$ is the unique $k$ with
$M(k) \le i < M(k + 1)$. -/
noncomputable def schurBlockOf (M' : ℕ → ℕ) (hex : ∀ i, ∃ k, i < M' (k + 1))
    (i : ℕ) : ℕ :=
  Nat.find (hex i)

/-- **An index lies in the block it is assigned to.** Let $M : \mathbb{N} \to \mathbb{N}$ satisfy
$M(0) = 0$, and suppose every $i \in \mathbb{N}$ satisfies $i < M(j + 1)$ for some $j$. For
every $i \in \mathbb{N}$, if $k$ is the block index of $i$ (the least $k$ with
$i < M(k + 1)$), then $M(k) \le i < M(k + 1)$. -/
theorem schurBlockOf_mem (M' : ℕ → ℕ) (hM'0 : M' 0 = 0)
    (hex : ∀ i, ∃ k, i < M' (k + 1)) (i : ℕ) :
    i ∈ Finset.Ico (M' (schurBlockOf M' hex i)) (M' (schurBlockOf M' hex i + 1)) := by
  rw [Finset.mem_Ico]
  refine ⟨?_, Nat.find_spec (hex i)⟩
  by_cases h0 : schurBlockOf M' hex i = 0
  · rw [h0, hM'0]
    exact Nat.zero_le _
  · have hmin := Nat.find_min (hex i) (show schurBlockOf M' hex i - 1 < schurBlockOf M' hex i by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ schurBlockOf M' hex i)] at hmin
    push Not at hmin
    exact hmin

/-- **Indices in block $k$ have block index $k$.** Let $M : \mathbb{N} \to \mathbb{N}$ be
monotone, and suppose every $i \in \mathbb{N}$ satisfies $i < M(j + 1)$ for some $j$. For all
$k, i \in \mathbb{N}$ with $M(k) \le i < M(k + 1)$, the block index of $i$ (the least $j$ with
$i < M(j + 1)$) is $k$. -/
theorem schurBlockOf_eq {M' : ℕ → ℕ} (hmono : Monotone M')
    (hex : ∀ i, ∃ k, i < M' (k + 1)) (k : ℕ)
    {i : ℕ} (hi : i ∈ Finset.Ico (M' k) (M' (k + 1))) :
    schurBlockOf M' hex i = k := by
  rw [Finset.mem_Ico] at hi
  apply le_antisymm
  · by_contra hcon
    push Not at hcon
    have hmin := Nat.find_min (hex i) hcon
    exact hmin hi.2
  · by_contra hcon
    push Not at hcon
    have hmono' : M' (schurBlockOf M' hex i + 1) ≤ M' k := hmono (by omega)
    have hspec : i < M' (schurBlockOf M' hex i + 1) := Nat.find_spec (hex i)
    omega

/-- **Conjugate-sign sequence of a block decomposition.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $(x_n)$ be a sequence in $\ell^1(\mathbb{N}, \mathbb{K})$, let
$n' : \mathbb{N} \to \mathbb{N}$, and let $M : \mathbb{N} \to \mathbb{N}$ be such that every
$i \in \mathbb{N}$ satisfies $i < M(j + 1)$ for some $j$. For $i \in \mathbb{N}$, let $k$ be
the block index of $i$ (the least $k$ with $i < M(k + 1)$) and let $v = x_{n'(k)}(i)$. The
$i$-th term $\sigma_i$ of the conjugate-sign sequence is $0$ if $v = 0$, and
$\overline{v} / |v|$ otherwise. -/
noncomputable def schurSignSeq (x : ℕ → lp (fun _ : ℕ => 𝕜) 1) (n' : ℕ → ℕ)
    (M' : ℕ → ℕ) (hex : ∀ i, ∃ k, i < M' (k + 1)) (i : ℕ) : 𝕜 :=
  if x (n' (schurBlockOf M' hex i)) i = 0 then 0
  else starRingEnd 𝕜 (x (n' (schurBlockOf M' hex i)) i) /
    (‖x (n' (schurBlockOf M' hex i)) i‖ : 𝕜)

/-- **The conjugate-sign sequence is bounded by one.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $(x_n)$ be a sequence in $\ell^1(\mathbb{N}, \mathbb{K})$, let
$n' : \mathbb{N} \to \mathbb{N}$, and let $M : \mathbb{N} \to \mathbb{N}$ be such that every
$i \in \mathbb{N}$ satisfies $i < M(j + 1)$ for some $j$. Every term $\sigma_i$ of the
conjugate-sign sequence of $(x_n)$, $n'$ and $M$ satisfies $|\sigma_i| \le 1$. -/
theorem norm_schurSignSeq_le (x : ℕ → lp (fun _ : ℕ => 𝕜) 1) (n' : ℕ → ℕ)
    (M' : ℕ → ℕ) (hex : ∀ i, ∃ k, i < M' (k + 1)) (i : ℕ) :
    ‖schurSignSeq x n' M' hex i‖ ≤ 1 := by
  by_cases hz : x (n' (schurBlockOf M' hex i)) i = 0
  · have hif : schurSignSeq x n' M' hex i = 0 := by
      simp only [schurSignSeq, hz, ite_true]
    rw [hif, norm_zero]
    exact zero_le_one
  · have hz' : (‖x (n' (schurBlockOf M' hex i)) i‖ : 𝕜) ≠ 0 := by
      rw [Ne, RCLike.ofReal_eq_zero, norm_eq_zero]
      exact hz
    have hif : schurSignSeq x n' M' hex i =
        starRingEnd 𝕜 (x (n' (schurBlockOf M' hex i)) i) /
          (‖x (n' (schurBlockOf M' hex i)) i‖ : 𝕜) := by
      simp only [schurSignSeq, hz, ite_false]
    rw [hif, norm_div, RCLike.norm_conj, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hz)]

/-- **On block $k$, the conjugate signs recover absolute values.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $(x_n)$ be a sequence in $\ell^1(\mathbb{N}, \mathbb{K})$,
let $n' : \mathbb{N} \to \mathbb{N}$, and let $M : \mathbb{N} \to \mathbb{N}$ be monotone and
such that every $i \in \mathbb{N}$ satisfies $i < M(j + 1)$ for some $j$. Let $\sigma$ be the
conjugate-sign sequence of $(x_n)$, $n'$ and $M$. For all $k, i \in \mathbb{N}$ with
$M(k) \le i < M(k + 1)$, we have $\sigma_i \, x_{n'(k)}(i) = |x_{n'(k)}(i)|$. -/
theorem schurSignSeq_mul (x : ℕ → lp (fun _ : ℕ => 𝕜) 1) (n' : ℕ → ℕ)
    (M' : ℕ → ℕ) (hmono : Monotone M') (hex : ∀ i, ∃ k, i < M' (k + 1)) (k : ℕ)
    {i : ℕ} (hi : i ∈ Finset.Ico (M' k) (M' (k + 1))) :
    schurSignSeq x n' M' hex i * x (n' k) i = (‖x (n' k) i‖ : 𝕜) := by
  have hblk : schurBlockOf M' hex i = k := schurBlockOf_eq hmono hex k hi
  by_cases hz : x (n' k) i = 0
  · have hif : schurSignSeq x n' M' hex i = 0 := by
      simp only [schurSignSeq, hblk, hz, ite_true]
    rw [hif, zero_mul]
    simp [hz]
  · have hz' : (‖x (n' k) i‖ : 𝕜) ≠ 0 := by
      rw [Ne, RCLike.ofReal_eq_zero, norm_eq_zero]
      exact hz
    have hif : schurSignSeq x n' M' hex i =
        starRingEnd 𝕜 (x (n' k) i) / (‖x (n' k) i‖ : 𝕜) := by
      simp only [schurSignSeq, hblk, hz, ite_false]
    rw [hif, div_mul_eq_mul_div, RCLike.conj_mul, pow_two,
      mul_div_cancel_right₀ _ hz']

/-- One gliding-hump step. Given previous cutoffs, choose a later index whose
term has norm at least `ε`, whose mass before the old cutoff is `< δ`, and a
new cutoff past which its remaining tail mass is `< δ`. -/
private theorem gliding_hump_step {x : ℕ → lp (fun _ : ℕ => 𝕜) 1} {ε δ : ℝ}
    (hx_coord : ∀ i, Tendsto (fun n => x n i) atTop (𝓝 0))
    (hx_freq : ∃ᶠ n in atTop, ε ≤ ‖x n‖) (hδ : 0 < δ) {n₀ M₀ : ℕ} :
    ∃ n M : ℕ, n₀ < n ∧ M₀ < M ∧
      (∑ i ∈ Finset.range M₀, ‖x n i‖ < δ) ∧
      (‖x n‖ - ∑ i ∈ Finset.range M, ‖x n i‖ < δ) ∧ ε ≤ ‖x n‖ := by
  have hcoord : ∀ i, Tendsto (fun n => ‖x n i‖) atTop (𝓝 0) := fun i =>
    tendsto_zero_iff_norm_tendsto_zero.mp (hx_coord i)
  have hhead_ev : ∀ᶠ n in atTop, ∑ i ∈ Finset.range M₀, ‖x n i‖ < δ := by
    have hsum : Tendsto (fun n => ∑ i ∈ Finset.range M₀, ‖x n i‖) atTop (𝓝 0) := by
      have h := tendsto_finsetSum (Finset.range M₀) (fun i _ => hcoord i)
      simpa using h
    exact (hsum.eventually (Iio_mem_nhds hδ)).mono fun n hn => hn
  obtain ⟨n, hn_ge, hεn, hhead_n⟩ :=
    frequently_atTop.mp (hx_freq.and_eventually hhead_ev) (n₀ + 1)
  have htail_ev : ∀ᶠ M in atTop, ‖x n‖ - ∑ i ∈ Finset.range M, ‖x n i‖ < δ := by
    have hlim : Tendsto (fun M => ∑ i ∈ Finset.range M, ‖x n i‖) atTop (𝓝 ‖x n‖) := by
      have h := (summable_norm_lp_one (x n)).hasSum.tendsto_sum_nat
      rw [← l1_norm_eq_tsum (x n)] at h
      exact h
    have hev := hlim.eventually (Ioi_mem_nhds (sub_lt_self _ hδ))
    exact hev.mono fun M hM => by linarith
  obtain ⟨A, hA⟩ := eventually_atTop.mp htail_ev
  refine ⟨n, max A (M₀ + 1), by omega, by omega, hhead_n, hA _ (le_max_left _ _), hεn⟩

/-- Schur's theorem, zero-limit form: a sequence in `ℓ¹` converging weakly
to `0` has norms converging to `0`. -/
private theorem tendsto_norm_zero_of_weak {x : ℕ → lp (fun _ : ℕ => 𝕜) 1}
    (hx : ∀ F : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] 𝕜,
      Tendsto (fun n => F (x n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
  by_contra hcon
  have hfreq : ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n in atTop, ε ≤ ‖x n‖ := by
    by_contra hnone
    push Not at hnone
    apply hcon
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev : ∀ᶠ n in atTop, ‖x n‖ < ε := hnone ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    exact ⟨N, fun n hn => by
      have h := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact h⟩
  obtain ⟨ε, hε, hfreq⟩ := hfreq
  set δ : ℝ := ε / 8 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  have hδeq : δ = ε / 8 := hδ_def
  have hx_coord : ∀ i, Tendsto (fun n => x n i) atTop (𝓝 0) := fun i => by
    exact hx (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 1 i)
  have step : ∀ p : ℕ × ℕ, ∃ q : ℕ × ℕ, p.1 < q.1 ∧ p.2 < q.2 ∧
      (∑ i ∈ Finset.range p.2, ‖x q.1 i‖ < δ) ∧
      (‖x q.1‖ - ∑ i ∈ Finset.range q.2, ‖x q.1 i‖ < δ) ∧ ε ≤ ‖x q.1‖ := by
    intro p
    obtain ⟨n, M, h1, h2, h3, h4, h5⟩ :=
      gliding_hump_step hx_coord hfreq hδ (n₀ := p.1) (M₀ := p.2)
    exact ⟨(n, M), h1, h2, h3, h4, h5⟩
  choose stepFn hstep using step
  set s : ℕ → ℕ × ℕ := fun k => (stepFn^[k]) (stepFn (0, 0)) with hs_def
  have hs_zero : s 0 = stepFn (0, 0) := by simp only [hs_def, Function.iterate_zero_apply]
  have hs_succ : ∀ k, s (k + 1) = stepFn (s k) := by
    intro k
    simp only [hs_def, Function.iterate_succ_apply']
  set n' : ℕ → ℕ := fun k => (s k).1 with hn'_def
  set M : ℕ → ℕ := fun k => (s k).2 with hM_def
  set M' : ℕ → ℕ := fun k => if k = 0 then 0 else M (k - 1) with hM'_def
  have h_n'_k : ∀ k, n' k = (s k).1 := fun k => by simp only [hn'_def]
  have hM_k : ∀ k, M k = (s k).2 := fun k => by simp only [hM_def]
  have hM'_zero : M' 0 = 0 := by simp [hM'_def]
  have hM'_succ_eq : ∀ k, M' (k + 1) = M k := by
    intro k
    simp only [hM'_def, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
  have hstep_k : ∀ k, (s k).1 < (stepFn (s k)).1 ∧ (s k).2 < (stepFn (s k)).2 ∧
      (∑ i ∈ Finset.range (s k).2, ‖x (stepFn (s k)).1 i‖ < δ) ∧
      (‖x (stepFn (s k)).1‖ - ∑ i ∈ Finset.range (stepFn (s k)).2,
        ‖x (stepFn (s k)).1 i‖ < δ) ∧
      ε ≤ ‖x (stepFn (s k)).1‖ := fun k => hstep (s k)
  have hn'_succ : ∀ k, n' k < n' (k + 1) := by
    intro k
    rw [h_n'_k k, h_n'_k (k + 1), hs_succ k]
    exact (hstep_k k).1
  have hM'_succ : ∀ k, M' k < M' (k + 1) := by
    intro k
    cases k with
    | zero =>
      rw [hM'_zero, hM'_succ_eq 0, hM_k 0, hs_zero]
      exact (hstep (0, 0)).2.1
    | succ k =>
      rw [hM'_succ_eq (k + 1), hM'_succ_eq k, hM_k (k + 1), hM_k k, hs_succ k]
      exact (hstep_k k).2.1
  have hM'_strict : StrictMono M' := strictMono_nat_of_lt_succ hM'_succ
  have hn'_strict : StrictMono n' := strictMono_nat_of_lt_succ hn'_succ
  have hM'_ge : ∀ k, k ≤ M' k := by
    intro k
    induction k with
    | zero => simp [hM'_zero]
    | succ k ih =>
      have hlt := hM'_succ k
      omega
  have hex : ∀ i, ∃ k, i < M' (k + 1) := fun i =>
    ⟨i, by have hge := hM'_ge (i + 1); omega⟩
  have hhead : ∀ k, ∑ i ∈ Finset.range (M' k), ‖x (n' k) i‖ < δ := by
    intro k
    cases k with
    | zero => rw [hM'_zero]; simpa using hδ
    | succ k =>
      rw [hM'_succ_eq k, hM_k k, h_n'_k (k + 1), hs_succ k]
      exact (hstep_k k).2.2.1
  have htail : ∀ k, ‖x (n' k)‖ - ∑ i ∈ Finset.range (M' (k + 1)), ‖x (n' k) i‖ < δ := by
    intro k
    cases k with
    | zero =>
      rw [hM'_succ_eq 0, hM_k 0, h_n'_k 0, hs_zero]
      exact (hstep (0, 0)).2.2.2.1
    | succ k =>
      rw [hM'_succ_eq (k + 1), hM_k (k + 1), h_n'_k (k + 1), hs_succ k]
      exact (hstep_k k).2.2.2.1
  have hεk : ∀ k, ε ≤ ‖x (n' k)‖ := by
    intro k
    cases k with
    | zero => rw [h_n'_k 0, hs_zero]; exact (hstep (0, 0)).2.2.2.2
    | succ k => rw [h_n'_k (k + 1), hs_succ k]; exact (hstep_k k).2.2.2.2
  have hblock : ∀ k, ε - 2 * δ ≤
      ∑ i ∈ Finset.Ico (M' k) (M' (k + 1)), ‖x (n' k) i‖ := by
    intro k
    have hsum := Finset.sum_range_add_sum_Ico (fun i => ‖x (n' k) i‖)
      (hM'_strict.monotone (Nat.le_succ k))
    have h1 := hhead k
    have h2 := htail k
    have h3 := hεk k
    linarith
  have hy : ∀ i, ‖schurSignSeq x n' M' hex i‖ ≤ 1 :=
    fun i => norm_schurSignSeq_le x n' M' hex i
  have hF := hx (l1DualOfBounded (schurSignSeq x n' M' hex) hy)
  have hsub : Tendsto
      (fun k => l1DualOfBounded (schurSignSeq x n' M' hex) hy (x (n' k)))
      atTop (𝓝 0) :=
    hF.comp hn'_strict.tendsto_atTop
  have hlower : ∀ k, ε / 2 ≤
      ‖l1DualOfBounded (schurSignSeq x n' M' hex) hy (x (n' k))‖ := by
    intro k
    rw [l1DualOfBounded_apply]
    have hsplit := tsum_split3 (summable_bounded_mul_l1 (schurSignSeq x n' M' hex) hy
      (x (n' k))) (hM'_strict.monotone (Nat.le_succ k))
    have hhead_norm : ‖∑ i ∈ Finset.range (M' k),
        schurSignSeq x n' M' hex i * x (n' k) i‖ ≤ δ := by
      calc _ ≤ ∑ i ∈ Finset.range (M' k),
            ‖schurSignSeq x n' M' hex i * x (n' k) i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (M' k), ‖x (n' k) i‖ := Finset.sum_le_sum fun i _ => by
              rw [norm_mul]
              calc ‖schurSignSeq x n' M' hex i‖ * ‖x (n' k) i‖ ≤
                    1 * ‖x (n' k) i‖ := by gcongr; exact hy i
                _ = ‖x (n' k) i‖ := one_mul _
        _ ≤ δ := (hhead k).le
    have hblock_norm : ε - 2 * δ ≤ ‖∑ i ∈ Finset.Ico (M' k) (M' (k + 1)),
        schurSignSeq x n' M' hex i * x (n' k) i‖ := by
      have hre : RCLike.re (∑ i ∈ Finset.Ico (M' k) (M' (k + 1)),
          schurSignSeq x n' M' hex i * x (n' k) i) =
          ∑ i ∈ Finset.Ico (M' k) (M' (k + 1)), ‖x (n' k) i‖ := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i hi => by
          rw [schurSignSeq_mul x n' M' hM'_strict.monotone hex k hi,
            RCLike.ofReal_re]
      calc ε - 2 * δ ≤ RCLike.re (∑ i ∈ Finset.Ico (M' k) (M' (k + 1)),
            schurSignSeq x n' M' hex i * x (n' k) i) := by
            rw [hre]; exact hblock k
        _ ≤ ‖∑ i ∈ Finset.Ico (M' k) (M' (k + 1)),
            schurSignSeq x n' M' hex i * x (n' k) i‖ := RCLike.re_le_norm _
    have htail_norm : ‖∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
        x (n' k) (j + M' (k + 1))‖ ≤ δ := by
      have htail_summ0 : Summable fun j =>
          schurSignSeq x n' M' hex (j + M' (k + 1)) * x (n' k) (j + M' (k + 1)) := by
        apply Summable.of_norm_bounded (summable_norm_shift (x (n' k)) (M' (k + 1)))
        intro j
        rw [norm_mul]
        calc ‖schurSignSeq x n' M' hex (j + M' (k + 1))‖ * ‖x (n' k) (j + M' (k + 1))‖ ≤
              1 * ‖x (n' k) (j + M' (k + 1))‖ := by gcongr; exact hy _
          _ = ‖x (n' k) (j + M' (k + 1))‖ := one_mul _
      have htail_summ : Summable fun j =>
          ‖schurSignSeq x n' M' hex (j + M' (k + 1)) * x (n' k) (j + M' (k + 1))‖ :=
        htail_summ0.norm
      calc _ ≤ ∑' j, ‖schurSignSeq x n' M' hex (j + M' (k + 1)) *
            x (n' k) (j + M' (k + 1))‖ :=
            norm_tsum_le_tsum_norm htail_summ
        _ ≤ ∑' j, ‖x (n' k) (j + M' (k + 1))‖ :=
            Summable.tsum_le_tsum (fun j => by
              rw [norm_mul]
              calc ‖schurSignSeq x n' M' hex (j + M' (k + 1))‖ *
                    ‖x (n' k) (j + M' (k + 1))‖ ≤
                    1 * ‖x (n' k) (j + M' (k + 1))‖ := by gcongr; exact hy _
                _ = ‖x (n' k) (j + M' (k + 1))‖ := one_mul _)
              htail_summ
              (summable_norm_shift (x (n' k)) (M' (k + 1)))
        _ = ‖x (n' k)‖ - ∑ i ∈ Finset.range (M' (k + 1)), ‖x (n' k) i‖ :=
            tail_tsum_norm (x (n' k)) (M' (k + 1))
        _ ≤ δ := (htail k).le
    have htri : ‖∑ i ∈ Finset.Ico (M' k) (M' (k + 1)),
        schurSignSeq x n' M' hex i * x (n' k) i‖ ≤
        ‖∑' i, schurSignSeq x n' M' hex i * x (n' k) i‖ +
          ‖∑ i ∈ Finset.range (M' k), schurSignSeq x n' M' hex i * x (n' k) i‖ +
          ‖∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
            x (n' k) (j + M' (k + 1))‖ := by
      have hBlock_eq : (∑ i ∈ Finset.Ico (M' k) (M' (k + 1)),
          schurSignSeq x n' M' hex i * x (n' k) i) =
          (∑' i, schurSignSeq x n' M' hex i * x (n' k) i) -
            (∑ i ∈ Finset.range (M' k), schurSignSeq x n' M' hex i * x (n' k) i) -
            (∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
              x (n' k) (j + M' (k + 1))) := by
        rw [hsplit, add_assoc, add_sub_cancel_left, add_sub_cancel_right]
      calc ‖∑ i ∈ Finset.Ico (M' k) (M' (k + 1)),
            schurSignSeq x n' M' hex i * x (n' k) i‖ =
            ‖(∑' i, schurSignSeq x n' M' hex i * x (n' k) i) -
              (∑ i ∈ Finset.range (M' k), schurSignSeq x n' M' hex i * x (n' k) i) -
              (∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
                x (n' k) (j + M' (k + 1)))‖ := by rw [hBlock_eq]
        _ ≤ ‖(∑' i, schurSignSeq x n' M' hex i * x (n' k) i) -
              (∑ i ∈ Finset.range (M' k), schurSignSeq x n' M' hex i * x (n' k) i)‖ +
              ‖∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
                x (n' k) (j + M' (k + 1))‖ := norm_sub_le _ _
        _ ≤ (‖∑' i, schurSignSeq x n' M' hex i * x (n' k) i‖ +
              ‖∑ i ∈ Finset.range (M' k), schurSignSeq x n' M' hex i * x (n' k) i‖) +
              ‖∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
                x (n' k) (j + M' (k + 1))‖ := by
            gcongr
            exact norm_sub_le _ _
        _ = ‖∑' i, schurSignSeq x n' M' hex i * x (n' k) i‖ +
              ‖∑ i ∈ Finset.range (M' k), schurSignSeq x n' M' hex i * x (n' k) i‖ +
              ‖∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
                x (n' k) (j + M' (k + 1))‖ := by rw [add_assoc]
    have hε2 : (ε - 2 * δ) - δ - δ = ε / 2 := by rw [hδeq]; ring
    have hstep4 : (‖∑ i ∈ Finset.Ico (M' k) (M' (k + 1)),
          schurSignSeq x n' M' hex i * x (n' k) i‖ -
          ‖∑ i ∈ Finset.range (M' k), schurSignSeq x n' M' hex i * x (n' k) i‖) -
          ‖∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
            x (n' k) (j + M' (k + 1))‖ ≤
        ‖∑' i, schurSignSeq x n' M' hex i * x (n' k) i‖ := by
      rw [sub_le_iff_le_add, sub_le_iff_le_add]
      calc ‖∑ i ∈ Finset.Ico (M' k) (M' (k + 1)),
            schurSignSeq x n' M' hex i * x (n' k) i‖ ≤
            ‖∑' i, schurSignSeq x n' M' hex i * x (n' k) i‖ +
              ‖∑ i ∈ Finset.range (M' k), schurSignSeq x n' M' hex i * x (n' k) i‖ +
              ‖∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
                x (n' k) (j + M' (k + 1))‖ := htri
        _ = (‖∑' i, schurSignSeq x n' M' hex i * x (n' k) i‖ +
              ‖∑' j, schurSignSeq x n' M' hex (j + M' (k + 1)) *
                x (n' k) (j + M' (k + 1))‖) +
              ‖∑ i ∈ Finset.range (M' k), schurSignSeq x n' M' hex i * x (n' k) i‖ := by
            rw [add_right_comm]
    have hfinal : (ε - 2 * δ) - δ - δ ≤
        ‖∑' i, schurSignSeq x n' M' hex i * x (n' k) i‖ := by
      refine le_trans ?_ hstep4
      refine le_trans ?_ (sub_le_sub_left htail_norm _)
      refine le_trans ?_
        (sub_le_sub_right (sub_le_sub_left hhead_norm _) δ)
      exact sub_le_sub_right (sub_le_sub_right hblock_norm δ) δ
    rw [hε2] at hfinal
    exact hfinal
  have h0 : Tendsto
      (fun k => ‖l1DualOfBounded (schurSignSeq x n' M' hex) hy (x (n' k))‖)
      atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hsub
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (h0.eventually (Iio_mem_nhds (show 0 < ε / 2 by linarith)))
  have hlt : ‖l1DualOfBounded (schurSignSeq x n' M' hex) hy (x (n' K))‖ < ε / 2 :=
    hK K (le_refl K)
  have hlow := hlower K
  exact absurd hlt (not_lt_of_ge hlow)

/-- **Schur's theorem.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $(x_n)$ be a sequence
in $\ell^1(\mathbb{N}, \mathbb{K})$ and let $x_0 \in \ell^1(\mathbb{N}, \mathbb{K})$. If
$F(x_n) \to F(x_0)$ for every continuous linear functional $F$ on $\ell^1(\mathbb{N}, \mathbb{K})$,
that is, if $(x_n)$ converges weakly to $x_0$, then $x_n \to x_0$ in the $\ell^1$ norm. -/
theorem schur_tendsto_of_weak_tendsto {x : ℕ → lp (fun _ : ℕ => 𝕜) 1}
    {x₀ : lp (fun _ : ℕ => 𝕜) 1}
    (hx : ∀ F : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] 𝕜,
      Tendsto (fun n => F (x n)) atTop (𝓝 (F x₀))) :
    Tendsto x atTop (𝓝 x₀) := by
  have h0 := tendsto_norm_zero_of_weak (𝕜 := 𝕜) (x := fun n => x n - x₀) (by
    intro F
    have h := hx F
    have hsub : Tendsto (fun n => F (x n) - F x₀) atTop (𝓝 (F x₀ - F x₀)) :=
      Filter.Tendsto.sub h tendsto_const_nhds
    simpa using hsub)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact h0

/-- **Schur's theorem, norm form.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let
$(x_n)$ be a sequence in $\ell^1(\mathbb{N}, \mathbb{K})$, and let
$x \in \ell^1(\mathbb{N}, \mathbb{K})$. If $F(x_n) \to F(x)$ as $n \to \infty$ for every
continuous linear functional $F : \ell^1(\mathbb{N}, \mathbb{K}) \to \mathbb{K}$, then
$\|x_n - x\| \to 0$ as $n \to \infty$. -/
theorem schur_tendsto_norm_sub_of_weak_tendsto {x : ℕ → lp (fun _ : ℕ => 𝕜) 1}
    {x₀ : lp (fun _ : ℕ => 𝕜) 1}
    (hx : ∀ F : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] 𝕜,
      Tendsto (fun n => F (x n)) atTop (𝓝 (F x₀))) :
    Tendsto (fun n => ‖x n - x₀‖) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp (schur_tendsto_of_weak_tendsto hx)

end MathlibExt.Analysis.FunctionalAnalysis.SchurL1
