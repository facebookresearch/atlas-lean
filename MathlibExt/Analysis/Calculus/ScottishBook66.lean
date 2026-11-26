/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Scottish Book Problem 66

We adapt the disjoint-strip construction of Mykhaylyuk and Plichko, Theorem 3.2
([arXiv:1508.06909](https://arxiv.org/abs/1508.06909v2)). The strips here lie in the first
coordinate, so the derivative that jumps across strips is the derivative in the second
coordinate. We use two bumps per strip, with sine and cosine oscillations, so that for every
second coordinate at least one of the two bump centers witnesses the jump. The construction
is on all of `ℝ × ℝ`; only the set used to contradict the almost-everywhere claim is
restricted to the open unit square.

The claim retains its original `Set.Ioo (0, 0) (1, 1)` restriction in the product order
for definitional compatibility. This interval includes some boundary points, but the
boundary lies on four Lebesgue-null coordinate lines. The regression proves that its
restricted measure agrees with the restriction to the product of the two open intervals.
-/

namespace MathlibExt.Analysis.Calculus.ScottishBook66Wanted

open Set Metric MeasureTheory Filter
open scoped Topology

@[expose] public section

/-- **Mazur's mixed partial derivatives claim.** This is the following statement, the claim of
Mazur's Problem 66 from the Scottish Book. Let $Q = (0, 1) \times (0, 1)$ be the open unit square.
For every function $f : \mathbb{R}^2 \to \mathbb{R}$ such that, at every point $(x, y) \in Q$, the
functions $s \mapsto f(s, y)$ and $s \mapsto f(x, s)$ are differentiable at $x$ and at $y$
respectively, and their derivatives $\partial_x f(\cdot, y)$ and $\partial_y f(x, \cdot)$ are
again differentiable at $x$ and at $y$ respectively, the mixed partial derivative
$\partial_x \partial_y f$ exists at almost every point of $Q$ for Lebesgue measure: for almost
every $(x, y) \in Q$, the function $s \mapsto \partial_y f(s, y)$ is differentiable at $x$.

Mazur asked whether a function with first partial derivatives and both pure second partial
derivatives must have its mixed second partial derivatives almost everywhere; the claim asks this
only for $\partial_x \partial_y f$. -/
def ScottishBookProblem66Claim : Prop :=
  ∀ f : ℝ × ℝ → ℝ,
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun x' => f (x', y)) x) →
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun y' => f (x, y')) y) →
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (deriv (fun x' => f (x', y))) x) →
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (deriv (fun y' => f (x, y'))) y) →
    ∀ᵐ p ∂(volume.restrict (Set.Ioo (0, 0) (1, 1) :
      Set (ℝ × ℝ))),
      DifferentiableAt ℝ (fun x' => deriv (fun y' => f (x', y')) p.2)
        p.1

end

-- Construct disjoint strips of small total length around a dense set.
private lemma exists_next_strip (q w : ℝ) (hw : 0 < w) (K : Set ℝ) (hK : IsCompact K) :
    ∃ c r : ℝ, 0 < r ∧ r ≤ w ∧ Disjoint (closedBall c r) K ∧ q ∈ K ∪ closedBall c r := by
  classical
  have hpick : ∃ c : ℝ, c ∉ K ∧ (q ∈ K ∨ q = c) := by
    by_cases hq : q ∈ K
    · obtain ⟨M, hM⟩ := hK.bddAbove
      obtain ⟨c, hc⟩ := exists_gt M
      exact ⟨c, fun h ↦ (not_le_of_gt hc) (hM h), Or.inl hq⟩
    · exact ⟨q, hq, Or.inr rfl⟩
  obtain ⟨c, hc, hq⟩ := hpick
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl c hc
  have hhalf : 0 < δ / 2 := half_pos hδ
  refine ⟨c, min (δ / 2) w, lt_min hhalf hw, min_le_right _ _, ?_, ?_⟩
  · refine Set.disjoint_left.mpr fun x hx ↦ hsub (mem_ball.mpr ?_)
    exact (mem_closedBall.mp hx).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ))
  · rcases hq with hq | rfl
    · exact Or.inl hq
    · exact Or.inr (mem_closedBall_self (lt_min hhalf hw).le)

private lemma exists_strips :
    ∃ (c r : ℕ → ℝ) (B : Set ℝ), (∀ n, 0 < r n) ∧
      Pairwise (fun i j ↦ Disjoint (ball (c i) (r i)) (ball (c j) (r j))) ∧
      MeasurableSet B ∧ B ⊆ Ioo (0 : ℝ) 1 ∧ volume B ≠ 0 ∧
      (∀ x ∈ B, ∀ n, x ∉ ball (c n) (r n)) ∧
      (∀ x ∈ B, ∀ ε > 0, ∃ n, dist (c n) x + r n < ε) := by
  classical
  let q : ℕ → ℝ := fun n ↦ ((Encodable.decode (α := ℚ) n).getD 0 : ℚ)
  let w : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n / 8
  have hstep (n : ℕ) (K : {s : Set ℝ // IsCompact s}) :
      ∃ c r : ℝ, 0 < r ∧ r ≤ w n ∧ Disjoint (closedBall c r) K.1 ∧
        q n ∈ K.1 ∪ closedBall c r :=
    exists_next_strip (q n) (w n) (by dsimp [w]; positivity) K.1 K.2
  choose center radius hpos hbound hdisj hcover using hstep
  let stage : ℕ → {s : Set ℝ // IsCompact s} :=
    Nat.rec ⟨∅, isCompact_empty⟩ fun n K ↦
      ⟨K.1 ∪ closedBall (center n K) (radius n K), K.2.union (isCompact_closedBall _ _)⟩
  let c : ℕ → ℝ := fun n ↦ center n (stage n)
  let r : ℕ → ℝ := fun n ↦ radius n (stage n)
  let C : ℕ → Set ℝ := fun n ↦ closedBall (c n) (r n)
  let U : Set ℝ := ⋃ n, C n
  have hstage (n : ℕ) : (stage (n + 1)).1 = (stage n).1 ∪ C n := rfl
  have hmono : Monotone (fun n ↦ (stage n).1) :=
    monotone_nat_of_le_succ fun n ↦ by rw [hstage]; exact subset_union_left
  have hC (n : ℕ) : C n ⊆ (stage (n + 1)).1 := by
    rw [hstage]
    exact subset_union_right
  have hCU (n : ℕ) : C n ⊆ U := subset_iUnion C n
  have hstageU (n : ℕ) : (stage n).1 ⊆ U := by
    induction n with
    | zero => exact empty_subset U
    | succ n ih =>
      rw [hstage]
      exact union_subset ih (hCU n)
  have hrat (a : ℚ) : (a : ℝ) ∈ U := by
    have hq : q (Encodable.encode a) = a := by simp [q, Encodable.encodek]
    rw [← hq]
    apply hstageU (Encodable.encode a + 1)
    rw [hstage]
    exact hcover (Encodable.encode a) (stage (Encodable.encode a))
  have hd (i j : ℕ) (hij : i < j) : Disjoint (C i) (C j) :=
    (hdisj j (stage j)).symm.mono_left ((hC i).trans (hmono (Nat.succ_le_of_lt hij)))
  let B := Ioo (0 : ℝ) 1 \ U
  refine ⟨c, r, B, fun n ↦ hpos n (stage n), ?_, ?_, sdiff_subset, ?_, ?_, ?_⟩
  · intro i j hij
    have hcdisj : Disjoint (C i) (C j) := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hd i j h
      · exact (hd j i h).symm
    exact hcdisj.mono ball_subset_closedBall ball_subset_closedBall
  · exact measurableSet_Ioo.diff (MeasurableSet.iUnion fun _ ↦ isClosed_closedBall.measurableSet)
  · have hnonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have hltOne : (1 / 2 : ℝ) < 1 := by norm_num
    have hsum := summable_geometric_of_lt_one hnonneg hltOne
    have hvolume : volume U ≤ ENNReal.ofReal (1 / 2) := calc
      volume U ≤ ∑' n, volume (C n) := measure_iUnion_le C
      _ ≤ ∑' n, ENNReal.ofReal ((1 / 2 : ℝ) ^ n / 4) := by
        apply tsum_le_tsum
        intro n
        change volume (closedBall (c n) (r n)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n / 4)
        rw [Real.volume_closedBall]
        apply ENNReal.ofReal_le_ofReal
        have hn : r n ≤ (1 / 2 : ℝ) ^ n / 8 := hbound n (stage n)
        linarith only [hn]
      _ = ENNReal.ofReal (1 / 2) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) (hsum.div_const 4),
          tsum_div_const, tsum_geometric_of_lt_one hnonneg hltOne]
        norm_num
    intro hzero
    have hsub : Ioo (0 : ℝ) 1 ⊆ B ∪ U := by
      intro x hx
      by_cases hu : x ∈ U
      · exact Or.inr hu
      · exact Or.inl ⟨hx, hu⟩
    have htotal := (measure_mono (μ := volume) hsub).trans (measure_union_le B U)
    rw [hzero, zero_add, Real.volume_Ioo, sub_zero] at htotal
    have hlt : ENNReal.ofReal (1 / 2) < ENNReal.ofReal 1 :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
    exact (not_le_of_gt hlt) (htotal.trans hvolume)
  · intro x hx n hn
    exact hx.2 (hCU n (ball_subset_closedBall hn))
  · intro x hx ε hε
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const hε)
    have hxN : x ∉ (stage N).1 := fun h ↦ hx.2 (hstageU N h)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (stage N).2.isClosed.isOpen_compl x hxN
    obtain ⟨a, ha⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_dist_lt x
      (lt_min hδ (half_pos hε))
    have haN : (a : ℝ) ∉ (stage N).1 := by
      apply hball
      rw [mem_ball, dist_comm]
      exact ha.trans_le (min_le_left _ _)
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hrat a)
    have hNn : N ≤ n := by
      by_contra! h
      exact haN (hmono (Nat.succ_le_of_lt h) (hC n hn))
    have hwidth : r n ≤ (1 / 2 : ℝ) ^ n / 8 := hbound n (stage n)
    have hrad : r n < ε / 8 := (hwidth.trans_lt (div_lt_div_of_pos_right (hN n hNn) (by norm_num)))
    have hac : dist (a : ℝ) (c n) ≤ r n := mem_closedBall.mp hn
    have hax : dist x (a : ℝ) < ε / 2 := ha.trans_le (min_le_right _ _)
    have htri : dist (c n) x ≤ dist (a : ℝ) (c n) + dist x (a : ℝ) := by
      rw [dist_comm x (a : ℝ)]
      exact dist_triangle_left _ _ _
    exact ⟨n, by linarith⟩


-- Each strip contains two disjoint bumps with distinct phase samples.
private lemma exists_bump_pair (c r : ℝ) (hr : 0 < r) :
    ∃ u v : ℝ → ℝ, ContDiff ℝ 2 u ∧ ContDiff ℝ 2 v ∧
      HasCompactSupport u ∧ HasCompactSupport v ∧
      Function.support u ⊆ ball c r ∧ Function.support v ⊆ ball c r ∧
      ∃ a ∈ ball c r, ∃ b ∈ ball c r, u a = 1 ∧ v a = 0 ∧ u b = 0 ∧ v b = 1 := by
  let a := c - r / 2
  let b := c + r / 2
  let g (z : ℝ) : ContDiffBump z := ⟨r / 8, r / 4, by positivity, by linarith⟩
  have ha : dist a c = r / 2 := by
    rw [Real.dist_eq, show a - c = -(r / 2) by dsimp [a]; ring, abs_neg, abs_of_pos (half_pos hr)]
  have hb : dist b c = r / 2 := by
    rw [Real.dist_eq, show b - c = r / 2 by dsimp [b]; ring, abs_of_pos (half_pos hr)]
  have hab : dist a b = r := by
    rw [Real.dist_eq, show a - b = -r by dsimp [a, b]; ring, abs_neg, abs_of_pos hr]
  have hsub (z : ℝ) (hz : dist z c = r / 2) : Function.support (g z) ⊆ ball c r := by
    rw [(g z).support_eq]
    intro x hx
    have h := dist_triangle x z c
    rw [hz] at h
    have hx' : dist x z < r / 4 := mem_ball.mp hx
    exact mem_ball.mpr (by linarith)
  refine ⟨g a, g b, (g a).contDiff, (g b).contDiff, (g a).hasCompactSupport,
    (g b).hasCompactSupport, hsub a ha, hsub b hb, a, ?_, b, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_ball.mpr (ha.trans_lt (half_lt_self hr))
  · exact mem_ball.mpr (hb.trans_lt (half_lt_self hr))
  · exact (g a).one_of_mem_closedBall (mem_closedBall_self (g a).rIn_pos.le)
  · exact (g b).zero_of_le_dist (by change r / 4 ≤ dist a b; rw [hab]; linarith)
  · exact (g a).zero_of_le_dist (by change r / 4 ≤ dist b a; rw [dist_comm b, hab]; linarith)
  · exact (g b).one_of_mem_closedBall (mem_closedBall_self (g b).rIn_pos.le)

private lemma exists_deriv_bounds {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    ∃ M > 0, ∀ x, |g x| ≤ M ∧ |deriv g x| ≤ M ∧ |deriv (deriv g) x| ≤ M := by
  obtain ⟨C₀, h₀⟩ := hc.exists_bound_of_continuous hg.continuous
  obtain ⟨C₁, h₁⟩ := hc.deriv.exists_bound_of_continuous (hg.continuous_deriv (by decide))
  have hd : ContDiff ℝ 1 (deriv g) := hg.deriv'
  obtain ⟨C₂, h₂⟩ := hc.deriv.deriv.exists_bound_of_continuous hd.continuous_deriv_one
  simp only [Real.norm_eq_abs] at h₀ h₁ h₂
  refine ⟨max 1 (max C₀ (max C₁ C₂)), zero_lt_one.trans_le (le_max_left ..), fun x ↦ ?_⟩
  have hmax := le_max_right (1 : ℝ) (max C₀ (max C₁ C₂))
  exact ⟨(h₀ x).trans ((le_max_left ..).trans hmax),
    (h₁ x).trans ((le_max_left ..).trans ((le_max_right ..).trans hmax)),
    (h₂ x).trans ((le_max_right ..).trans ((le_max_right ..).trans hmax))⟩

private noncomputable def wave (u v : ℝ → ℝ) (k x y : ℝ) : ℝ :=
  u x * (Real.sin (k * y) / k) + v x * (-Real.cos (k * y) / k)

private lemma norm_wave_le {u v : ℝ → ℝ} {k A B x : ℝ} (y : ℝ)
    (hk : 0 < k) (hu : |u x| ≤ A) (hv : |v x| ≤ B) :
    ‖wave u v k x y‖ ≤ (A + B) / k := by
  rw [Real.norm_eq_abs, wave]
  refine (abs_add_le ..).trans ?_
  simp only [abs_mul, abs_div, abs_neg, abs_of_pos hk]
  have hsin := div_le_div_of_nonneg_right (Real.abs_sin_le_one (k * y)) hk.le
  have hcos := div_le_div_of_nonneg_right (Real.abs_cos_le_one (k * y)) hk.le
  rw [add_div, ← mul_one_div A, ← mul_one_div B]
  gcongr <;> first | exact (abs_nonneg _).trans hu | exact (abs_nonneg _).trans hv

private lemma hasDerivAt_wave_x {u v : ℝ → ℝ} {x : ℝ} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (k y : ℝ) :
    HasDerivAt (fun t ↦ wave u v k t y) (wave (deriv u) (deriv v) k x y) x :=
  (hu.hasDerivAt.mul_const _).add (hv.hasDerivAt.mul_const _)

private lemma hasDerivAt_wave_y (u v : ℝ → ℝ) {k : ℝ} (hk : k ≠ 0) (x y : ℝ) :
    HasDerivAt (wave u v k x) (u x * Real.cos (k * y) + v x * Real.sin (k * y)) y := by
  have hk' : HasDerivAt (fun t : ℝ ↦ k * t) k y := by
    simpa only [id, mul_one] using (hasDerivAt_id y).const_mul k
  have hs := (hk'.sin.div_const k).const_mul (u x)
  have hc := (hk'.cos.neg.div_const k).const_mul (v x)
  change HasDerivAt (fun t ↦ u x * (Real.sin (k * t) / k) + v x * (-Real.cos (k * t) / k)) _ y
  simpa only [Pi.add_def, Pi.neg_apply, neg_mul, neg_neg, mul_div_cancel_right₀ _ hk]
    using hs.add hc

private lemma contDiff_wave_y (u v : ℝ → ℝ) (k x : ℝ) : ContDiff ℝ 2 (wave u v k x) := by
  unfold wave
  fun_prop

private lemma exists_wave_frequency {u v : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v) {w : ℝ} (hw : 0 < w) :
    ∃ k > 0, ∀ x y, ‖wave u v k x y‖ ≤ w ∧
      ‖wave (deriv u) (deriv v) k x y‖ ≤ w ∧
      ‖wave (deriv (deriv u)) (deriv (deriv v)) k x y‖ ≤ w := by
  obtain ⟨A, hA, hbA⟩ := exists_deriv_bounds hu huc
  obtain ⟨B, hB, hbB⟩ := exists_deriv_bounds hv hvc
  let k := (A + B) / w
  have hk : 0 < k := div_pos (add_pos hA hB) hw
  have heq : (A + B) / k = w := by
    rw [show k = (A + B) / w from rfl, div_div_eq_mul_div, mul_comm, mul_div_cancel_right₀]
    exact (add_pos hA hB).ne'
  refine ⟨k, hk, fun x y ↦ ?_⟩
  rw [← heq]
  exact ⟨norm_wave_le y hk (hbA x).1 (hbB x).1,
    norm_wave_le y hk (hbA x).2.1 (hbB x).2.1,
    norm_wave_le y hk (hbA x).2.2 (hbB x).2.2⟩

private noncomputable def waveSeries (u v : ℕ → ℝ → ℝ) (k : ℕ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑' n, wave (u n) (v n) (k n) p.1 p.2

-- The amplitudes bound the series of the first two strip-direction derivatives uniformly.
private lemma waveSeries_twice_x {u v : ℕ → ℝ → ℝ} {k w : ℕ → ℝ} (hw : Summable w)
    (hu : ∀ n, ContDiff ℝ 2 (u n)) (hv : ∀ n, ContDiff ℝ 2 (v n))
    (hb : ∀ n x y, ‖wave (u n) (v n) (k n) x y‖ ≤ w n ∧
      ‖wave (deriv (u n)) (deriv (v n)) (k n) x y‖ ≤ w n ∧
      ‖wave (deriv (deriv (u n))) (deriv (deriv (v n))) (k n) x y‖ ≤ w n)
    (y : ℝ) : Differentiable ℝ (fun x ↦ waveSeries u v k (x, y)) ∧
      Differentiable ℝ (deriv (fun x ↦ waveSeries u v k (x, y))) := by
  have hd (x : ℝ) := hasDerivAt_tsum hw
    (fun n t ↦ hasDerivAt_wave_x ((hu n).differentiable (by decide) t)
      ((hv n).differentiable (by decide) t) (k n) y)
    (fun n t ↦ (hb n t y).2.1)
    (hw.of_norm_bounded (fun n ↦ (hb n 0 y).1)) x
  refine ⟨fun x ↦ (hd x).differentiableAt, ?_⟩
  have hderiv : deriv (fun x ↦ waveSeries u v k (x, y)) =
      fun t ↦ ∑' n, wave (deriv (u n)) (deriv (v n)) (k n) t y :=
    funext fun x ↦ (hd x).deriv
  rw [hderiv]
  exact fun x ↦ (hasDerivAt_tsum hw
    (fun n t ↦ hasDerivAt_wave_x ((hu n).differentiable_deriv_two t)
      ((hv n).differentiable_deriv_two t) (k n) y)
    (fun n t ↦ (hb n t y).2.2)
    (hw.of_norm_bounded (fun n ↦ (hb n 0 y).2.1)) x).differentiableAt

private lemma waveSeries_eq_wave {u v : ℕ → ℝ → ℝ} {k : ℕ → ℝ} {S : ℕ → Set ℝ}
    (hu : ∀ n, Function.support (u n) ⊆ S n) (hv : ∀ n, Function.support (v n) ⊆ S n)
    (hd : Pairwise (fun m n ↦ Disjoint (S m) (S n))) {n : ℕ} {x : ℝ} (hx : x ∈ S n) :
    (fun y ↦ waveSeries u v k (x, y)) = wave (u n) (v n) (k n) x := by
  funext y
  unfold waveSeries
  apply tsum_eq_single n
  intro m hm
  have hx' : x ∉ S m := fun h ↦ Set.disjoint_left.mp (hd hm) h hx
  have h₁ := Function.notMem_support.mp (fun h ↦ hx' (hu m h))
  have h₂ := Function.notMem_support.mp (fun h ↦ hx' (hv m h))
  simp [wave, h₁, h₂]

private lemma waveSeries_eq_zero {u v : ℕ → ℝ → ℝ} {k : ℕ → ℝ} {S : ℕ → Set ℝ}
    (hu : ∀ n, Function.support (u n) ⊆ S n) (hv : ∀ n, Function.support (v n) ⊆ S n)
    {x : ℝ} (hx : ∀ n, x ∉ S n) : (fun y ↦ waveSeries u v k (x, y)) = fun _ ↦ 0 := by
  funext y
  have hz (n : ℕ) : wave (u n) (v n) (k n) x y = 0 := by
    have h₁ := Function.notMem_support.mp (fun h ↦ hx n (hu n h))
    have h₂ := Function.notMem_support.mp (fun h ↦ hx n (hv n h))
    simp [wave, h₁, h₂]
  simp only [waveSeries, hz, tsum_zero]

private lemma waveSeries_twice_y {u v : ℕ → ℝ → ℝ} {k : ℕ → ℝ} {S : ℕ → Set ℝ}
    (hu : ∀ n, Function.support (u n) ⊆ S n) (hv : ∀ n, Function.support (v n) ⊆ S n)
    (hd : Pairwise (fun m n ↦ Disjoint (S m) (S n))) (x : ℝ) :
    Differentiable ℝ (fun y ↦ waveSeries u v k (x, y)) ∧
      Differentiable ℝ (deriv (fun y ↦ waveSeries u v k (x, y))) := by
  by_cases! h : ∃ n, x ∈ S n
  · obtain ⟨n, hn⟩ := h
    rw [waveSeries_eq_wave hu hv hd hn]
    exact ⟨(contDiff_wave_y ..).differentiable (by decide),
      (contDiff_wave_y ..).differentiable_deriv_two⟩
  · rw [waveSeries_eq_zero hu hv h]
    exact ⟨differentiable_const _, by simpa only [deriv_const'] using differentiable_const (0 : ℝ)⟩

private lemma abs_cos_or_abs_sin (z : ℝ) : 1 / 2 ≤ |Real.cos z| ∨ 1 / 2 ≤ |Real.sin z| := by
  by_contra! h
  have hcos := mul_nonneg (sub_nonneg.mpr h.1.le) (abs_nonneg (Real.cos z))
  have hsin := mul_nonneg (sub_nonneg.mpr h.2.le) (abs_nonneg (Real.sin z))
  have hc := Real.sin_sq_add_cos_sq z
  rw [← sq_abs (Real.sin z), ← sq_abs (Real.cos z)] at hc
  nlinarith only [hc, h.1, h.2, hcos, hsin]

public section

/--
**Mazur's Problem 66 has a negative answer.** Mazur's mixed partial derivatives claim is false:
there is a function $f : \mathbb{R}^2 \to \mathbb{R}$ such that, at every point $(x, y)$ of the
open unit square $Q = (0, 1) \times (0, 1)$, the functions $s \mapsto f(s, y)$ and
$s \mapsto f(x, s)$ are differentiable at $x$ and at $y$ respectively, and their derivatives
$\partial_x f(\cdot, y)$ and $\partial_y f(x, \cdot)$ are again differentiable at $x$ and at $y$
respectively, but the set of points $(x, y) \in Q$ at which $s \mapsto \partial_y f(s, y)$ is not
differentiable at $x$ is not a Lebesgue null set.

Source: S. Mazur, Problem 66 of the
Scottish Book; refuted by V. Mykhaylyuk and A. Plichko, who construct a
separately twice differentiable function on `[0, 1]²` and a set of
positive measure on which the mixed derivative `f_xy` does not exist
("On a Mazur problem from 'The Scottish Book' concerning second partial
derivatives", Colloq. Math. 141 (2015), 175–181, arXiv:1508.06909).
-/
theorem mazur66_refuted : ¬ ScottishBookProblem66Claim := by
  classical
  intro hclaim
  obtain ⟨c, r, B, hr, hd, hB, hBI, hBpos, hout, hnear⟩ := exists_strips
  choose u v hu hv huc hvc hus hvs a ha b hb hua hva hub hvb using
    fun n ↦ exists_bump_pair (c n) (r n) (hr n)
  let w (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
  have hw : Summable w := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  choose k hk hbound using
    fun n ↦ exists_wave_frequency (hu n) (hv n) (huc n) (hvc n) (w := w n)
      (by dsimp [w]; positivity)
  have hx := waveSeries_twice_x hw hu hv hbound
  have hy := waveSeries_twice_y (k := k) hus hvs hd
  have hae := hclaim (waveSeries u v k)
    (fun x y _ _ ↦ (hx y).1 x) (fun x y _ _ ↦ (hy x).1 y)
    (fun x y _ _ ↦ (hx y).2 x) (fun x y _ _ ↦ (hy x).2 y)
  let I := Ioo (0 : ℝ) 1
  let Q : Set (ℝ × ℝ) := Ioo (0, 0) (1, 1)
  have hEQ : B ×ˢ I ⊆ Q := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨lt_of_le_not_ge ⟨(hBI hx).1.le, hy.1.le⟩ (fun h ↦ (hBI hx).1.not_ge h.1),
      lt_of_le_not_ge ⟨(hBI hx).2.le, hy.2.le⟩ (fun h ↦ (hBI hx).2.not_ge h.1)⟩
  have hfail (p : ℝ × ℝ) (hp : p ∈ B ×ˢ I) :
      ¬ DifferentiableAt ℝ (fun x ↦ deriv (fun y ↦ waveSeries u v k (x, y)) p.2) p.1 := by
    intro hdiff
    let D (x : ℝ) := deriv (fun y ↦ waveSeries u v k (x, y)) p.2
    have hzero : D p.1 = 0 := by
      dsimp only [D]
      rw [waveSeries_eq_zero hus hvs (hout _ hp.1)]
      simp
    have hcont : ContinuousAt D p.1 := hdiff.continuousAt
    obtain ⟨ε, hε, hclose⟩ := Metric.continuousAt_iff.mp hcont (1 / 2) (by norm_num)
    obtain ⟨n, hn⟩ := hnear _ hp.1 ε hε
    have hsmall {t : ℝ} (ht : t ∈ ball (c n) (r n)) : |D t| < 1 / 2 := by
      have hdist : dist t p.1 < ε := calc
        dist t p.1 ≤ dist t (c n) + dist (c n) p.1 := dist_triangle ..
        _ ≤ dist (c n) p.1 + r n := by linarith [mem_ball.mp ht]
        _ < ε := hn
      simpa only [Real.dist_eq, hzero, sub_zero] using hclose hdist
    have hcompute {t : ℝ} (ht : t ∈ ball (c n) (r n)) :
        D t = u n t * Real.cos (k n * p.2) + v n t * Real.sin (k n * p.2) := by
      dsimp only [D]
      rw [waveSeries_eq_wave hus hvs hd ht]
      exact (hasDerivAt_wave_y _ _ (hk n).ne' _ _).deriv
    rcases abs_cos_or_abs_sin (k n * p.2) with hcos | hsin
    · have h := hsmall (ha n)
      rw [hcompute (ha n), hua n, hva n, one_mul, zero_mul, add_zero] at h
      exact (not_lt_of_ge hcos) h
    · have h := hsmall (hb n)
      rw [hcompute (hb n), hub n, hvb n, zero_mul, one_mul, zero_add] at h
      exact (not_lt_of_ge hsin) h
  have hfailure : (volume.restrict Q) (B ×ˢ I) = 0 := by
    have hn : ∀ᵐ p ∂(volume.restrict Q), p ∉ B ×ˢ I :=
      hae.mono fun p hp hmem ↦ hfail p hmem hp
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hn
  have hmeasure : (volume.restrict Q) (B ×ˢ I) = volume B := by
    rw [Measure.restrict_apply (hB.prod measurableSet_Ioo), inter_eq_left.mpr hEQ,
      Measure.volume_eq_prod, Measure.prod_prod]
    simp [I, Real.volume_Ioo]
  exact hBpos (hmeasure ▸ hfailure)

end

end MathlibExt.Analysis.Calculus.ScottishBook66Wanted
