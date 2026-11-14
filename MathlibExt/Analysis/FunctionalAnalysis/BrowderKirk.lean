/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Uniform
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section

section

open Set

namespace MathlibExt.Analysis.FunctionalAnalysis.BrowderKirkWanted

private theorem exists_one_div_succ_lt {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 1 / ((N : ℝ) + 1) < η := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds hη)
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by have h2 := hN N le_rfl; simpa using h2⟩

private theorem one_div_succ_le_of_le {N k : ℕ} (h : N ≤ k) :
    1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
  apply one_div_le_one_div_of_le
  · have hN : (0:ℝ) ≤ (N : ℝ) := by positivity
    linarith
  · have hNk : (N:ℝ) ≤ (k:ℝ) := Nat.cast_le.mpr h
    linarith

/-- Asymptotic radius of a sequence at a point: `limsup_n ‖u n - x‖`. -/
private noncomputable def asympRadius {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) (x : E) : ℝ :=
  Filter.limsup (fun n => ‖u n - x‖) Filter.atTop

private theorem asympRadius_le_of_eventually
    {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} {z : E} {C : ℝ}
    (h : ∀ᶠ t in Filter.atTop, ‖u t - z‖ ≤ C) :
    asympRadius u z ≤ C := by
  change Filter.limsup (fun n => ‖u n - z‖) Filter.atTop ≤ C
  exact Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le Filter.atTop (fun n => norm_nonneg _)) h

private theorem zero_le_asympRadius
    {E : Type*} [NormedAddCommGroup E]
    {K : Set E} {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    {u : ℕ → E} (hu_mem : ∀ n, u n ∈ K)
    {x : E} (hx : x ∈ K) :
    0 ≤ asympRadius u x := by
  change 0 ≤ Filter.limsup (fun n => ‖u n - x‖) Filter.atTop
  exact Filter.le_limsup_of_le
    (Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall (fun n => hD _ (hu_mem n) _ hx)))
    (fun b hb => let ⟨n, hn⟩ := hb.exists; (norm_nonneg _).trans hn)

private theorem eventually_asympRadius_lt
    {E : Type*} [NormedAddCommGroup E]
    {K : Set E} {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    {u : ℕ → E} (hu_mem : ∀ n, u n ∈ K)
    {x : E} (hx : x ∈ K) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in Filter.atTop, ‖u n - x‖ < asympRadius u x + η := by
  change ∀ᶠ n in Filter.atTop,
    ‖u n - x‖ < Filter.limsup (fun n => ‖u n - x‖) Filter.atTop + η
  exact Filter.eventually_lt_of_limsup_lt
    (lt_add_of_pos_right _ hη)
    (Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall (fun n => hD _ (hu_mem n) _ hx)))

/-- Uniform convexity gives a midpoint estimate at a fixed radius. -/
private theorem uc_midpoint_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]
    {R0 : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ {a b : E}, ‖a‖ ≤ R0 → ‖b‖ ≤ R0 → ε ≤ ‖a - b‖ →
      ‖(1 / 2 : ℝ) • (a + b)‖ ≤ R0 - δ / 2 := by
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_mul_sub E hε R0
  refine ⟨δ, hδ, fun {a b} ha hb hsep => ?_⟩
  have h2 := h ha hb hsep
  calc ‖(1 / 2 : ℝ) • (a + b)‖ = (1 / 2) * ‖a + b‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2) * (2 * R0 - δ) := by
        apply mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 1 / 2)
    _ = R0 - δ / 2 := by ring

/-- Scaled version: the midpoint estimate at any smaller radius, by scaling up. -/
private theorem uc_midpoint_scaled
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R0 : ℝ} (hR0 : 0 < R0) {ε : ℝ} (hε : 0 < ε)
    {δ : ℝ}
    (hUC : ∀ {a b : E}, ‖a‖ ≤ R0 → ‖b‖ ≤ R0 → ε ≤ ‖a - b‖ →
      ‖(1 / 2 : ℝ) • (a + b)‖ ≤ R0 - δ / 2)
    {R : ℝ} (hR : 0 < R) (hRR : R ≤ R0)
    {a b : E} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hsep : ε ≤ ‖a - b‖) :
    ‖(1 / 2 : ℝ) • (a + b)‖ ≤ R * (1 - δ / (2 * R0)) := by
  have hR0ne : R0 ≠ 0 := ne_of_gt hR0
  have hRne : R ≠ 0 := ne_of_gt hR
  have h2R0ne : (2:ℝ) * R0 ≠ 0 := mul_ne_zero (by norm_num) hR0ne
  set s : ℝ := R0 / R with hs
  have hs0 : 0 < s := div_pos hR0 hR
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ hR]
    linarith
  have hsa : ‖s • a‖ ≤ R0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0.le]
    calc s * ‖a‖ ≤ s * R := by
          apply mul_le_mul_of_nonneg_left ha hs0.le
      _ = R0 := by
          rw [hs]
          exact div_mul_cancel₀ R0 hRne
  have hsb : ‖s • b‖ ≤ R0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0.le]
    calc s * ‖b‖ ≤ s * R := by
          apply mul_le_mul_of_nonneg_left hb hs0.le
      _ = R0 := by
          rw [hs]
          exact div_mul_cancel₀ R0 hRne
  have hsep' : ε ≤ ‖s • a - s • b‖ := by
    have e1 : s • a - s • b = s • (a - b) := (smul_sub s a b).symm
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0.le]
    calc ε = 1 * ε := (one_mul ε).symm
      _ ≤ s * ‖a - b‖ := mul_le_mul hs1 hsep hε.le hs0.le
  have hUCab := hUC hsa hsb hsep'
  have hscale : (1 / 2 : ℝ) • (s • a + s • b) = s • ((1 / 2 : ℝ) • (a + b)) := by
    simp only [smul_add, ← mul_smul, mul_comm (1 / 2 : ℝ) s]
  rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0.le] at hUCab
  have hM : ‖(1 / 2 : ℝ) • (a + b)‖ ≤ (R0 - δ / 2) / s := by
    rw [le_div_iff₀ hs0, mul_comm]
    exact hUCab
  calc ‖(1 / 2 : ℝ) • (a + b)‖ ≤ (R0 - δ / 2) / s := hM
    _ = R * (1 - δ / (2 * R0)) := by
        rw [hs]
        field_simp

/--
If two points `p q` are eventually within radius `R` of the sequence and are
`ε`-separated, their midpoint has asymptotic radius at most `R * (1 - δ/(2R0))`.
-/
private theorem midpoint_asympRadius_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R0 : ℝ} (hR0 : 0 < R0) {ε : ℝ} (hε : 0 < ε)
    {δ0 : ℝ}
    (hUC0 : ∀ {a b : E}, ‖a‖ ≤ R0 → ‖b‖ ≤ R0 → ε ≤ ‖a - b‖ →
      ‖(1 / 2 : ℝ) • (a + b)‖ ≤ R0 - δ0 / 2)
    {R : ℝ} (hR : 0 < R) (hRR : R ≤ R0)
    {u : ℕ → E} {p q : E}
    (hB : ∀ᶠ t in Filter.atTop, ‖u t - p‖ ≤ R ∧ ‖u t - q‖ ≤ R)
    (hsep : ε ≤ ‖p - q‖)
    {m : E} (hm : m = (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) :
    asympRadius u m ≤ R * (1 - δ0 / (2 * R0)) := by
  apply asympRadius_le_of_eventually
  apply hB.mono
  intro t ht
  obtain ⟨htp, htq⟩ := ht
  have hsepm : ε ≤ ‖(u t - p) - (u t - q)‖ := by
    have e : (u t - p) - (u t - q) = q - p := by abel
    rw [e, norm_sub_rev]
    exact hsep
  have hsc := uc_midpoint_scaled hR0 hε hUC0 hR hRR htp htq hsepm
  have ehalf : (1 / 2 : ℝ) • u t + (1 / 2 : ℝ) • u t = u t := by
    rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
  have e2 : (1 / 2 : ℝ) • ((u t - p) + (u t - q))
      = ((1 / 2 : ℝ) • u t + (1 / 2 : ℝ) • u t) - ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) := by
    rw [smul_add, smul_sub, smul_sub]
    abel
  have heq : (1 / 2 : ℝ) • ((u t - p) + (u t - q)) = u t - m := by
    rw [e2, ehalf, hm]
  rw [heq] at hsc
  exact hsc

/-- Choice of a slightly enlarged radius whose contracted value is below `r`. -/
private theorem exists_radius_contract
    {r R0 δ0 : ℝ} (hr : 0 < r) (hR0 : 0 < R0) (hδ0 : 0 < δ0) (hRr : r + 1 ≤ R0) :
    ∃ ηstar R : ℝ, 0 < ηstar ∧ ηstar ≤ 1 / 2 ∧ 0 < R ∧ R ≤ R0 ∧ R = r + ηstar ∧
      R * (1 - δ0 / (2 * R0)) < r := by
  have h4R0 : (0:ℝ) < 4 * R0 := by linarith
  have h2R0 : (0:ℝ) < 2 * R0 := by linarith
  have hApos : 0 < r * δ0 / (4 * R0) := div_pos (mul_pos hr hδ0) h4R0
  set η0 : ℝ := min (r * δ0 / (4 * R0)) (1 / 2) with hη0def
  have hηpos : 0 < η0 := lt_min hApos (by norm_num)
  have hη1 : η0 ≤ 1 / 2 := min_le_right _ _
  have hηA : η0 ≤ r * δ0 / (4 * R0) := min_le_left _ _
  have hRpos : 0 < r + η0 := by linarith
  have hRR0 : r + η0 ≤ R0 := by linarith
  refine ⟨η0, r + η0, hηpos, hη1, hRpos, hRR0, rfl, ?_⟩
  have hA : r * δ0 / (4 * R0) < r * δ0 / (2 * R0) := by
    have h4ne : (4:ℝ) * R0 ≠ 0 := ne_of_gt h4R0
    have h2ne : (2:ℝ) * R0 ≠ 0 := ne_of_gt h2R0
    have hpos : (0:ℝ) < r * δ0 / (4 * R0) := div_pos (mul_pos hr hδ0) h4R0
    have e : r * δ0 / (2 * R0) = 2 * (r * δ0 / (4 * R0)) := by
      field_simp
      ring
    rw [e]
    linarith
  have hB : r * δ0 / (2 * R0) ≤ (r + η0) * δ0 / (2 * R0) := by
    have hrR : r ≤ r + η0 := le_add_of_nonneg_right hηpos.le
    have hle : r * δ0 ≤ (r + η0) * δ0 := mul_le_mul_of_nonneg_right hrR hδ0.le
    rw [div_eq_mul_one_div (r * δ0) (2 * R0),
      div_eq_mul_one_div ((r + η0) * δ0) (2 * R0)]
    exact mul_le_mul_of_nonneg_right hle (le_of_lt (one_div_pos.mpr h2R0))
  have hηR : η0 < (r + η0) * δ0 / (2 * R0) :=
    lt_of_le_of_lt hηA (lt_of_lt_of_le hA hB)
  have e : (r + η0) * (1 - δ0 / (2 * R0)) = (r + η0) - (r + η0) * δ0 / (2 * R0) := by
    ring
  rw [e]
  linarith

/-- Approximate fixed points: contractions toward a base point give
`u n ∈ K` with `‖u n - f (u n)‖ → 0`, via Banach's theorem on `K`. -/
private theorem approxFixedPoint_seq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK_nonempty : K.Nonempty)
    (hK_closed : IsClosed K)
    (hK_bounded : Bornology.IsBounded K) (hK_convex : Convex ℝ K)
    {f : E → E} (hf_maps : MapsTo f K K) (hf_lip : LipschitzOnWith 1 f K) :
    ∃ u : ℕ → E, (∀ n, u n ∈ K) ∧
      Filter.Tendsto (fun n => ‖u n - f (u n)‖) Filter.atTop (nhds 0) := by
  obtain ⟨u0, hu0⟩ := hK_nonempty
  obtain ⟨rD, hrD⟩ := hK_bounded.subset_closedBall u0
  have hrDnn : 0 ≤ rD := by
    have h0 : u0 ∈ Metric.closedBall u0 rD := hrD hu0
    rw [Metric.mem_closedBall, dist_self] at h0
    exact h0
  have hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ rD + rD := by
    intro x hx y hy
    have hx' : dist x u0 ≤ rD := Metric.mem_closedBall.mp (hrD hx)
    have hy' : dist y u0 ≤ rD := Metric.mem_closedBall.mp (hrD hy)
    calc dist x y ≤ dist x u0 + dist u0 y := dist_triangle _ _ _
      _ ≤ rD + rD := by
        have e : dist u0 y = dist y u0 := dist_comm _ _
        rw [e]
        linarith
  have key : ∀ n : ℕ, ∃ v ∈ K, ‖v - f v‖ ≤ (rD + rD) / ((n : ℝ) + 1) := by
    intro n
    have hnpos : (0:ℝ) < (n : ℝ) + 1 := by
      have hN : (0:ℝ) ≤ (n : ℝ) := by positivity
      linarith
    have hnne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hnpos
    set τ : ℝ := (n : ℝ) / ((n : ℝ) + 1) with hτdef
    have hτnn : 0 ≤ τ := div_nonneg (by positivity) hnpos.le
    have hτlt : τ < 1 := (div_lt_one hnpos).mpr (by linarith)
    have hτle : τ ≤ 1 := le_of_lt hτlt
    have h1m : 1 - τ = 1 / ((n : ℝ) + 1) := by
      rw [hτdef]
      field_simp
      ring
    have hGmaps : MapsTo (fun x => (1 - τ) • u0 + τ • f x) K K := by
      intro x hx
      exact hK_convex hu0 (hf_maps hx) (sub_nonneg.mpr hτle) hτnn (sub_add_cancel 1 τ)
    have hLip : LipschitzWith (NNReal.mk τ hτnn : NNReal)
        (MapsTo.restrict (fun x => (1 - τ) • u0 + τ • f x) K K hGmaps) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      have hx : (x : E) ∈ K := x.property
      have hy : (y : E) ∈ K := y.property
      have hff : dist (f (x:E)) (f (y:E)) ≤ dist (x:E) (y:E) := by
        have h := hf_lip.dist_le_mul _ hx _ hy
        simpa using h
      change dist ((1 - τ) • u0 + τ • f (x:E)) ((1 - τ) • u0 + τ • f (y:E))
        ≤ ↑(NNReal.mk τ hτnn : NNReal) * dist (x:E) (y:E)
      have eG : (1 - τ) • u0 + τ • f (x:E) - ((1 - τ) • u0 + τ • f (y:E))
          = τ • (f (x:E) - f (y:E)) := by
        rw [smul_sub]
        abel
      have eN : dist ((1 - τ) • u0 + τ • f (x:E)) ((1 - τ) • u0 + τ • f (y:E))
          = τ * dist (f (x:E)) (f (y:E)) := by
        rw [dist_eq_norm, dist_eq_norm, eG, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hτnn]
      rw [eN]
      calc τ * dist (f (x:E)) (f (y:E)) ≤ τ * dist (x:E) (y:E) :=
            mul_le_mul_of_nonneg_left hff hτnn
        _ = ↑(NNReal.mk τ hτnn : NNReal) * dist (x:E) (y:E) := by
            simp only [NNReal.coe_mk]
    have hKlt : (NNReal.mk τ hτnn : NNReal) < 1 :=
      NNReal.coe_lt_coe.mp
        (by simp only [NNReal.coe_mk, NNReal.coe_one]; exact hτlt)
    have hcon : ContractingWith (NNReal.mk τ hτnn : NNReal)
        (MapsTo.restrict (fun x => (1 - τ) • u0 + τ • f x) K K hGmaps) :=
      ⟨hKlt, hLip⟩
    obtain ⟨v, hvK, hvfix, _, _⟩ := hcon.exists_fixedPoint'
      hK_closed.isComplete hGmaps hu0 (edist_ne_top _ _)
    refine ⟨v, hvK, ?_⟩
    have hfix : (1 - τ) • u0 + τ • f v = v := hvfix
    have e : (1 - τ) • f v + τ • f v = f v := by
      rw [← add_smul, show (1 - τ : ℝ) + τ = 1 by ring, one_smul]
    have h1 : (1 - τ) • (u0 - f v) = ((1 - τ) • u0 + τ • f v) - f v := by
      rw [smul_sub]
      calc (1 - τ) • u0 - (1 - τ) • f v
          = ((1 - τ) • u0 + τ • f v) - ((1 - τ) • f v + τ • f v) := by abel
        _ = ((1 - τ) • u0 + τ • f v) - f v := by rw [e]
    have ev : v - f v = (1 - τ) • (u0 - f v) := by
      rw [h1, hfix]
    calc ‖v - f v‖ = ‖(1 - τ) • (u0 - f v)‖ := by rw [ev]
      _ = (1 - τ) * ‖u0 - f v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hτle)]
      _ ≤ (1 - τ) * (rD + rD) := by
          apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hτle)
          rw [← dist_eq_norm]
          exact hD _ hu0 _ (hf_maps hvK)
      _ = (rD + rD) / ((n:ℝ)+1) := by
          rw [h1m]
          ring
  choose u huK huB using key
  have hlim : Filter.Tendsto (fun n : ℕ => (rD + rD) / (((n:ℝ)) + 1)) Filter.atTop
      (nhds 0) := by
    have h1 := Filter.Tendsto.const_mul (rD + rD)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [mul_zero] at h1
    have e : (fun n : ℕ => (rD + rD) / (((n:ℝ)) + 1))
        = (fun n : ℕ => (rD + rD) * (1 / (((n:ℝ)) + 1))) :=
      funext fun n => div_eq_mul_one_div _ _
    rw [e]
    exact h1
  exact ⟨u, huK, squeeze_zero (fun n => norm_nonneg _) (fun n => huB n) hlim⟩

/-- The asymptotic center of an approximate fixed-point sequence is a fixed point. -/
private theorem asymptoticCenter_fixedPoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E] [CompleteSpace E]
    {K : Set E} (hK_closed : IsClosed K)
    (hK_bounded : Bornology.IsBounded K) (hK_convex : Convex ℝ K)
    {f : E → E} (hf_maps : MapsTo f K K) (hf_lip : LipschitzOnWith 1 f K)
    {u : ℕ → E} (hu_mem : ∀ n, u n ∈ K)
    (hu_apx : Filter.Tendsto (fun n => ‖u n - f (u n)‖) Filter.atTop (nhds 0)) :
    ∃ y ∈ K, f y = y := by
  have hKne : K.Nonempty := ⟨u 0, hu_mem 0⟩
  obtain ⟨rD, hrD⟩ := hK_bounded.subset_closedBall (u 0)
  have hrDnn : 0 ≤ rD := by
    have h0 : u 0 ∈ Metric.closedBall (u 0) rD := hrD (hu_mem 0)
    rw [Metric.mem_closedBall, dist_self] at h0
    exact h0
  have hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ rD + rD := by
    intro x hx y hy
    have hx' : dist x (u 0) ≤ rD := Metric.mem_closedBall.mp (hrD hx)
    have hy' : dist y (u 0) ≤ rD := Metric.mem_closedBall.mp (hrD hy)
    calc ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
      _ ≤ dist x (u 0) + dist (u 0) y := dist_triangle _ _ _
      _ ≤ rD + rD := by
        have e : dist (u 0) y = dist y (u 0) := dist_comm _ _
        rw [e]
        linarith
  set r : ℝ := sInf (asympRadius u '' K) with hrdef
  have hImage_ne : (asympRadius u '' K).Nonempty := hKne.image _
  have hBddBelow : BddBelow (asympRadius u '' K) := by
    refine ⟨0, ?_⟩
    intro b hb
    rw [Set.mem_image] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    exact zero_le_asympRadius hD hu_mem hx
  have hr_le : ∀ x ∈ K, r ≤ asympRadius u x := by
    intro x hx
    rw [hrdef]
    exact csInf_le hBddBelow ⟨x, hx, rfl⟩
  have hr_nn : 0 ≤ r := by
    rw [hrdef]
    apply le_csInf hImage_ne
    intro b hb
    rw [Set.mem_image] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    exact zero_le_asympRadius hD hu_mem hx
  have hmin : ∀ k : ℕ, ∃ y ∈ K, asympRadius u y < r + 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hlt : r < r + 1 / ((k : ℝ) + 1) := lt_add_of_pos_right _ hpos
    rw [hrdef] at hlt
    obtain ⟨b, hb, hblt⟩ := exists_lt_of_csInf_lt hImage_ne hlt
    rw [Set.mem_image] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨y, hy, hblt⟩
  choose y hyK hyphi using hmin
  have hyCauchy : CauchySeq y := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    by_cases hr0 : r = 0
    · obtain ⟨N, hN⟩ := exists_one_div_succ_lt (show (0:ℝ) < ε / 2 by linarith)
      refine ⟨N, fun m hm n hn => ?_⟩
      have hmk : dist (y m) (y n) ≤ asympRadius u (y m) + asympRadius u (y n) := by
        apply le_of_forall_pos_lt_add
        intro η hη
        have e1 := eventually_asympRadius_lt hD hu_mem (hyK m)
          (show (0:ℝ) < η / 2 by linarith)
        have e2 := eventually_asympRadius_lt hD hu_mem (hyK n)
          (show (0:ℝ) < η / 2 by linarith)
        obtain ⟨t, ht1, ht2⟩ := (e1.and e2).exists
        calc dist (y m) (y n) = ‖y m - y n‖ := dist_eq_norm _ _
          _ ≤ ‖y m - u t‖ + ‖u t - y n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ = ‖u t - y m‖ + ‖u t - y n‖ := by rw [norm_sub_rev]
          _ < (asympRadius u (y m) + η / 2) + (asympRadius u (y n) + η / 2) :=
              add_lt_add ht1 ht2
          _ = asympRadius u (y m) + asympRadius u (y n) + η := by ring
      have b1 : asympRadius u (y m) < 1 / ((m:ℝ) + 1) := by
        have h := hyphi m
        rw [hr0] at h
        linarith
      have b2 : asympRadius u (y n) < 1 / ((n:ℝ) + 1) := by
        have h := hyphi n
        rw [hr0] at h
        linarith
      have c1 : (1:ℝ) / ((m:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := one_div_succ_le_of_le hm
      have c2 : (1:ℝ) / ((n:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := one_div_succ_le_of_le hn
      calc dist (y m) (y n) ≤ asympRadius u (y m) + asympRadius u (y n) := hmk
        _ < 1 / ((m:ℝ) + 1) + 1 / ((n:ℝ) + 1) := add_lt_add b1 b2
        _ ≤ 1 / ((N:ℝ) + 1) + 1 / ((N:ℝ) + 1) := add_le_add c1 c2
        _ < ε / 2 + ε / 2 := add_lt_add hN hN
        _ = ε := by ring
    · have hrpos : 0 < r := by
        rcases eq_or_lt_of_le hr_nn with h | h
        · exfalso
          exact hr0 h.symm
        · exact h
      have hR0 : (0:ℝ) < r + 1 := by linarith
      obtain ⟨δ0, hδ0, hUC0⟩ := uc_midpoint_le (E := E) (R0 := r + 1) hε
      obtain ⟨ηstar, R, hηpos, hη1, hRpos, hRR0, hReq, hCR⟩ :=
        exists_radius_contract hrpos hR0 hδ0 (le_refl _)
      obtain ⟨N, hN⟩ := exists_one_div_succ_lt (show (0:ℝ) < ηstar / 2 by linarith)
      refine ⟨N, fun m hm n hn => ?_⟩
      by_contra hcon
      push Not at hcon
      have hsep : ε ≤ ‖y m - y n‖ := by
        have e : dist (y m) (y n) = ‖y m - y n‖ := dist_eq_norm _ _
        rwa [e] at hcon
      have am : asympRadius u (y m) < r + ηstar / 2 := by
        have h1 := hyphi m
        have h2 : (1:ℝ) / ((m:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := one_div_succ_le_of_le hm
        have h3 : (1:ℝ) / ((N:ℝ) + 1) ≤ ηstar / 2 := le_of_lt hN
        linarith
      have an : asympRadius u (y n) < r + ηstar / 2 := by
        have h1 := hyphi n
        have h2 : (1:ℝ) / ((n:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := one_div_succ_le_of_le hn
        have h3 : (1:ℝ) / ((N:ℝ) + 1) ≤ ηstar / 2 := le_of_lt hN
        linarith
      have hτ2 : (0:ℝ) < ηstar / 2 := by linarith
      have e1 := eventually_asympRadius_lt hD hu_mem (hyK m) hτ2
      have e2 := eventually_asympRadius_lt hD hu_mem (hyK n) hτ2
      have eB : ∀ᶠ t in Filter.atTop, ‖u t - y m‖ ≤ R ∧ ‖u t - y n‖ ≤ R := by
        have g1 : ∀ᶠ t in Filter.atTop, ‖u t - y m‖ ≤ R := by
          apply e1.mono
          intro t ht
          rw [hReq]
          linarith [am]
        have g2 : ∀ᶠ t in Filter.atTop, ‖u t - y n‖ ≤ R := by
          apply e2.mono
          intro t ht
          rw [hReq]
          linarith [an]
        exact g1.and g2
      set mp : E := (1 / 2 : ℝ) • y m + (1 / 2 : ℝ) • y n with hmpdef
      have hmpK : mp ∈ K :=
        hK_convex (hyK m) (hyK n) (by norm_num) (by norm_num) (by norm_num)
      have hφmp := midpoint_asympRadius_le hR0 hε hUC0 hRpos hRR0 eB hsep hmpdef
      have h1 : r ≤ asympRadius u mp := hr_le _ hmpK
      linarith
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hyCauchy
  have hzK : z ∈ K :=
    hK_closed.mem_of_tendsto hz (Filter.Eventually.of_forall hyK)
  have hφz_le : asympRadius u z ≤ r := by
    apply le_of_forall_pos_le_add
    intro σ hσ
    have hσ2 : (0:ℝ) < σ / 2 := by linarith
    have hσ4 : (0:ℝ) < σ / 4 := by linarith
    obtain ⟨N1, hN1⟩ := exists_one_div_succ_lt hσ4
    have hev : ∀ᶠ k in Filter.atTop, dist (y k) z < σ / 4 :=
      (Metric.tendsto_nhds.mp hz) (σ / 4) hσ4
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N2, hN2⟩ := hev
    set k : ℕ := max N1 N2 with hkdef
    have hk1 : N1 ≤ k := le_max_left _ _
    have hk2 : N2 ≤ k := le_max_right _ _
    have hα : (1:ℝ) / (((k:ℝ)) + 1) < σ / 4 :=
      lt_of_le_of_lt (one_div_succ_le_of_le hk1) hN1
    have hφyk : asympRadius u (y k) < r + σ / 4 := by
      have h1 := hyphi k
      have h2 : (1:ℝ) / (((k:ℝ)) + 1) ≤ σ / 4 := le_of_lt hα
      linarith
    have hykz : dist (y k) z < σ / 4 := hN2 k hk2
    have hbk : ∀ᶠ t in Filter.atTop, ‖u t - z‖ ≤ r + σ := by
      have e1 := eventually_asympRadius_lt hD hu_mem (hyK k)
        (show (0:ℝ) < σ / 2 by linarith)
      have h' : ∀ᶠ t in Filter.atTop, ‖u t - z‖ < r + σ := by
        apply e1.mono
        intro t ht
        calc ‖u t - z‖ ≤ ‖u t - y k‖ + ‖y k - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ = ‖u t - y k‖ + dist (y k) z := by rw [dist_eq_norm]
          _ < (asympRadius u (y k) + σ / 2) + σ / 4 := add_lt_add ht hykz
          _ < r + σ := by linarith [hφyk]
      exact h'.mono fun t ht => le_of_lt ht
    exact asympRadius_le_of_eventually hbk
  have hφz : asympRadius u z = r := le_antisymm hφz_le (hr_le _ hzK)
  have hfzK : f z ∈ K := hf_maps hzK
  have hφfz_le : asympRadius u (f z) ≤ r := by
    apply le_of_forall_pos_le_add
    intro σ hσ
    have hσ2 : (0:ℝ) < σ / 2 := by linarith
    have e1 : ∀ᶠ t in Filter.atTop, ‖u t - f (u t)‖ < σ / 2 :=
      hu_apx.eventually (eventually_lt_nhds hσ2)
    have e2 : ∀ᶠ t in Filter.atTop, ‖u t - z‖ < r + σ / 2 := by
      have hle : Filter.limsup (fun n => ‖u n - z‖) Filter.atTop ≤ r := hφz_le
      have hlt : Filter.limsup (fun n => ‖u n - z‖) Filter.atTop < r + σ / 2 :=
        lt_of_le_of_lt hle (lt_add_of_pos_right _ hσ2)
      exact Filter.eventually_lt_of_limsup_lt hlt
        (Filter.isBoundedUnder_of_eventually_le
          (Filter.Eventually.of_forall (fun n => hD _ (hu_mem n) _ hzK)))
    have hbk : ∀ᶠ t in Filter.atTop, ‖u t - f z‖ ≤ r + σ := by
      apply (e1.and e2).mono
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      have hnonexp : dist (f (u t)) (f z) ≤ dist (u t) z := by
        have h := hf_lip.dist_le_mul _ (hu_mem t) _ hzK
        simpa using h
      calc ‖u t - f z‖ ≤ ‖u t - f (u t)‖ + ‖f (u t) - f z‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖u t - f (u t)‖ + dist (f (u t)) (f z) := by rw [dist_eq_norm]
        _ ≤ σ / 2 + (r + σ / 2) := by
            apply add_le_add (le_of_lt ht1)
            apply le_trans hnonexp
            rw [dist_eq_norm]
            exact le_of_lt ht2
        _ = r + σ := by ring
    exact asympRadius_le_of_eventually hbk
  by_cases hr0 : r = 0
  · have hlim : Filter.Tendsto (fun n => ‖u n - z‖) Filter.atTop (nhds 0) := by
      have h0 : Filter.limsup (fun n => ‖u n - z‖) Filter.atTop = 0 := by
        have h := hφz
        rw [hr0] at h
        exact h
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hlt : Filter.limsup (fun n => ‖u n - z‖) Filter.atTop < ε := by
        rw [h0]
        exact hε
      have hlt' := Filter.eventually_lt_of_limsup_lt hlt
        (Filter.isBoundedUnder_of_eventually_le
          (Filter.Eventually.of_forall (fun n => hD _ (hu_mem n) _ hzK)))
      apply hlt'.mono
      intro n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact hn
    have hnorm : ‖f z - z‖ ≤ 0 := by
      apply le_of_forall_pos_lt_add
      intro σ hσ
      have hσ4 : (0:ℝ) < σ / 4 := by linarith
      have hσ2 : (0:ℝ) < σ / 2 := by linarith
      have e1 : ∀ᶠ t in Filter.atTop, ‖u t - z‖ < σ / 4 := by
        have hlt := (Metric.tendsto_nhds.mp hlim) (σ / 4) hσ4
        apply hlt.mono
        intro t ht
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at ht
        exact ht
      have e2 : ∀ᶠ t in Filter.atTop, ‖u t - f (u t)‖ < σ / 2 :=
        hu_apx.eventually (eventually_lt_nhds hσ2)
      obtain ⟨t, ht1, ht2⟩ := (e1.and e2).exists
      have hnonexp : dist (f z) (f (u t)) ≤ dist z (u t) := by
        have h := hf_lip.dist_le_mul _ hzK _ (hu_mem t)
        simpa using h
      have h1 : ‖f z - z‖ ≤ ‖f z - f (u t)‖ + ‖f (u t) - z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h2 : ‖f (u t) - z‖ ≤ ‖f (u t) - u t‖ + ‖u t - z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have g1 : ‖f z - f (u t)‖ ≤ dist z (u t) := by
        have e : ‖f z - f (u t)‖ = dist (f z) (f (u t)) := (dist_eq_norm _ _).symm
        rw [e]
        exact hnonexp
      have g2 : ‖f (u t) - u t‖ ≤ σ / 2 := by
        rw [norm_sub_rev]
        exact le_of_lt ht2
      have g4 : dist z (u t) = ‖u t - z‖ := by
        rw [dist_eq_norm, norm_sub_rev]
      have hle : ‖f z - z‖ ≤ dist z (u t) + σ / 2 + σ / 4 := by linarith
      have hlt : dist z (u t) + σ / 2 + σ / 4 < 0 + σ := by
        rw [g4]
        linarith [ht1]
      linarith
    have h0 : ‖f z - z‖ = 0 := le_antisymm hnorm (norm_nonneg _)
    have h00 : f z - z = 0 := norm_eq_zero.mp h0
    exact ⟨z, hzK, sub_eq_zero.mp h00⟩
  · have hrpos : 0 < r := by
      rcases eq_or_lt_of_le hr_nn with h | h
      · exfalso
        exact hr0 h.symm
      · exact h
    by_cases hd : ‖z - f z‖ = 0
    · have h00 : z - f z = 0 := norm_eq_zero.mp hd
      exact ⟨z, hzK, (sub_eq_zero.mp h00).symm⟩
    · have hdpos : 0 < ‖z - f z‖ := by
        rcases eq_or_lt_of_le (norm_nonneg (z - f z)) with h | h
        · exfalso
          exact hd h.symm
        · exact h
      have hR0 : (0:ℝ) < r + 1 := by linarith
      obtain ⟨δ0, hδ0, hUC0⟩ := uc_midpoint_le (E := E) (R0 := r + 1) hdpos
      obtain ⟨ηstar, R, hηpos, hη1, hRpos, hRR0, hReq, hCR⟩ :=
        exists_radius_contract hrpos hR0 hδ0 (le_refl _)
      have hτ2 : (0:ℝ) < ηstar / 2 := by linarith
      have ez : ∀ᶠ t in Filter.atTop, ‖u t - z‖ ≤ R := by
        have e := eventually_asympRadius_lt hD hu_mem hzK hτ2
        apply e.mono
        intro t ht
        have hb : asympRadius u z < r + ηstar / 2 := by
          have h1 := hφz_le
          linarith
        rw [hReq]
        linarith
      have efz : ∀ᶠ t in Filter.atTop, ‖u t - f z‖ ≤ R := by
        have e2 : ∀ᶠ t in Filter.atTop, ‖u t - f z‖ < r + ηstar / 2 := by
          have hle : Filter.limsup (fun n => ‖u n - f z‖) Filter.atTop ≤ r := hφfz_le
          have hlt : Filter.limsup (fun n => ‖u n - f z‖) Filter.atTop < r + ηstar / 2 :=
            lt_of_le_of_lt hle (lt_add_of_pos_right _ hτ2)
          exact Filter.eventually_lt_of_limsup_lt hlt
            (Filter.isBoundedUnder_of_eventually_le
              (Filter.Eventually.of_forall (fun n => hD _ (hu_mem n) _ hfzK)))
        apply e2.mono
        intro t ht
        rw [hReq]
        linarith
      set mp : E := (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • f z with hmpdef
      have hmpK : mp ∈ K :=
        hK_convex hzK hfzK (by norm_num) (by norm_num) (by norm_num)
      have hφmp := midpoint_asympRadius_le hR0 hdpos hUC0 hRpos hRR0 (ez.and efz)
        (le_refl _) hmpdef
      exfalso
      have h1 : r ≤ asympRadius u mp := hr_le _ hmpK
      linarith

/--
In a complete uniformly convex real normed space, every nonexpansive self-map `f : E → E` with
`MapsTo f K K` and `LipschitzOnWith 1 f K` of a nonempty closed bounded convex set `K` has a fixed
point in `K`, i.e. `∃ y ∈ K, f y = y`. Source: F. Browder, Proc. Nat. Acad. Sci. USA 1965, D.
Göhde, Math. Ann. 1965, and W. Kirk, Amer. Math. Monthly 1965-66, fixed-point theorem for
nonexpansive mappings in uniformly convex Banach spaces; textbook Goebel and Kirk, 1990; Lean
states complete uniformly convex real case with `Bornology.IsBounded` convex set.

Proves `Wanted` entry `browderGoehdeKirk_fixedPoint`.
-/
theorem browderGoehdeKirk_fixedPoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E] [CompleteSpace E]
    {K : Set E} (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_bounded : Bornology.IsBounded K) (hK_convex : Convex ℝ K)
    {f : E → E} (hf_maps : MapsTo f K K) (hf_lip : LipschitzOnWith 1 f K) :
    ∃ y ∈ K, f y = y := by
  obtain ⟨u, huK, huapx⟩ := approxFixedPoint_seq hK_nonempty hK_closed hK_bounded
    hK_convex hf_maps hf_lip
  exact asymptoticCenter_fixedPoint hK_closed hK_bounded hK_convex hf_maps hf_lip huK huapx

end MathlibExt.Analysis.FunctionalAnalysis.BrowderKirkWanted
