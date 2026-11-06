/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Uniform
import MathlibExt.Analysis.FunctionalAnalysis.MilmanPettis
import MathlibExt.Analysis.FunctionalAnalysis.EberleinSmulian
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-- Homogeneous uniform convexity modulus: `δ` does not depend on `R`. -/
private theorem bsak_uc_add_le_two_sub_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ), 0 < R → ∀ u v : E,
      ‖u‖ ≤ R → ‖v‖ ≤ R → ε * R ≤ ‖u - v‖ → ‖u + v‖ ≤ (2 - δ) * R := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_forall_closed_ball_dist_add_le_two_sub E hε
  refine ⟨δ, hδpos, fun R hR u v hu hv hdiff => ?_⟩
  have hRne : R ≠ 0 := ne_of_gt hR
  have hRinv : (0 : ℝ) < R⁻¹ := inv_pos.mpr hR
  have hRinvR : R⁻¹ * R = 1 := inv_mul_cancel₀ hRne
  have ha1 : ‖R⁻¹ • u‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRinv]
    calc R⁻¹ * ‖u‖ ≤ R⁻¹ * R :=
          mul_le_mul_of_nonneg_left hu (le_of_lt hRinv)
      _ = 1 := hRinvR
  have hb1 : ‖R⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRinv]
    calc R⁻¹ * ‖v‖ ≤ R⁻¹ * R :=
          mul_le_mul_of_nonneg_left hv (le_of_lt hRinv)
      _ = 1 := hRinvR
  have hdiff' : ε ≤ ‖R⁻¹ • u - R⁻¹ • v‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hRinv]
    have hscale : R⁻¹ * (ε * R) = ε := by
      calc R⁻¹ * (ε * R) = ε * (R⁻¹ * R) := by ring
        _ = ε := by rw [hRinvR, mul_one]
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hdiff (le_of_lt hRinv)
  have h2 := hδ ha1 hb1 hdiff'
  rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos hRinv] at h2
  have hmul := mul_le_mul_of_nonneg_right h2 (le_of_lt hR)
  have hback : R⁻¹ * ‖u + v‖ * R = ‖u + v‖ := by
    calc R⁻¹ * ‖u + v‖ * R = ‖u + v‖ * (R⁻¹ * R) := by ring
      _ = ‖u + v‖ := by rw [hRinvR, mul_one]
  rwa [hback] at hmul

/-- Two-block Kakutani estimate with contraction factor `θ`. -/
private theorem bsak_kakutani_two_block
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E] :
    ∃ θ : ℝ, 3 / 4 ≤ θ ∧ θ < 1 ∧ ∀ (R : ℝ), 0 < R → ∀ u v : E, ∀ g : StrongDual ℝ E,
      ‖g‖ ≤ 1 → g u = ‖u‖ → ‖u‖ ≤ R → ‖v‖ ≤ R → ‖g v‖ ≤ R / 4 → ‖u + v‖ ≤ 2 * θ * R := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    bsak_uc_add_le_two_sub_mul (E := E) (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨max (3 / 4) (1 - δ / 2), le_max_left _ _, ?_, ?_⟩
  · rw [max_lt_iff]
    exact ⟨by norm_num, by linarith⟩
  · intro R hR u v g hg1 hgu huR hvR hgv
    have hR2 : (0 : ℝ) ≤ R := le_of_lt hR
    by_cases hcase : R / 2 ≤ ‖u‖
    · have hgu' : R / 2 ≤ g u := by rw [hgu]; exact hcase
      have hgv' : g v ≤ R / 4 := le_trans (Real.le_norm_self _) hgv
      have hsub : g (u - v) = g u - g v := map_sub g u v
      have hle : R / 4 ≤ g (u - v) := by rw [hsub]; linarith
      have hnorm : g (u - v) ≤ ‖u - v‖ := by
        calc g (u - v) ≤ ‖g (u - v)‖ := Real.le_norm_self _
          _ ≤ ‖g‖ * ‖u - v‖ := ContinuousLinearMap.le_opNorm g (u - v)
          _ ≤ 1 * ‖u - v‖ :=
              mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)
          _ = ‖u - v‖ := one_mul _
      have hsep : (1 / 4) * R ≤ ‖u - v‖ := by linarith
      have hN1 := hδ R hR u v huR hvR hsep
      calc ‖u + v‖ ≤ (2 - δ) * R := hN1
        _ = 2 * (1 - δ / 2) * R := by ring
        _ ≤ 2 * max (3 / 4) (1 - δ / 2) * R := by
            apply mul_le_mul_of_nonneg_right _ hR2
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
            exact le_max_right _ _
    · push Not at hcase
      calc ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
        _ ≤ R / 2 + R := add_le_add hcase.le hvR
        _ = 2 * (3 / 4) * R := by ring
        _ ≤ 2 * max (3 / 4) (1 - δ / 2) * R := by
            apply mul_le_mul_of_nonneg_right _ hR2
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
            exact le_max_left _ _

/-- History-dependent subsequence extraction. -/
private theorem bsak_exists_strictMono_of_history
    {Q : List ℕ → ℕ → Prop}
    (hQ : ∀ l : List ℕ, ∀ᶠ n in Filter.atTop, Q l n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j : ℕ, Q ((List.range j).map φ) (φ j) := by
  classical
  have hpick : ∀ l : List ℕ, ∃ n, Q l n ∧ l.sum < n := by
    intro l
    obtain ⟨n, hn1, hn2⟩ := ((hQ l).and (Filter.eventually_gt_atTop l.sum)).exists
    exact ⟨n, hn1, hn2⟩
  choose nxt hnxtQ hnxtgt using hpick
  set step : List ℕ → List ℕ := fun l => l ++ [nxt l] with hstepdef
  set φ : ℕ → ℕ := fun j => nxt (step^[j] []) with hφdef
  have hstep : ∀ l, step l = l ++ [nxt l] := fun l => rfl
  have hφ : ∀ j, φ j = nxt (step^[j] []) := fun j => rfl
  have key : ∀ j, step^[j] [] = (List.range j).map φ := by
    intro j
    induction j with
    | zero => rw [Function.iterate_zero_apply, List.range_zero, List.map_nil]
    | succ j ih =>
      conv_lhs => rw [show j + 1 = j.succ from rfl, Function.iterate_succ_apply',
        hstep, ih]
      rw [List.range_succ, List.map_append, List.map_singleton, hφ, ih]
  have hmem : ∀ j, φ j ∈ step^[j + 1] [] := by
    intro j
    have e1 : step^[j + 1] [] = step (step^[j] []) := by
      rw [show j + 1 = j.succ from rfl, Function.iterate_succ_apply']
    have e2 : step (step^[j] []) = step^[j] [] ++ [φ j] := by
      rw [hstep, ← hφ j]
    rw [e1, e2]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hlt : ∀ j, φ j < φ (j + 1) := by
    intro j
    have h1 : φ j ≤ (step^[j + 1] []).sum := List.le_sum_of_mem (hmem j)
    have h2 : (step^[j + 1] []).sum < nxt (step^[j + 1] []) := hnxtgt _
    rw [hφ (j + 1)]
    exact lt_of_le_of_lt h1 h2
  refine ⟨φ, strictMono_nat_of_lt_succ hlt, fun j => ?_⟩
  rw [← key j, hφ j]
  exact hnxtQ _

/-- Greedy Kakutani selection of a subsequence. -/
private theorem bsak_exists_subseq_kakutani_selection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : ℕ → E}
    (hw : ∀ f : StrongDual ℝ E,
      Filter.Tendsto (fun n => f (w n)) Filter.atTop (nhds 0))
    (F : E → StrongDual ℝ E) (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j a b : ℕ, b ≤ j →
      ‖F (∑ i ∈ Finset.Ico a b, w (φ i)) (w (φ j))‖ ≤ η j := by
  classical
  have hQ : ∀ l : List ℕ, ∀ᶠ n in Filter.atTop,
      ∀ s ∈ l.toFinset.powerset, ‖F (∑ m ∈ s, w m) (w n)‖ ≤ η (l.length) := by
    intro l
    refine (Finset.eventually_all _).mpr fun s _ => ?_
    have hpos : (0 : ℝ) < η (l.length) := hη _
    have htend := hw (F (∑ m ∈ s, w m))
    have hev := (Metric.tendsto_nhds.mp htend) _ hpos
    apply hev.mono
    intro n hn
    rw [dist_zero_right] at hn
    exact hn.le
  obtain ⟨φ, hφmono, hφQ⟩ := bsak_exists_strictMono_of_history (Q := fun l n =>
    ∀ s ∈ l.toFinset.powerset, ‖F (∑ m ∈ s, w m) (w n)‖ ≤ η (l.length)) hQ
  refine ⟨φ, hφmono, fun j a b hbj => ?_⟩
  have hφj : ∀ s ∈ ((List.range j).map φ).toFinset.powerset,
      ‖F (∑ m ∈ s, w m) (w (φ j))‖ ≤ η (((List.range j).map φ).length) :=
    hφQ j
  rw [List.length_map, List.length_range] at hφj
  have hmem : (Finset.Ico a b).image φ ∈ ((List.range j).map φ).toFinset.powerset := by
    rw [Finset.mem_powerset]
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_Ico] at hi
    have hij : i < j := lt_of_lt_of_le hi.2 hbj
    rw [List.mem_toFinset]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hij, rfl⟩
  have hsum : ∑ m ∈ (Finset.Ico a b).image φ, w m = ∑ i ∈ Finset.Ico a b, w (φ i) :=
    Finset.sum_image (fun x _ y _ h => hφmono.injective h)
  rw [← hsum]
  exact hφj _ hmem

/-- One analytic block-combining step. -/
private theorem bsak_kakutani_block_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ}
    (hθ : ∀ (R : ℝ), 0 < R → ∀ u v : E, ∀ g : StrongDual ℝ E,
      ‖g‖ ≤ 1 → g u = ‖u‖ → ‖u‖ ≤ R → ‖v‖ ≤ R → |g v| ≤ R / 4 →
      ‖u + v‖ ≤ 2 * θ * R)
    {r : ℝ} (hr : 0 < r)
    {w' : ℕ → E} {F : E → StrongDual ℝ E}
    (hFnorm : ∀ v, ‖F v‖ ≤ 1) (hFval : ∀ v, F v v = ‖v‖)
    (hsel : ∀ j a b : ℕ, b ≤ j →
      ‖F (∑ i ∈ Finset.Ico a b, w' i) (w' j)‖ ≤ r / 8 * (1 / 2) ^ j) :
    ∀ a b c : ℕ, a ≤ b → b ≤ c → ∀ R : ℝ, r ≤ R →
      ‖∑ i ∈ Finset.Ico a b, w' i‖ ≤ R → ‖∑ i ∈ Finset.Ico b c, w' i‖ ≤ R →
      ‖∑ i ∈ Finset.Ico a c, w' i‖ ≤ 2 * θ * R := by
  intro a b c hab hbc R hR huR hvR
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le hr hR
  set u : E := ∑ i ∈ Finset.Ico a b, w' i with hu_def
  set v : E := ∑ i ∈ Finset.Ico b c, w' i with hv_def
  have hsum : u + v = ∑ i ∈ Finset.Ico a c, w' i := by
    rw [hu_def, hv_def, Finset.sum_Ico_consecutive _ hab hbc]
  have hgv : (F u) v = ∑ j ∈ Finset.Ico b c, F u (w' j) := by
    rw [hv_def, map_sum]
  have hterm : ∀ j ∈ Finset.Ico b c, ‖F u (w' j)‖ ≤ r / 8 * (1 / 2) ^ j := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have h := hsel j a b hj.1
    rw [← hu_def] at h
    exact h
  have hgeom : ∑ j ∈ Finset.Ico b c, ((1 / 2 : ℝ)) ^ j ≤ 2 := by
    have h1 := geom_sum_Ico_le_of_lt_one (m := b) (n := c)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    have h2 : ((1 / 2 : ℝ)) ^ b / (1 - 1 / 2) ≤ 2 := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        div_le_iff₀ (show (0 : ℝ) < 1 / 2 by norm_num)]
      calc (1 / 2 : ℝ) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        _ = 2 * (1 / 2) := by norm_num
    exact le_trans h1 h2
  have hnorm : ‖(F u) v‖ ≤ r / 4 := by
    calc ‖(F u) v‖ = ‖∑ j ∈ Finset.Ico b c, F u (w' j)‖ := by rw [hgv]
      _ ≤ ∑ j ∈ Finset.Ico b c, ‖F u (w' j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Ico b c, (r / 8 * (1 / 2) ^ j) := Finset.sum_le_sum hterm
      _ = r / 8 * ∑ j ∈ Finset.Ico b c, (1 / 2) ^ j := by rw [← Finset.mul_sum]
      _ ≤ r / 8 * 2 :=
          mul_le_mul_of_nonneg_left hgeom (div_nonneg hr.le (by norm_num))
      _ = r / 4 := by ring
  have hR4 : ‖(F u) v‖ ≤ R / 4 := by
    calc ‖(F u) v‖ ≤ r / 4 := hnorm
      _ ≤ R / 4 := by linarith
  have hmain := hθ R hRpos u v (F u) (hFnorm u) (hFval u) huR hvR hR4
  rw [← hsum]
  exact hmain

/-- Dyadic block bound by induction on `k`. -/
private theorem bsak_kakutani_dyadic_block_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ r : ℝ} (hθ34 : 3 / 4 ≤ θ)
    (hθ : ∀ (R : ℝ), 0 < R → ∀ u v : E, ∀ g : StrongDual ℝ E,
      ‖g‖ ≤ 1 → g u = ‖u‖ → ‖u‖ ≤ R → ‖v‖ ≤ R → |g v| ≤ R / 4 →
      ‖u + v‖ ≤ 2 * θ * R)
    (hr : 0 < r)
    {w' : ℕ → E} {F : E → StrongDual ℝ E}
    (hFnorm : ∀ v, ‖F v‖ ≤ 1) (hFval : ∀ v, F v v = ‖v‖)
    (hsel : ∀ j a b : ℕ, b ≤ j →
      ‖F (∑ i ∈ Finset.Ico a b, w' i) (w' j)‖ ≤ r / 8 * (1 / 2) ^ j)
    (hbnd : ∀ i, ‖w' i‖ ≤ r) :
    ∀ k m : ℕ,
      ‖∑ i ∈ Finset.Ico (m * 2 ^ k) ((m + 1) * 2 ^ k), w' i‖ ≤ (2 * θ) ^ k * r := by
  intro k m
  induction k generalizing m with
  | zero =>
    rw [show m * 2 ^ 0 = m by simp, show (m + 1) * 2 ^ 0 = m + 1 by simp,
      Nat.Ico_succ_singleton, Finset.sum_singleton]
    simpa using hbnd m
  | succ k IH =>
    have e1 : m * 2 ^ (k + 1) = (2 * m) * 2 ^ k := by rw [pow_succ]; ring
    have e2 : (m + 1) * 2 ^ (k + 1) = ((2 * m) + 2) * 2 ^ k := by
      rw [pow_succ]; ring
    rw [e1, e2]
    have h1k : (1 : ℝ) ≤ (2 * θ) ^ k := one_le_pow₀ (by linarith)
    have hR : r ≤ (2 * θ) ^ k * r := le_mul_of_one_le_left hr.le h1k
    have ih1 := IH (2 * m)
    have ih2 := IH (2 * m + 1)
    have e3 : ((2 * m + 1) + 1) * 2 ^ k = ((2 * m) + 2) * 2 ^ k := by ring
    rw [e3] at ih2
    have hle1 : (2 * m) * 2 ^ k ≤ ((2 * m) + 1) * 2 ^ k := by
      apply Nat.mul_le_mul_right; omega
    have hle2 : ((2 * m) + 1) * 2 ^ k ≤ ((2 * m) + 2) * 2 ^ k := by
      apply Nat.mul_le_mul_right; omega
    have hstep := bsak_kakutani_block_step hθ hr hFnorm hFval hsel
      ((2 * m) * 2 ^ k) (((2 * m) + 1) * 2 ^ k) (((2 * m) + 2) * 2 ^ k)
      hle1 hle2 ((2 * θ) ^ k * r) hR ih1 ih2
    calc ‖∑ i ∈ Finset.Ico ((2 * m) * 2 ^ k) (((2 * m) + 2) * 2 ^ k), w' i‖
          ≤ 2 * θ * ((2 * θ) ^ k * r) := hstep
      _ = (2 * θ) ^ (k + 1) * r := by rw [pow_succ]; ring

/-- Block decomposition of a range sum. -/
private theorem bsak_sum_range_mul_eq_sum_blocks
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (L q : ℕ) :
    ∑ i ∈ Finset.range (q * L), f i =
      ∑ m ∈ Finset.range q, ∑ i ∈ Finset.Ico (m * L) ((m + 1) * L), f i := by
  induction q with
  | zero => simp
  | succ q IH =>
    have hle : q * L ≤ (q + 1) * L := by apply Nat.mul_le_mul_right; omega
    rw [← Finset.sum_range_add_sum_Ico f hle, IH, Finset.sum_range_succ]

/-- Range-sum estimate from dyadic block bounds. -/
private theorem bsak_norm_sum_range_le_of_dyadic_blocks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w' : ℕ → E} {θ r : ℝ} (hθ0 : 0 ≤ θ) (hr0 : 0 ≤ r)
    (hbnd : ∀ i, ‖w' i‖ ≤ r)
    (hblock : ∀ k m : ℕ,
      ‖∑ i ∈ Finset.Ico (m * 2 ^ k) ((m + 1) * 2 ^ k), w' i‖ ≤ (2 * θ) ^ k * r) :
    ∀ k n : ℕ,
      ‖∑ i ∈ Finset.range n, w' i‖ ≤ (n : ℝ) * θ ^ k * r + (2 : ℝ) ^ k * r := by
  intro k n
  set q : ℕ := n / 2 ^ k with hqdef
  have hle : q * 2 ^ k ≤ n := by
    rw [hqdef]
    exact Nat.div_mul_le_self n (2 ^ k)
  have hqR : ((q * 2 ^ k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
  have hcast : ((q * 2 ^ k : ℕ) : ℝ) = (q : ℝ) * (2 : ℝ) ^ k := by
    simp [Nat.cast_mul, Nat.cast_pow]
  have hfirst : ‖∑ i ∈ Finset.range (q * 2 ^ k), w' i‖ ≤ (n : ℝ) * θ ^ k * r := by
    rw [bsak_sum_range_mul_eq_sum_blocks w' (2 ^ k) q]
    have hle1 : (q : ℝ) * ((2 * θ) ^ k * r) ≤ (n : ℝ) * θ ^ k * r := by
      have h1 : (q : ℝ) * ((2 * θ) ^ k * r)
          = ((q * 2 ^ k : ℕ) : ℝ) * (θ ^ k * r) := by
        rw [hcast, mul_pow]; ring
      rw [h1]
      calc ((q * 2 ^ k : ℕ) : ℝ) * (θ ^ k * r)
            ≤ (n : ℝ) * (θ ^ k * r) :=
            mul_le_mul_of_nonneg_right hqR (by positivity)
        _ = (n : ℝ) * θ ^ k * r := by ring
    calc ‖∑ m ∈ Finset.range q,
            ∑ i ∈ Finset.Ico (m * 2 ^ k) ((m + 1) * 2 ^ k), w' i‖
          ≤ ∑ m ∈ Finset.range q, ((2 * θ) ^ k * r) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => hblock k m))
      _ = (q : ℝ) * ((2 * θ) ^ k * r) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (n : ℝ) * θ ^ k * r := hle1
  have h2kpos : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
  have hmod : n % 2 ^ k < 2 ^ k := Nat.mod_lt n h2kpos
  have hdecomp : q * 2 ^ k + n % 2 ^ k = n := by
    have h := Nat.div_add_mod n (2 ^ k)
    rw [← hqdef] at h
    rwa [mul_comm] at h
  have hcard : (Finset.Ico (q * 2 ^ k) n).card ≤ 2 ^ k := by
    rw [Nat.card_Ico]
    omega
  have hsecond : ‖∑ i ∈ Finset.Ico (q * 2 ^ k) n, w' i‖ ≤ (2 : ℝ) ^ k * r := by
    calc ‖∑ i ∈ Finset.Ico (q * 2 ^ k) n, w' i‖
          ≤ ∑ i ∈ Finset.Ico (q * 2 ^ k) n, ‖w' i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.Ico (q * 2 ^ k) n, r :=
          Finset.sum_le_sum (fun i _ => hbnd i)
      _ = ((Finset.Ico (q * 2 ^ k) n).card : ℝ) * r := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ k * r := by
          apply mul_le_mul_of_nonneg_right _ hr0
          exact_mod_cast hcard
  have hsplit := (Finset.sum_range_add_sum_Ico w' hle).symm
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Cesàro convergence from dyadic block estimates. -/
private theorem bsak_tendsto_cesaro_zero_of_dyadic_blocks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w' : ℕ → E} {θ r : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hr0 : 0 ≤ r)
    (hbnd : ∀ i, ‖w' i‖ ≤ r)
    (hblock : ∀ k m : ℕ,
      ‖∑ i ∈ Finset.Ico (m * 2 ^ k) ((m + 1) * 2 ^ k), w' i‖ ≤ (2 * θ) ^ k * r) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, w' i)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ε / 2 / (r + 1) by positivity) hθ1
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 : ℝ) ^ k * r / (ε / 2))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hA : θ ^ k * r < ε / 2 := by
    have h1 : θ ^ k * r ≤ θ ^ k * (r + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hr0]) (pow_nonneg hθ0 k)
    have hpos : (0 : ℝ) < r + 1 := by linarith [hr0]
    have h2 : θ ^ k * (r + 1) < ε / 2 := (lt_div_iff₀ hpos).mp hk
    exact lt_of_le_of_lt h1 h2
  have hB : 2 ^ k * r < ε / 2 * (n : ℝ) := by
    have hN' : 2 ^ k * r / (ε / 2) < (n : ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hnN)
    have hpos2 : (0 : ℝ) < ε / 2 := by linarith
    calc 2 ^ k * r < (n : ℝ) * (ε / 2) := (div_lt_iff₀ hpos2).mp hN'
      _ = ε / 2 * (n : ℝ) := by ring
  have hBterm : (n : ℝ)⁻¹ * (2 ^ k * r) < ε / 2 := by
    rw [show (n : ℝ)⁻¹ * (2 ^ k * r) = (2 ^ k * r) / (n : ℝ) by
      rw [div_eq_mul_inv]; exact mul_comm _ _]
    exact (div_lt_iff₀ hnR).mpr hB
  have hS := bsak_norm_sum_range_le_of_dyadic_blocks hθ0 hr0 hbnd hblock k n
  have hdist : (n : ℝ)⁻¹ * (↑n * θ ^ k * r + 2 ^ k * r)
      = θ ^ k * r + (n : ℝ)⁻¹ * (2 ^ k * r) := by
    have e1 : (n : ℝ)⁻¹ * (↑n * θ ^ k * r) = θ ^ k * r := by
      have e : (n : ℝ)⁻¹ * (↑n * θ ^ k * r)
          = ((n : ℝ)⁻¹ * ↑n) * (θ ^ k * r) := by ring
      rw [e, inv_mul_cancel₀ hnne, one_mul]
    rw [mul_add, e1]
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnR)]
  calc (n : ℝ)⁻¹ * ‖∑ i ∈ Finset.range n, w' i‖
        ≤ (n : ℝ)⁻¹ * (↑n * θ ^ k * r + 2 ^ k * r) :=
          mul_le_mul_of_nonneg_left hS (le_of_lt (inv_pos.mpr hnR))
    _ = θ ^ k * r + (n : ℝ)⁻¹ * (2 ^ k * r) := hdist
    _ < ε / 2 + ε / 2 := add_lt_add hA hBterm
    _ = ε := by ring

/-- Weak-compact superset of a norm ball in a uniformly convex Banach space. -/
private theorem bsak_exists_isCompact_weakSpace_superset_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [UniformConvexSpace E] [CompleteSpace E]
    (M : ℝ) :
    ∃ K : Set (WeakSpace ℝ E), IsCompact K ∧
      ∀ v : E, ‖v‖ ≤ M → toWeakSpace ℝ E v ∈ K := by
  classical
  set pt : WeakDual ℝ (StrongDual ℝ E) → E :=
    fun Φ => Classical.choose
      (MathlibExt.Analysis.FunctionalAnalysis.MilmanPettisWanted.milman_pettis
        (WeakDual.toStrongDual Φ)) with hptdef
  have hpt : ∀ (Φ : WeakDual ℝ (StrongDual ℝ E)) (f : StrongDual ℝ E),
      WeakDual.toStrongDual Φ f = f (pt Φ) := by
    intro Φ f
    exact Classical.choose_spec
      (MathlibExt.Analysis.FunctionalAnalysis.MilmanPettisWanted.milman_pettis
        (WeakDual.toStrongDual Φ)) f
  set T : WeakDual ℝ (StrongDual ℝ E) → WeakSpace ℝ E :=
    fun Φ => toWeakSpace ℝ E (pt Φ) with hTdef
  have hTapp : ∀ Φ, T Φ = toWeakSpace ℝ E (pt Φ) := fun Φ => rfl
  have hcoord : ∀ (f : StrongDual ℝ E) (Φ : WeakDual ℝ (StrongDual ℝ E)),
      f ((toWeakSpace ℝ E).symm (T Φ)) = Φ f := by
    intro f Φ
    rw [hTapp, LinearEquiv.symm_apply_apply, ← hpt Φ f]
    exact (WeakDual.toStrongDual_apply Φ f).symm
  have hTcont : Continuous T := by
    apply WeakBilin.continuous_of_continuous_eval (B := (topDualPairing ℝ E).flip)
    intro f
    have heq : (fun a => ((topDualPairing ℝ E).flip) (T a) f) = (fun a => a f) := by
      funext a
      show ((topDualPairing ℝ E).flip) (T a) f = a f
      calc ((topDualPairing ℝ E).flip) (T a) f
          = f ((toWeakSpace ℝ E).symm (T a)) := rfl
        _ = a f := hcoord f a
    rw [heq]
    exact WeakDual.eval_continuous f
  refine ⟨T '' (WeakDual.toStrongDual ⁻¹'
    (Metric.closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) M)), ?_, ?_⟩
  · exact (WeakDual.isCompact_closedBall 0 M).image hTcont
  · intro v hv
    have hnorm : ‖NormedSpace.inclusionInDoubleDual ℝ E v‖ ≤ M :=
      le_trans (NormedSpace.double_dual_bound ℝ E v) hv
    set Ψ : WeakDual ℝ (StrongDual ℝ E) :=
      StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℝ E v) with hΨdef
    have hΨJ : WeakDual.toStrongDual Ψ =
        NormedSpace.inclusionInDoubleDual ℝ E v :=
      StrongDual.toStrongDual_toWeakDual _
    have hmem : Ψ ∈ WeakDual.toStrongDual ⁻¹'
        (Metric.closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) M) := by
      rw [Set.mem_preimage, hΨJ, Metric.mem_closedBall]
      calc dist (NormedSpace.inclusionInDoubleDual ℝ E v) 0
          = ‖-(NormedSpace.inclusionInDoubleDual ℝ E v) + 0‖ :=
            SeminormedAddCommGroup.dist_eq
              (E := StrongDual ℝ (StrongDual ℝ E)) _ _
        _ = ‖NormedSpace.inclusionInDoubleDual ℝ E v‖ := by
            rw [add_zero]
            exact norm_neg (NormedSpace.inclusionInDoubleDual ℝ E v)
        _ ≤ M := hnorm
    have hTΨ : T Ψ = toWeakSpace ℝ E v := by
      rw [hTapp]
      congr 1
      refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ) (V := E)).mpr ?_
      intro f
      calc f (pt Ψ) = WeakDual.toStrongDual Ψ f := (hpt Ψ f).symm
        _ = NormedSpace.inclusionInDoubleDual ℝ E v f := by rw [hΨJ]
        _ = f v := rfl
    rw [← hTΨ]
    exact Set.mem_image_of_mem _ hmem

/-- Bounded sequences have weakly convergent subsequences. -/
private theorem bsak_exists_subseq_weak_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [UniformConvexSpace E] [CompleteSpace E]
    {x : ℕ → E} {M : ℝ} (hx : ∀ n, ‖x n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : E,
      ∀ f : StrongDual ℝ E,
        Filter.Tendsto (fun j => f (x (φ j))) Filter.atTop (nhds (f y)) := by
  obtain ⟨K, hKcomp, hKmem⟩ :=
    bsak_exists_isCompact_weakSpace_superset_closedBall (E := E) M
  have hseq : IsSeqCompact K :=
    (MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted.eberlein_smulian).mp
      hKcomp
  have hmem : ∀ n, toWeakSpace ℝ E (x n) ∈ K := fun n => hKmem _ (hx n)
  obtain ⟨a, _, φ, hφmono, hlim⟩ := hseq hmem
  refine ⟨φ, hφmono, (toWeakSpace ℝ E).symm a, fun f => ?_⟩
  have hcont : Continuous
      (fun w : WeakSpace ℝ E => f ((toWeakSpace ℝ E).symm w)) :=
    WeakBilin.eval_continuous _ f
  have hcomp := (hcont.tendsto a).comp hlim
  exact hcomp

/-- Kakutani extraction: weak convergence implies Cesàro-norm convergence
along a further subsequence. -/
private theorem bsak_kakutani_cesaro_of_weak_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]
    {x : ℕ → E} {M : ℝ} (hxb : ∀ n, ‖x n‖ ≤ M)
    {y : E}
    (hlim : ∀ f : StrongDual ℝ E,
      Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds (f y))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, x (φ i))
        Filter.atTop (nhds y) := by
  classical
  have hwnull : ∀ f : StrongDual ℝ E,
      Filter.Tendsto (fun n => f (x n - y)) Filter.atTop (nhds 0) := by
    intro f
    have h := (hlim f).sub_const (f y)
    rw [sub_self] at h
    exact h.congr fun n => (map_sub f (x n) y).symm
  set r : ℝ := max M 0 + ‖y‖ + 1 with hrdef
  have hrpos : 0 < r := by
    have h1 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    have h2 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    rw [hrdef]
    linarith
  have hwbnd : ∀ n, ‖x n - y‖ ≤ r := by
    intro n
    calc ‖x n - y‖ ≤ ‖x n‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ M + ‖y‖ := add_le_add (hxb n) le_rfl
      _ ≤ r := by
        have hle : M ≤ max M 0 := le_max_left _ _
        rw [hrdef]
        linarith
  choose F hF using fun (v : E) => exists_dual_vector'' ℝ v
  have hFnorm : ∀ v, ‖F v‖ ≤ 1 := fun v => (hF v).1
  have hFval : ∀ v, F v v = ‖v‖ := by
    intro v
    have h := (hF v).2
    simpa [RCLike.ofReal_real_eq_id] using h
  obtain ⟨θ, hθ34, hθ1, hθ⟩ := bsak_kakutani_two_block (E := E)
  have hθ' : ∀ (R : ℝ), 0 < R → ∀ u v : E, ∀ g : StrongDual ℝ E,
      ‖g‖ ≤ 1 → g u = ‖u‖ → ‖u‖ ≤ R → ‖v‖ ≤ R → |g v| ≤ R / 4 →
      ‖u + v‖ ≤ 2 * θ * R := by
    intro R hR u v g hg1 hgu huR hvR hgv
    apply hθ R hR u v g hg1 hgu huR hvR
    rwa [Real.norm_eq_abs]
  have hη : ∀ j, 0 < r / 8 * (1 / 2 : ℝ) ^ j := fun j =>
    mul_pos (by linarith [hrpos]) (pow_pos (by norm_num) j)
  obtain ⟨φ, hφmono, hsel⟩ := bsak_exists_subseq_kakutani_selection
    (w := fun n => x n - y) hwnull F (fun j => r / 8 * (1 / 2 : ℝ) ^ j) hη
  have hblock : ∀ k m : ℕ,
      ‖∑ i ∈ Finset.Ico (m * 2 ^ k) ((m + 1) * 2 ^ k), (x (φ i) - y)‖ ≤
        (2 * θ) ^ k * r :=
    bsak_kakutani_dyadic_block_bound hθ34 hθ' hrpos hFnorm hFval hsel
      (fun i => hwbnd (φ i))
  have hθ0 : 0 ≤ θ := by linarith [hθ34]
  have hces : Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (x (φ i) - y))
      Filter.atTop (nhds 0) :=
    bsak_tendsto_cesaro_zero_of_dyadic_blocks hθ0 hθ1 hrpos.le
      (fun i => hwbnd (φ i)) hblock
  have hev : (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, x (φ i)) =ᶠ[
      Filter.atTop]
      (fun n : ℕ => ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (x (φ i) - y)) + y) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast lt_of_lt_of_le zero_lt_one hn
      exact ne_of_gt hnpos
    have hS : (∑ i ∈ Finset.range n, (x (φ i) - y))
        = (∑ i ∈ Finset.range n, x (φ i)) - n • y := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have hS2 : (∑ i ∈ Finset.range n, x (φ i))
        = (∑ i ∈ Finset.range n, (x (φ i) - y)) + n • y := by
      rw [hS, sub_add_cancel]
    have hny : (n : ℝ)⁻¹ • (n • y) = y := by
      rw [← Nat.cast_smul_eq_nsmul (R := ℝ), inv_smul_smul₀ hn0]
    rw [hS2, smul_add, hny]
  refine ⟨φ, hφmono, ?_⟩
  have hadd := hces.add_const y
  rw [zero_add] at hadd
  exact Filter.Tendsto.congr' hev.symm hadd

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.BanachSaksWanted

/--
**Banach–Saks theorem for uniformly convex spaces.** Let $E$ be a uniformly convex real Banach
space and let $(x_n)_{n \in \mathbb{N}}$ be a bounded sequence in $E$. Then there are a strictly
increasing map $\varphi : \mathbb{N} \to \mathbb{N}$ and a point $y \in E$ such that the Cesàro
means $\frac{1}{n} \sum_{i=0}^{n-1} x_{\varphi(i)}$ converge to $y$ in norm as $n \to \infty$.

Proves `Wanted` entry `banach_saks`.

Source: S. Banach and S. Saks, Studia Math. 2 (1930) 51-57;
uniformly convex form and property due to Kakutani, 1939; textbook Diestel, Sequences and Series
in Banach Spaces; Lean gives uniformly convex real Banach specialization with explicit `StrictMono
φ` and norm-convergent Cesàro means.
-/
public theorem banach_saks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E] [CompleteSpace E]
    {x : ℕ → E} (hx : Bornology.IsBounded (Set.range x)) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (y : E),
      Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, x (φ i)) Filter.atTop (nhds y)
      := by
  obtain ⟨M, hM⟩ := hx.exists_norm_le
  have hb : ∀ n, ‖x n‖ ≤ M := fun n => hM (x n) ⟨n, rfl⟩
  obtain ⟨φ₁, hφ₁, y, hlim⟩ := bsak_exists_subseq_weak_tendsto (E := E) hb
  obtain ⟨φ₂, hφ₂, hces⟩ :=
    bsak_kakutani_cesaro_of_weak_tendsto (fun n => hb (φ₁ n)) hlim
  exact ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, y, hces⟩

end MathlibExt.Analysis.FunctionalAnalysis.BanachSaksWanted
