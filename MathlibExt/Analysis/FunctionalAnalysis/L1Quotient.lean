/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Lp.lpHolder

@[expose] public section

/-!
# Separable Banach spaces are quotients of `ℓ¹`

Every separable real Banach space is the image of a surjective bounded linear map from
`lp (fun _ : ℕ => ℝ) 1`.
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.L1Quotient

/-- Radial projection of `E` into its open unit ball. -/
private noncomputable def rho {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : E :=
  (1 + ‖v‖)⁻¹ • v

/-- The radial projection is continuous. -/
private lemma rho_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (rho : E → E) := by
  have h1 : Continuous (fun v : E => (1 + ‖v‖ : ℝ)) :=
    continuous_const.add continuous_norm
  have h2 : ∀ v : E, (1 + ‖v‖ : ℝ) ≠ 0 := fun v => by positivity
  have h3 : Continuous (fun v : E => ((1 + ‖v‖ : ℝ))⁻¹) := h1.inv₀ h2
  unfold rho
  exact h3.smul continuous_id

/-- Every point of the open unit ball is hit by the radial projection. -/
private lemma rho_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : E} (hw : ‖w‖ < 1) : rho ((1 - ‖w‖)⁻¹ • w) = w := by
  have h1 : (0 : ℝ) < 1 - ‖w‖ := sub_pos.mpr hw
  have h1ne : (1 : ℝ) - ‖w‖ ≠ 0 := ne_of_gt h1
  have hnorm : ‖(1 - ‖w‖)⁻¹ • w‖ = (1 - ‖w‖)⁻¹ * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1)]
  have h2 : (1 : ℝ) + (1 - ‖w‖)⁻¹ * ‖w‖ = (1 - ‖w‖)⁻¹ := by
    field_simp
    ring
  change (1 + ‖(1 - ‖w‖)⁻¹ • w‖)⁻¹ • ((1 - ‖w‖)⁻¹ • w) = w
  rw [hnorm, h2, inv_inv, smul_inv_smul₀ h1ne]

/-- Points of the closed unit ball are approximable by `rho` of a dense sequence. -/
private lemma exists_approx_unit_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ → E) (hd : DenseRange d) {w : E} (hw : ‖w‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ‖w - rho (d n)‖ < ε := by
  have hw1 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  set δ : ℝ := min (1 / 2) (ε / (2 * (‖w‖ + 1))) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  set w' : E := (1 - δ) • w with hw'
  have h1δ : (0 : ℝ) ≤ 1 - δ := by linarith
  have hle : δ * ‖w‖ ≤ (ε / (2 * (‖w‖ + 1))) * ‖w‖ :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hw1
  have hlt : (ε / (2 * (‖w‖ + 1))) * ‖w‖ < ε / 2 := by
    have h2pos : (0 : ℝ) < 2 * (‖w‖ + 1) := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ h2pos]
    have h3 : ε / 2 * (2 * (‖w‖ + 1)) = ε * (‖w‖ + 1) := by ring
    rw [h3]
    exact mul_lt_mul_of_pos_left (by linarith) hε
  have hww' : ‖w - w'‖ < ε / 2 := by
    have heq : w - w' = δ • w := by rw [hw']; module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hδpos)]
    exact lt_of_le_of_lt hle hlt
  have hw'norm : ‖w'‖ < 1 := by
    rw [hw', norm_smul, Real.norm_eq_abs, abs_of_nonneg h1δ]
    calc (1 - δ) * ‖w‖ ≤ (1 - δ) * 1 :=
          mul_le_mul_of_nonneg_left hw h1δ
      _ = 1 - δ := mul_one _
      _ < 1 := by linarith
  set v : E := (1 - ‖w'‖)⁻¹ • w' with hv
  have hρv : rho v = w' := by rw [hv]; exact rho_mem hw'norm
  have hcont : ContinuousAt rho v := rho_continuous.continuousAt
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    Metric.continuousAt_iff.mp hcont (ε / 2) (half_pos hε)
  have hmem : v ∈ closure (Set.range d) := by
    rw [hd.closure_range]
    exact Set.mem_univ v
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨-, ⟨n, rfl⟩, hn⟩ := hmem δ₂ hδ₂pos
  have hclose : dist w' (rho (d n)) < ε / 2 := by
    rw [dist_comm, ← hρv]
    exact hδ₂ (by rwa [dist_comm])
  refine ⟨n, ?_⟩
  rw [← dist_eq_norm]
  calc dist w (rho (d n)) ≤ dist w w' + dist w' (rho (d n)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by rwa [dist_eq_norm]) hclose
    _ = ε := add_halves ε

/--
**Separable real Banach spaces are quotients of ℓ¹.** For every separable real Banach space $E$
there is a surjective bounded linear operator $T \colon \ell^1(\mathbb{N}, \mathbb{R}) \to E$.

Proves `Wanted` entry `separableRealBanach_quotient_l1`.

Source: S. Banach, Theorie des operations
lineaires, 1932, `ℓ¹` quotient theorem; Albiac and Kalton, Topics in Banach Space Theory; Lean
states separable real Banach specialization with concrete `lp _ 1` domain and surjective bounded
linear quotient.
-/
theorem separableRealBanach_quotient_l1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ (T : lp (fun _ : ℕ => ℝ) 1 →L[ℝ] E), Function.Surjective T := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq E
  set x : ℕ → E := rho ∘ d with hx
  have hnx : ∀ n, x n = rho (d n) := fun n => rfl
  have hxnorm : ∀ n, ‖x n‖ ≤ 1 := by
    intro n
    have hpos : (0 : ℝ) < 1 + ‖d n‖ := by positivity
    have hnn : (0 : ℝ) ≤ (1 + ‖d n‖)⁻¹ := le_of_lt (inv_pos.mpr hpos)
    have e1 : x n = (1 + ‖d n‖)⁻¹ • d n := rfl
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    calc (1 + ‖d n‖)⁻¹ * ‖d n‖ ≤ (1 + ‖d n‖)⁻¹ * (1 + ‖d n‖) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hnn
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have : Fact ((1 : ENNReal) ≤ 1) := ⟨le_rfl⟩
  set G : (i : ℕ) → ((fun _ : ℕ => ℝ) i →L[ℝ] (fun _ : ℕ => E) i) :=
    fun i => (ContinuousLinearMap.id ℝ ℝ).smulRight (x i) with hG
  have hGnorm : ∀ i, ‖G i‖ ≤ 1 := by
    intro i
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c => ?_
    have e2 : G i c = c • x i := by
      rw [hG]
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    rw [e2, norm_smul, Real.norm_eq_abs]
    calc |c| * ‖x i‖ ≤ |c| * 1 := mul_le_mul_of_nonneg_left (hxnorm i) (abs_nonneg _)
      _ = 1 * ‖c‖ := by rw [Real.norm_eq_abs]; ring
  set Φ : lp (fun _ : ℕ => ℝ) 1 →L[ℝ] lp (fun _ : ℕ => E) 1 :=
    lp.mapCLM (1 : ENNReal) G zero_le_one hGnorm with hΦ
  set T : lp (fun _ : ℕ => ℝ) 1 →L[ℝ] E := (lp.tsumCLM ℝ ℕ E).comp Φ with hT
  refine ⟨T, ?_⟩
  have hTapply : ∀ f : lp (fun _ : ℕ => ℝ) 1, T f = ∑' i, (f i : ℝ) • x i := by
    intro f
    rw [hT, hΦ, ContinuousLinearMap.comp_apply, lp.tsumCLM_apply]
    simp only [lp.mapCLM_apply_coe, hG, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply]
  have hTsingle : ∀ (n : ℕ) (c : ℝ), T (lp.single 1 n c) = c • x n := by
    intro n c
    have hfn : ∀ b : ℕ, b ≠ n → (((lp.single 1 n c : lp (fun _ : ℕ => ℝ) 1) b : ℝ)) • x b = 0 := by
      intro b hb
      rw [lp.coeFn_single, Pi.single_apply]
      simp [hb]
    rw [hTapply, tsum_eq_single n hfn, lp.coeFn_single, Pi.single_apply]
    simp
  have step : ∀ (e : E) (m : ℕ), ∃ (n : ℕ) (e' : E),
      (‖e‖ ≤ ((2 ^ m : ℝ))⁻¹ → ‖e'‖ ≤ ((2 ^ (m + 1) : ℝ))⁻¹ ∧ e' = e - ((2 ^ m : ℝ))⁻¹ • x n) := by
    intro e m
    by_cases he : ‖e‖ ≤ ((2 ^ m : ℝ))⁻¹
    · have h2m : (0 : ℝ) < 2 ^ m := by positivity
      have h2mne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt h2m
      set r : E := (2 ^ m : ℝ) • e with hr
      have hr1 : ‖r‖ ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left he (le_of_lt h2m)
        rw [mul_inv_cancel₀ h2mne] at h
        rw [hr, norm_smul, Real.norm_eq_abs, abs_of_pos h2m]
        exact h
      obtain ⟨n, hn⟩ := exists_approx_unit_ball d hd hr1 (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [← hnx n] at hn
      refine ⟨n, e - ((2 ^ m : ℝ))⁻¹ • x n, fun _ => ⟨?_, rfl⟩⟩
      have hsplit : e - ((2 ^ m : ℝ))⁻¹ • x n = ((2 ^ m : ℝ))⁻¹ • (r - x n) := by
        rw [hr, smul_sub, ← mul_smul, inv_mul_cancel₀ h2mne, one_smul]
      rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h2m)]
      have hnm : ((2 ^ (m + 1) : ℝ))⁻¹ = ((2 ^ m : ℝ))⁻¹ * (1 / 2) := by
        rw [pow_succ, mul_inv]
        congr 1
        norm_num
      rw [hnm]
      exact le_of_lt (mul_lt_mul_of_pos_left hn (inv_pos.mpr h2m))
    · exact ⟨0, 0, fun h => absurd h he⟩
  choose nseq eseq hseq using step
  have main : ∀ z : E, ‖z‖ < 1 → ∃ a, T a = z := by
    intro z hz
    set e : ℕ → E := fun m => Nat.rec z (fun m ih => eseq ih m) m with he
    set nn : ℕ → ℕ := fun m => nseq (e m) m with hnn
    set g : ℕ → E := fun j => ((2 ^ j : ℝ))⁻¹ • x (nn j) with hg
    have he0 : e 0 = z := rfl
    have hes : ∀ m, e (m + 1) = eseq (e m) m := fun m => rfl
    have hnnm : ∀ m, nn m = nseq (e m) m := fun m => rfl
    have hgm : ∀ j, g j = ((2 ^ j : ℝ))⁻¹ • x (nn j) := fun j => rfl
    have hres : ∀ m, ‖e m‖ ≤ ((2 ^ m : ℝ))⁻¹ ∧
        e m = z - ∑ j ∈ Finset.range m, g j := by
      intro m
      induction m with
      | zero =>
        refine ⟨?_, ?_⟩
        · rw [he0]
          simp only [pow_zero, inv_one]
          exact le_of_lt hz
        · rw [he0, Finset.sum_range_zero, sub_zero]
      | succ m ih =>
        obtain ⟨ihb, ihe⟩ := ih
        have hstep := hseq (e m) m ihb
        have eSm : e (m + 1) = eseq (e m) m := hes m
        refine ⟨?_, ?_⟩
        · rw [eSm]
          exact hstep.1
        · rw [eSm, hstep.2, ← hnnm m, ihe, Finset.sum_range_succ, hgm m, sub_sub]
    have hpow : ∀ j : ℕ, (((2 ^ j : ℝ))⁻¹) = ((1 / 2 : ℝ) ^ j) := by
      intro j
      rw [← inv_pow]
      congr 1
      norm_num
    have hgsumm : Summable g := by
      apply Summable.of_norm
      refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) summable_geometric_two
      rw [hgm j, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
      calc ((2 ^ j : ℝ))⁻¹ * ‖x (nn j)‖ ≤ ((2 ^ j : ℝ))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (hxnorm _) (le_of_lt (inv_pos.mpr (by positivity)))
        _ = (1 / 2) ^ j := by rw [mul_one]; exact hpow j
    set h : ℕ → lp (fun _ : ℕ => ℝ) 1 :=
      fun j => ((2 ^ j : ℝ))⁻¹ • lp.single 1 (nn j) 1 with hh
    have hhj : ∀ j, h j = ((2 ^ j : ℝ))⁻¹ • lp.single 1 (nn j) 1 := fun j => rfl
    have hhsumm : Summable h := by
      apply Summable.of_norm
      refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) summable_geometric_two
      rw [hhj j, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity)),
        lp.norm_single (show (0 : ENNReal) < 1 by exact zero_lt_one) _ _, norm_one, mul_one]
      exact le_of_eq (hpow j)
    set a : lp (fun _ : ℕ => ℝ) 1 := ∑' j, h j with ha
    refine ⟨a, ?_⟩
    have hTa : T a = ∑' j, g j := by
      have h1 : T a = ∑' j, T (h j) := by
        rw [ha]
        exact T.map_tsum hhsumm
      have h2 : (fun j => T (h j)) = g := by
        funext j
        rw [hhj j, hgm j, map_smul, hTsingle, one_smul]
      rw [h1, h2]
    rw [hTa]
    have h0 : Filter.Tendsto (fun m : ℕ => ((2 ^ m : ℝ))⁻¹) Filter.atTop (nhds 0) := by
      have heq : (fun m : ℕ => ((2 ^ m : ℝ))⁻¹) = (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
        funext fun m => hpow m
      rw [heq]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hSz : Filter.Tendsto (fun m => (∑ j ∈ Finset.range m, g j) - z) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun m => ?_) h0
      have hm := (hres m).2
      have hme : (∑ j ∈ Finset.range m, g j) - z = -(e m) := by
        rw [hm]
        exact (neg_sub z _).symm
      rw [hme, norm_neg]
      exact (hres m).1
    have hlim : Filter.Tendsto (fun m => ∑ j ∈ Finset.range m, g j) Filter.atTop (nhds z) := by
      have h := hSz.add_const z
      simpa using h
    exact tendsto_nhds_unique hgsumm.hasSum.tendsto_sum_nat hlim
  intro y
  set c : ℝ := ‖y‖ + 1 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hclt : ‖y‖ < c := by rw [hc]; exact lt_add_one _
  set z : E := c⁻¹ • y with hz
  have hznorm : ‖z‖ < 1 := by
    have h := mul_lt_mul_of_pos_left hclt (inv_pos.mpr hcpos)
    rw [inv_mul_cancel₀ (ne_of_gt hcpos)] at h
    rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    exact h
  obtain ⟨b, hb⟩ := main z hznorm
  refine ⟨c • b, ?_⟩
  rw [map_smul, hb, hz, smul_inv_smul₀ (ne_of_gt hcpos)]

end MathlibExt.Analysis.FunctionalAnalysis.L1Quotient
