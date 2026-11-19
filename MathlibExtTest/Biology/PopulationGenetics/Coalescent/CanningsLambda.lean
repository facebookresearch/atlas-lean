/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsLambda
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Tests for Cannings models converging to Λ-coalescents

All three cases use one family of Cannings models, the **sweepstake model** `sweepstake N m ε`
(an Eldon–Wakeley-type model, Eldon–Wakeley 2006): with probability `ε` one parent has `m`
offspring and every other parent at most one; otherwise every parent has exactly one offspring.
Its merger probabilities are computed from the definitions (`mergeProb_sweepstake`:
`q_k = ε (m)_k / (N)_k`), as is the absence of simultaneous mergers
(`doubleMergeProb_sweepstake`).

* **Heavy tail** (`heavy`, `m = ⌊N/2⌋`, `ε = 1/(N+1)`): the Möhle–Sagitov conditions hold with
  `Λ = δ_{1/2}`, determined by `q_k / c_N → (1/2)^(k-2)`; the model is heavy-tailed, so the
  ancestral lineage count converges to the Λ-coalescent with multiple mergers.
* **Kingman boundary** (`moran`, `m = 2`, `ε = 1`, a Moran-type model): the conditions hold
  with `Λ = δ₀`, the model is not heavy-tailed, and the Λ statement reduces to Kingman's
  pure-death limit.
* **Violated hypothesis** (`clonal`, `m = N`, `ε = 1`): every generation is one family, so
  `c_N = 1` does not tend to `0`; no Λ satisfies the Möhle–Sagitov conditions and no
  convergence is claimed.
-/

@[expose] public section

noncomputable section

open Finset Filter Topology MeasureTheory unitInterval
open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsLambda
open MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsLambda.CanningsModel

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.CanningsLambda

/-! ### The sweepstake model -/

/-- One parent has `m` offspring and every other parent at most one. -/
def IsFamily {N : ℕ} (m : ℕ) (f : Fin N → Fin N) : Prop :=
  ∃ p, offspring f p = m ∧ ∀ q, q ≠ p → offspring f q ≤ 1

instance {N m : ℕ} : DecidablePred (IsFamily (N := N) m) := fun f => by
  unfold IsFamily; infer_instance

/-- The number of family maps. -/
def famCard (N m : ℕ) : ℕ := #(univ.filter (IsFamily (N := N) m))

/-- The number of injective (one-offspring-each) maps. -/
def injCard (N : ℕ) : ℕ := #(univ.filter fun f : Fin N → Fin N => Function.Injective f)

/-- The weight of the family event: `ε`, or `0` when no family map exists. -/
def famWeight (N m : ℕ) (ε : ℝ) : ℝ := if 0 < famCard N m then ε else 0

/-- The sweepstake law: uniform over injective maps with weight `1 - ε`, uniform over family
maps with weight `ε`. -/
def sweepstakeLaw (N m : ℕ) (ε : ℝ) (f : Fin N → Fin N) : ℝ :=
  (1 - famWeight N m ε) * (if Function.Injective f then 1 else 0) / injCard N +
    famWeight N m ε * (if IsFamily m f then 1 else 0) / famCard N m

lemma injCard_pos (N : ℕ) : 0 < injCard N :=
  card_pos.2 ⟨id, mem_filter.2 ⟨mem_univ _, Function.injective_id⟩⟩

lemma isFamily_comp_perm {N m : ℕ} (f : Fin N → Fin N) (τ : Equiv.Perm (Fin N)) :
    IsFamily m (f ∘ τ) ↔ IsFamily m f := by
  simp only [IsFamily, offspring_comp_perm]

lemma isFamily_perm_comp {N m : ℕ} (f : Fin N → Fin N) (ρ : Equiv.Perm (Fin N)) :
    IsFamily m (ρ ∘ f) ↔ IsFamily m f := by
  simp only [IsFamily, offspring_perm_comp]
  constructor
  · rintro ⟨p, hp, hq⟩
    refine ⟨ρ.symm p, hp, fun q hqp => ?_⟩
    have := hq (ρ q) fun h => hqp (by rw [← h]; simp)
    simpa using this
  · rintro ⟨p, hp, hq⟩
    refine ⟨ρ p, by simpa using hp, fun q hqp => hq _ fun h => hqp (by rw [← h]; simp)⟩

lemma sweepstakeLaw_nonneg {N m : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (f : Fin N → Fin N) :
    0 ≤ sweepstakeLaw N m ε f := by
  have hw0 : 0 ≤ famWeight N m ε := by unfold famWeight; split_ifs <;> linarith
  have hw1 : famWeight N m ε ≤ 1 := by unfold famWeight; split_ifs <;> linarith
  unfold sweepstakeLaw
  refine add_nonneg (div_nonneg (mul_nonneg (by linarith) ?_) (Nat.cast_nonneg _))
    (div_nonneg (mul_nonneg hw0 ?_) (Nat.cast_nonneg _)) <;> split_ifs <;> norm_num

lemma sum_sweepstakeLaw (N m : ℕ) (ε : ℝ) : ∑ f, sweepstakeLaw N m ε f = 1 := by
  simp only [sweepstakeLaw, sum_add_distrib, ← sum_div, ← mul_sum, sum_boole]
  have hI : ((injCard N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (injCard_pos N).ne'
  rw [show (#(univ.filter fun f : Fin N → Fin N => Function.Injective f) : ℝ) = injCard N from
    rfl, show (#(univ.filter (IsFamily (N := N) m)) : ℝ) = famCard N m from rfl,
    mul_div_assoc, div_self hI, mul_one]
  unfold famWeight
  split_ifs with hF
  · rw [mul_div_assoc, div_self (by exact_mod_cast hF.ne'), mul_one]
    ring
  · simp

/-- The sweepstake Cannings model, its law built with `PMF.ofFintype` from `sweepstakeLaw`. -/
def sweepstake (N m : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : CanningsModel N where
  law := PMF.ofFintype (fun f => ENNReal.ofReal (sweepstakeLaw N m ε f)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun f _ => sweepstakeLaw_nonneg hε0 hε1 f,
      sum_sweepstakeLaw, ENNReal.ofReal_one])
  law_comp_perm τ f := by
    simp only [PMF.ofFintype_apply, sweepstakeLaw, isFamily_comp_perm, Equiv.injective_comp]
  law_perm_comp ρ f := by
    simp only [PMF.ofFintype_apply, sweepstakeLaw, isFamily_perm_comp, Equiv.comp_injective]

/-- The real masses of the sweepstake model are `sweepstakeLaw`. -/
lemma toReal_law_sweepstake {N m : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (f : Fin N → Fin N) :
    ((sweepstake N m ε hε0 hε1).law f).toReal = sweepstakeLaw N m ε f :=
  ENNReal.toReal_ofReal (sweepstakeLaw_nonneg hε0 hε1 f)

/-- A family map exists when `1 ≤ m ≤ N`: children `0, …, m - 1` have parent `0`, every other
child is its own parent. -/
lemma famCard_pos {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) : 0 < famCard N m := by
  set z : Fin N := ⟨0, by omega⟩
  set f : Fin N → Fin N := fun c => if (c : ℕ) < m then z else c with hf
  refine card_pos.2 ⟨f, mem_filter.2 ⟨mem_univ _, z, ?_, fun q hq => ?_⟩⟩
  · have : (univ.filter fun c => f c = z) = univ.filter fun c : Fin N => (c : ℕ) < m := by
      refine filter_congr fun c _ => ?_
      by_cases hc : (c : ℕ) < m
      · simp [hf, hc]
      · simp only [hf, hc, ite_false, iff_false]
        intro h
        exact hc (by rw [h]; simp [z]; omega)
    rw [offspring, this, Fin.card_filter_val_lt, min_eq_right hmN]
  · refine card_le_one.2 fun a ha b hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    have key : ∀ c, f c = q → c = q := fun c hc => by
      by_cases h : (c : ℕ) < m
      · simp only [hf, h, ite_true] at hc
        exact absurd hc.symm hq
      · simpa [hf, h] using hc
    rw [key a ha, key b hb]

lemma famWeight_eq {N m : ℕ} {ε : ℝ} (hm : 1 ≤ m) (hmN : m ≤ N) : famWeight N m ε = ε := by
  simp [famWeight, famCard_pos hm hmN]

lemma offspring_le_one_of_injective {N : ℕ} {f : Fin N → Fin N} (hf : Function.Injective f)
    (i : Fin N) : offspring f i ≤ 1 :=
  card_le_one.2 fun _ ha _ hb => hf ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm)

lemma sum_descFactorial_of_injective {N k : ℕ} {f : Fin N → Fin N}
    (hf : Function.Injective f) (hk : 2 ≤ k) :
    ∑ i, ((offspring f i).descFactorial k : ℝ) = 0 :=
  sum_eq_zero fun i _ => by
    rw [Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt]
    have := offspring_le_one_of_injective hf i
    omega

lemma sum_descFactorial_of_isFamily {N m k : ℕ} {f : Fin N → Fin N} (hf : IsFamily m f)
    (hk : 2 ≤ k) : ∑ i, ((offspring f i).descFactorial k : ℝ) = m.descFactorial k := by
  obtain ⟨p, hp, hq⟩ := hf
  rw [sum_eq_single p (fun q _ hqp => by
    rw [Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt]
    have := hq q hqp
    omega) (by simp), hp]

/-- **Merger probabilities of the sweepstake model**, from the definitions:
`q_k = ε (m)_k / (N)_k` for `2 ≤ k ≤ N` and `2 ≤ m ≤ N`. -/
theorem mergeProb_sweepstake {N m k : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hm : 2 ≤ m)
    (hmN : m ≤ N) (hk : 2 ≤ k) (hkN : k ≤ N) :
    (sweepstake N m ε hε0 hε1).mergeProb k = ε * m.descFactorial k / N.descFactorial k := by
  have hNk : (N.descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 hkN).ne'
  rw [eq_div_iff hNk, mergeProb_mul_descFactorial _ (by omega)]
  have hF : ((famCard N m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (famCard_pos (by omega) hmN).ne'
  have hpt : ∀ f : Fin N → Fin N, ((sweepstake N m ε hε0 hε1).law f).toReal *
      ∑ i, ((offspring f i).descFactorial k : ℝ) =
      ε * m.descFactorial k / famCard N m * if IsFamily m f then 1 else 0 := by
    intro f
    rw [toReal_law_sweepstake, sweepstakeLaw, famWeight_eq (by omega) hmN]
    by_cases hfam : IsFamily m f
    · have hinj : ¬ Function.Injective f := fun hinj => by
        obtain ⟨p, hp, -⟩ := hfam
        have := offspring_le_one_of_injective hinj p
        omega
      simp only [hinj, hfam, ite_true, ite_false, sum_descFactorial_of_isFamily hfam hk, mul_zero,
        zero_div, zero_add, mul_one]
      field_simp
    · by_cases hinj : Function.Injective f
      · simp [hfam, sum_descFactorial_of_injective hinj hk]
      · simp [hfam, hinj]
  rw [sum_congr rfl fun f _ => hpt f, ← mul_sum, sum_boole]
  change _ * ((famCard N m : ℕ) : ℝ) = _
  field_simp

/-- Two different parents with at least two offspring each are impossible in a sweepstake
generation. -/
lemma offspring_le_one_or {N m : ℕ} {ε : ℝ} {hε0 : 0 ≤ ε} {hε1 : ε ≤ 1}
    {f : Fin N → Fin N} (hf : ((sweepstake N m ε hε0 hε1).law f).toReal ≠ 0) {p p' : Fin N}
    (hpp' : p ≠ p') : offspring f p ≤ 1 ∨ offspring f p' ≤ 1 := by
  rw [toReal_law_sweepstake] at hf
  by_cases hinj : Function.Injective f
  · exact Or.inl (offspring_le_one_of_injective hinj p)
  · by_cases hfam : IsFamily m f
    · obtain ⟨r, -, hr⟩ := hfam
      by_cases hpr : p = r
      · exact Or.inr (hr p' (hpr ▸ hpp'.symm))
      · exact Or.inl (hr p hpr)
    · exact absurd (by simp [sweepstakeLaw, hinj, hfam]) hf

/-- **No simultaneous mergers in the sweepstake model**, from the definitions. -/
theorem doubleMergeProb_sweepstake {N m : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (sweepstake N m ε hε0 hε1).doubleMergeProb = 0 := by
  unfold doubleMergeProb sampleProb
  split_ifs with h4
  · refine sum_eq_zero fun f _ => ?_
    by_cases hf : ((sweepstake N m ε hε0 hε1).law f).toReal = 0
    · rw [hf, zero_mul]
    rw [ite_eq_right ?_, mul_zero]
    rintro ⟨h01, h23, h02⟩
    simp only [Function.comp_apply] at h01 h23 h02
    have two : ∀ a b : Fin 4, a ≠ b → f (Fin.castLE h4 a) = f (Fin.castLE h4 b) →
        2 ≤ offspring f (f (Fin.castLE h4 a)) := by
      intro a b hab heq
      have hne : Fin.castLE h4 a ≠ Fin.castLE h4 b := fun h => hab (Fin.castLE_injective h4 h)
      calc 2 = #({Fin.castLE h4 a, Fin.castLE h4 b} : Finset (Fin N)) := (card_pair hne).symm
        _ ≤ _ := card_le_card fun c hc => by
          simp only [mem_insert, mem_singleton] at hc
          rcases hc with rfl | rfl <;> simp [heq]
    have hA := two 0 1 (by decide) h01
    have hB := two 2 3 (by decide) h23
    rcases offspring_le_one_or hf h02 with h | h <;> omega
  · rfl


/-! ### Limits of falling-factorial ratios -/

/-- If `a N, b N → ∞` and `a N / b N → ψ`, then `(a N)_j / (b N)_j → ψ ^ j`. -/
lemma tendsto_descFactorial_div {a b : ℕ → ℕ} (ha : Tendsto a atTop atTop)
    (hb : Tendsto b atTop atTop) {ψ : ℝ} (hab : Tendsto (fun N => (a N : ℝ) / b N) atTop (𝓝 ψ))
    (j : ℕ) :
    Tendsto (fun N => ((a N).descFactorial j : ℝ) / (b N).descFactorial j) atTop (𝓝 (ψ ^ j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjb : Tendsto (fun N => (j : ℝ) / b N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hb)
    have hstep : Tendsto (fun N => ((a N : ℝ) / b N - j / b N) / (1 - j / b N)) atTop
        (𝓝 ((ψ - 0) / (1 - 0))) :=
      (hab.sub hjb).div (tendsto_const_nhds.sub hjb) (by norm_num)
    rw [sub_zero, sub_zero, div_one] at hstep
    rw [pow_succ]
    refine (ih.mul hstep).congr' ?_
    filter_upwards [ha.eventually_ge_atTop j, hb.eventually_gt_atTop j] with N haN hbN
    have hb0 : (b N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hbj : (b N : ℝ) - j ≠ 0 := by
      have : (j : ℝ) < b N := by exact_mod_cast hbN
      linarith
    have hbd : ((b N).descFactorial j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.2 hbN.le).ne'
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub haN, Nat.cast_sub hbN.le]
    field_simp

/-- The ratio `q_k / c_N` of a sweepstake model with `ε > 0`. -/
lemma mergeProb_div_coalProb_sweepstake {N m k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : 2 ≤ m) (hmN : m ≤ N) (hk : 2 ≤ k) (hkN : k ≤ N) :
    (sweepstake N m ε hε.le hε1).mergeProb k / (sweepstake N m ε hε.le hε1).coalProb =
      ((m.descFactorial k : ℝ) / N.descFactorial k) /
        ((m.descFactorial 2 : ℝ) / N.descFactorial 2) := by
  have h1 : (N.descFactorial k : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.2 hkN).ne'
  have h2 : (N.descFactorial 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 (by omega : 2 ≤ N)).ne'
  have h3 : (m.descFactorial 2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.2 hm).ne'
  have h4 : ε ≠ 0 := hε.ne'
  rw [coalProb, mergeProb_sweepstake _ _ hm hmN hk hkN,
    mergeProb_sweepstake _ _ hm hmN le_rfl (by omega)]
  field_simp

/-! ### Heavy tail: `m = ⌊N/2⌋`, `ε = 1/(N+1)`, limit `Λ = δ_{1/2}` -/

lemma inv_succ_le_one (N : ℕ) : 1 / ((N : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [N.cast_nonneg (α := ℝ)]

/-- The heavy-tailed sweepstake model: with probability `1/(N+1)`, one parent has `⌊N/2⌋`
offspring. -/
def heavy (N : ℕ) : CanningsModel N :=
  sweepstake N (N / 2) (1 / ((N : ℝ) + 1)) (by positivity) (inv_succ_le_one N)

/-- The point `1/2` of the unit interval. -/
def half : I := ⟨1 / 2, by constructor <;> norm_num⟩

lemma tendsto_half_div : Tendsto (fun N : ℕ => ((N / 2 : ℕ) : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  have hlow : Tendsto (fun N : ℕ => 1 / 2 - 1 / (2 * (N : ℝ))) atTop (𝓝 (1 / 2 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)))
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : N ≤ 2 * (N / 2) + 1)
    rw [le_div_iff₀ hN']
    field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : 2 * (N / 2) ≤ N)
    rw [div_le_iff₀ hN']
    linarith

lemma tendsto_div_two_atTop : Tendsto (fun N : ℕ => N / 2) atTop atTop :=
  tendsto_atTop_atTop.2 fun B => ⟨2 * B, fun N hN => by omega⟩

/-- `q_k / c_N → (1/2)^(k-2)` for the heavy model, computed from the definitions. -/
lemma tendsto_heavy_mergeProb_div {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun N => (heavy N).mergeProb k / (heavy N).coalProb) atTop
      (𝓝 ((1 / 2 : ℝ) ^ (k - 2))) := by
  have hlim := (tendsto_descFactorial_div tendsto_div_two_atTop tendsto_id tendsto_half_div k).div
    (tendsto_descFactorial_div tendsto_div_two_atTop tendsto_id tendsto_half_div 2)
    (by norm_num)
  rw [show ((1 : ℝ) / 2) ^ k / (1 / 2) ^ 2 = (1 / 2) ^ (k - 2) by
    rw [div_eq_mul_inv, ← pow_sub₀ _ (by norm_num) hk]] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (max 4 k)] with N hN
  simp only [Pi.div_apply, id]
  exact (mergeProb_div_coalProb_sweepstake (by positivity) (inv_succ_le_one N) (by omega)
    (by omega) hk (by omega)).symm

/-- **The heavy model satisfies the Möhle–Sagitov conditions with `Λ = δ_{1/2}`**: Λ is determined
by the offspring law through `q_k / c_N → (1/2)^(k-2) = ∫ x ^ (k-2) δ_{1/2}(dx)`. -/
theorem mohleSagitovLambda_heavy : MohleSagitovLambda heavy (Measure.dirac half) where
  eventually_coalProb_pos := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    rw [heavy, coalProb, mergeProb_sweepstake _ _ (by omega) (by omega) le_rfl (by omega)]
    have h1 : 0 < ((N / 2).descFactorial 2 : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.2 (by omega)
    have h2 : 0 < (N.descFactorial 2 : ℝ) := by exact_mod_cast Nat.descFactorial_pos.2 (by omega)
    positivity
  tendsto_coalProb := by
    have hε : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := hε.mul (tendsto_descFactorial_div tendsto_div_two_atTop tendsto_id
      tendsto_half_div 2)
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 4] with N hN
    rw [heavy, coalProb, mergeProb_sweepstake _ _ (by omega) (by omega) le_rfl (by omega),
      mul_div_assoc]
    rfl
  tendsto_mergeProb_div k hk := by
    rw [integral_dirac]
    exact tendsto_heavy_mergeProb_div hk
  tendsto_doubleMergeProb_div := by
    refine tendsto_const_nhds.congr fun N => ?_
    rw [heavy, doubleMergeProb_sweepstake, zero_div]

/-- **The heavy model is heavy-tailed**, from the definitions: `q_3 / c_N → 1/2 > 0`. -/
theorem heavyTailed_heavy : HeavyTailed heavy :=
  ⟨1 / 2, by norm_num, by simpa using tendsto_heavy_mergeProb_div (k := 3) (by norm_num)⟩

/-- The limit is a Λ-coalescent with multiple mergers: the ancestral lineage count of the heavy
model converges to the block-counting process of the `δ_{1/2}`-coalescent. -/
example (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N => (heavy N).lineageMatrix n ^ ⌊t / (heavy N).coalProb⌋₊) atTop
      (𝓝 (NormedSpace.exp (t • LambdaCoalescent.blockCountingGenerator (Measure.dirac half) n))) :=
  (tendsto_lineageMatrix_pow_of_heavyTailed mohleSagitovLambda_heavy heavyTailed_heavy n ht).2.2

/-- Λ is determined by the model: any Λ satisfying the conditions for `heavy` is `δ_{1/2}`. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (h : MohleSagitovLambda heavy Λ) :
    Λ = Measure.dirac half :=
  eq_of_mohleSagitovLambda h mohleSagitovLambda_heavy

/-- The `δ_{1/2}`-coalescent rates, from the definitions: of three lineages, a given pair merges
at rate `1/2` and all three merge at rate `1/2`. -/
example : LambdaCoalescent.mergerRate (Measure.dirac half) 3 2 = 1 / 2 ∧
    LambdaCoalescent.mergerRate (Measure.dirac half) 3 3 = 1 / 2 := by
  rw [LambdaCoalescent.mergerRate_of_le _ le_rfl (by norm_num),
    LambdaCoalescent.mergerRate_of_le _ (by norm_num) le_rfl, integral_dirac, integral_dirac]
  simp only [half]
  norm_num

/-- Its block-counting generator has a positive rate `1/2` for three lineages to become one;
Kingman's has rate `0`. -/
example : LambdaCoalescent.blockCountingGenerator (Measure.dirac half) 3 3 1 = 1 / 2 ∧
    KingmanBlockCounting.blockCountingGenerator 3 3 1 = 0 := by
  constructor
  · simp only [LambdaCoalescent.blockCountingGenerator]
    rw [LambdaCoalescent.mergerRate_of_le _ (by norm_num) (by norm_num), integral_dirac]
    simp [half]
  · simp [KingmanBlockCounting.blockCountingGenerator]

/-! ### Kingman boundary: the Moran model `m = 2`, `ε = 1`, limit `Λ = δ₀` -/

/-- The Moran-type sweepstake model: in every generation one parent has two offspring, one has
none, and every other parent has one. -/
def moran (N : ℕ) : CanningsModel N := sweepstake N 2 1 zero_le_one le_rfl

lemma moran_mergeProb_eq_zero {N k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ N) : (moran N).mergeProb k = 0 := by
  rw [moran, mergeProb_sweepstake _ _ le_rfl (by omega) (by omega) hkN,
    Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]
  simp

lemma moran_coalProb {N : ℕ} (hN : 2 ≤ N) : (moran N).coalProb = 2 / N.descFactorial 2 := by
  rw [moran, coalProb, mergeProb_sweepstake _ _ le_rfl hN le_rfl hN]
  norm_num [Nat.descFactorial]

/-- **The Moran model satisfies the Möhle–Sagitov conditions with `Λ = δ₀`**, from the
definitions: `q_k = 0` for `k ≥ 3`. -/
theorem mohleSagitovLambda_moran : MohleSagitovLambda moran (Measure.dirac 0) where
  eventually_coalProb_pos := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [moran_coalProb hN]
    have : 0 < (N.descFactorial 2 : ℝ) := by exact_mod_cast Nat.descFactorial_pos.2 hN
    positivity
  tendsto_coalProb := by
    have hd : Tendsto (fun N : ℕ => (N.descFactorial 2 : ℝ)) atTop atTop := by
      refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun N => ?_)
        (tendsto_sub_atTop_nat 1))
      rw [Nat.descFactorial_succ, Nat.descFactorial_one]
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · nlinarith [Nat.sub_le N 1]
    refine ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop hd).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [moran_coalProb hN]
  tendsto_mergeProb_div k hk := by
    rw [integral_dirac]
    rcases eq_or_lt_of_le hk with rfl | hk3
    · simp only [Nat.sub_self, pow_zero]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hc : 0 < (moran N).coalProb := by
        rw [moran_coalProb hN]
        have : 0 < (N.descFactorial 2 : ℝ) := by exact_mod_cast Nat.descFactorial_pos.2 hN
        positivity
      rw [coalProb] at hc ⊢
      rw [div_self hc.ne']
    · rw [Set.Icc.coe_zero, zero_pow (by omega)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop k] with N hN
      rw [moran_mergeProb_eq_zero (by omega) hN, zero_div]
  tendsto_doubleMergeProb_div := by
    refine tendsto_const_nhds.congr fun N => ?_
    rw [moran, doubleMergeProb_sweepstake, zero_div]

/-- **The Moran model is not heavy-tailed**, from the definitions: `q_3 = 0`, so `q_3 / c_N`
has limit `0` and no positive limit. -/
theorem not_heavyTailed_moran : ¬ HeavyTailed moran := by
  rintro ⟨φ, hφ, hlim⟩
  have h0 : Tendsto (fun N => (moran N).mergeProb 3 / (moran N).coalProb) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with N hN
    rw [moran_mergeProb_eq_zero le_rfl hN, zero_div]
  exact hφ.ne' (tendsto_nhds_unique hlim h0)

/-- At the boundary the Λ statement reduces to Kingman's: the Moran model's lineage count
converges to Kingman's pure-death process with rates `k choose 2`. -/
example (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N => (moran N).lineageMatrix n ^ ⌊t / (moran N).coalProb⌋₊) atTop
      (𝓝 (NormedSpace.exp (t • KingmanBlockCounting.blockCountingGenerator n))) :=
  tendsto_lineageMatrix_pow_dirac_zero mohleSagitovLambda_moran n ht

/-- The `δ₀` generator, from the definitions: three lineages become two at rate `3` (three
pairs, each at rate `1`) and never become one; this matches Kingman's generator. -/
example : LambdaCoalescent.blockCountingGenerator (Measure.dirac 0) 3 3 2 = 3 ∧
    LambdaCoalescent.blockCountingGenerator (Measure.dirac 0) 3 3 1 = 0 ∧
    KingmanBlockCounting.blockCountingGenerator 3 3 2 = 3 ∧
    KingmanBlockCounting.blockCountingGenerator 3 3 1 = 0 := by
  simp [LambdaCoalescent.blockCountingGenerator, LambdaCoalescent.mergerRate_dirac_zero,
    KingmanBlockCounting.blockCountingGenerator, Nat.choose]

/-! ### Violated hypothesis: one family per generation, `c_N = 1` -/

/-- The clonal sweepstake model: in every generation one parent has all `N` offspring. -/
def clonal (N : ℕ) : CanningsModel N := sweepstake N N 1 zero_le_one le_rfl

lemma clonal_mergeProb {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N) : (clonal N).mergeProb k = 1 := by
  rw [clonal, mergeProb_sweepstake _ _ (by omega) le_rfl hk hkN, one_mul,
    div_self (by exact_mod_cast (Nat.descFactorial_pos.2 hkN).ne')]

/-- `c_N = 1` for the clonal model, computed from the definitions. -/
lemma clonal_coalProb {N : ℕ} (hN : 2 ≤ N) : (clonal N).coalProb = 1 :=
  clonal_mergeProb le_rfl hN

/-- **No Λ-coalescent limit is claimed for the clonal model**: `c_N` does not tend to `0`, so
the Möhle–Sagitov conditions fail for every Λ. -/
theorem not_mohleSagitovLambda_clonal (Λ : Measure I) [IsFiniteMeasure Λ] :
    ¬ MohleSagitovLambda clonal Λ := by
  intro h
  have h1 : Tendsto (fun N => (clonal N).coalProb) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [clonal_coalProb hN]
  exact one_ne_zero (tendsto_nhds_unique h1 h.tendsto_coalProb)

/-- The clonal model does pass the tail-ratio test (`q_3 / c_N = 1`), so it is the time-scale
condition `c_N → 0`, not the tail condition, that rules it out. -/
example : HeavyTailed clonal := by
  refine ⟨1, one_pos, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [eventually_ge_atTop 3] with N hN
  rw [clonal_mergeProb (by norm_num) hN, clonal_coalProb (by omega), div_one]

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.CanningsLambda
