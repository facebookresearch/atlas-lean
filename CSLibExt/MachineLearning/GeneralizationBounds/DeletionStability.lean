/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.Stability
public import MathlibExt.Probability.Concentration.McDiarmidPi

/-!
# High-probability generalization from deletion stability

O. Bousquet and A. Elisseeff, *Stability and Generalization*, JMLR 2 (2002), Definition 6
(p. 504) and Theorem 12 (pp. 507–509). A change of one training example affects each of the
two gaps (population minus empirical or leave-one-out risk) by at most `4β + M/m`. Their
mean bounds differ: `2β` for empirical risk, `β` for the held-out estimate. Applying McDiarmid
separately gives (11) and (12), not a confidence bound on the intersection of the two events.

Samples are ordered tuples; deletion preserves the order of the remaining examples. Both
sizes of fit have replacement sensitivity at most `2β` at this single pair of sizes, without
permutation invariance or a stability assumption at a third size.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace CSLibExt.MachineLearning.GeneralizationBounds

variable {Z H : Type*} {n : ℕ} {L : H → Z → ℝ} {A : (Fin (n + 1) → Z) → H}
  {B : (Fin n → Z) → H} {β M : ℝ}

/-- Deletion stability with parameter `β`: at every test point, removing any one observation
from any sample changes the loss by at most `β`. `A` and `B` are the full and shorter fits;
when `n = 0`, `B` is evaluated on the empty tuple. Bousquet–Elisseeff, Definition 6. -/
def IsDeletionStable (L : H → Z → ℝ) (A : (Fin (n + 1) → Z) → H) (B : (Fin n → Z) → H)
    (β : ℝ) : Prop :=
  ∀ S (i : Fin (n + 1)) z, |L (A S) z - L (B (i.removeNth S)) z| ≤ β

/-- The leave-one-out risk tests each fit on the very observation excluded from its sample,
then averages the losses (Bousquet–Elisseeff, p. 502). -/
noncomputable def leaveOneOutRisk (L : H → Z → ℝ) (B : (Fin n → Z) → H)
    (S : Fin (n + 1) → Z) : ℝ :=
  (1 / (n + 1 : ℕ) : ℝ) * ∑ i, L (B (i.removeNth S)) (S i)

/-- The original and replaced full samples have the same deletion at the changed index.
Thus deletion stability `β` gives replace-one stability `2β` at the full size. -/
theorem IsDeletionStable.isUniformlyStable (h : IsDeletionStable L A B β) :
    IsUniformlyStable L A (2 * β) := by
  intro S i x z
  have h' := h (Function.update S i x) i z
  rw [Fin.removeNth_update] at h'
  linarith [(abs_le.mp h').2, (abs_le.mp (h S i z)).1]

-- Insert the new value immediately before the old one. Deleting the old value yields the
-- updated tuple; deleting the new value gives back the original tuple, in the original order.
private lemma stable_short (h : IsDeletionStable L A B β) : IsUniformlyStable L B (2 * β) := by
  intro S i x z
  let T := i.castSucc.insertNth (α := fun _ => Z) x S
  have hold : i.castSucc.removeNth T = S := Fin.removeNth_insertNth ..
  have hnew : i.succ.removeNth T = Function.update S i x := by
    funext j
    rcases lt_trichotomy j i with hj | rfl | hj
    · rw [Fin.removeNth_apply, Fin.succAbove_succ_of_le _ _ hj.le, Function.update_of_ne hj.ne,
        ← Fin.succAbove_castSucc_of_lt _ _ hj]
      exact Fin.insertNth_apply_succAbove ..
    · simp [Fin.removeNth_apply, T]
    · rw [Fin.removeNth_apply, Fin.succAbove_succ_of_lt _ _ hj, Function.update_of_ne hj.ne',
        ← Fin.succAbove_castSucc_of_le _ _ hj.le]
      exact Fin.insertNth_apply_succAbove ..
  have h₁ := h T i.castSucc z
  have h₂ := h T i.succ z
  rw [hold] at h₁
  rw [hnew] at h₂
  linarith [(abs_le.mp h₁).2, (abs_le.mp h₂).1]

private lemma replacement_abs {m : ℕ} {C : (Fin m → Z) → H} {c : ℝ}
    (h : IsUniformlyStable L C c) (S : Fin m → Z) (i : Fin m) (x z : Z) :
    |L (C (Function.update S i x)) z - L (C S) z| ≤ c := by
  refine abs_le.mpr ⟨?_, h S i x z⟩
  have h' := h (Function.update S i x) i (S i) z
  rw [Function.update_idem, Function.update_eq_self] at h'
  linarith

-- One loss may change by M; all other terms of the average change by at most c.
private lemma average_change {m : ℕ} [NeZero m] (u v : Fin m → ℝ) (i : Fin m) {c : ℝ}
    (hc : 0 ≤ c) (hi : |u i - v i| ≤ M) (hj : ∀ j ≠ i, |u j - v j| ≤ c) :
    |(1 / m : ℝ) * ∑ j, u j - (1 / m : ℝ) * ∑ j, v j| ≤ c + M / m := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ))]
  calc _ ≤ (1 / m : ℝ) * ∑ j, (c + if j = i then M else 0) := by
        gcongr
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        refine Finset.sum_le_sum fun j _ => ?_
        rcases eq_or_ne j i with rfl | h
        · simpa using hi.trans (le_add_of_nonneg_left hc)
        · simpa [h] using hj j h
    _ = _ := by simp [Finset.sum_add_distrib]; field_simp

private lemma abs_sub_le_range {a b : ℝ} (ha : a ∈ Set.Icc 0 M) (hb : b ∈ Set.Icc 0 M) :
    |a - b| ≤ M := abs_le.mpr ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩

private lemma empirical_change (h : IsDeletionStable L A B β) (hβ : 0 ≤ β)
    (hb : ∀ S z, L (A S) z ∈ Set.Icc 0 M) (S : Fin (n + 1) → Z) (i : Fin (n + 1)) (x : Z) :
    |empiricalRisk L (Function.update S i x) (A (Function.update S i x)) - empiricalRisk L S (A S)|
      ≤ 2 * β + M / (n + 1 : ℕ) := by
  apply average_change _ _ i (by positivity) (abs_sub_le_range (hb _ _) (hb _ _))
  intro j hji
  rw [Function.update_of_ne hji]
  exact replacement_abs h.isUniformlyStable S i x (S j)

private lemma loo_change (h : IsDeletionStable L A B β) (hβ : 0 ≤ β)
    (hb : ∀ T z, L (B T) z ∈ Set.Icc 0 M) (S : Fin (n + 1) → Z) (i : Fin (n + 1)) (x : Z) :
    |leaveOneOutRisk L B (Function.update S i x) - leaveOneOutRisk L B S|
      ≤ 2 * β + M / (n + 1 : ℕ) := by
  apply average_change _ _ i (by positivity) (abs_sub_le_range (hb _ _) (hb _ _))
  intro j hji
  obtain ⟨k, rfl⟩ := (Fin.eq_self_or_eq_succAbove j i).resolve_left hji.symm
  rw [Function.update_of_ne hji, Fin.removeNth_update_succAbove]
  exact replacement_abs (stable_short h) (j.removeNth S) k x (S j)

variable [MeasurableSpace Z] {ν : Measure Z} [IsProbabilityMeasure ν]

private lemma integrable_Icc {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc 0 M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]; exact (hb x).2)

private lemma risk_change {a b : H} {c : ℝ} (ha : Measurable (L a)) (hb : Measurable (L b))
    (haM : ∀ z, L a z ∈ Set.Icc 0 M) (hbM : ∀ z, L b z ∈ Set.Icc 0 M)
    (hab : ∀ z, |L a z - L b z| ≤ c) : |risk L ν a - risk L ν b| ≤ c := by
  rw [risk, risk, ← integral_sub (integrable_Icc ha haM) (integrable_Icc hb hbM)]
  simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := ν)
    (Filter.Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (hab z))

private lemma measurable_remove (i : Fin (n + 1)) : Measurable (i.removeNth (α := fun _ => Z)) :=
  Measurable.of_eval fun j => measurable_pi_apply (i.succAbove j)

-- The held-out example is independent of the deleted tuple: split the product law at i.
private lemma integral_held_out (i : Fin (n + 1))
    (hB : Measurable fun p : (Fin n → Z) × Z => L (B p.1) p.2)
    (hb : ∀ T z, L (B T) z ∈ Set.Icc 0 M) :
    ∫ S, L (B (i.removeNth S)) (S i) ∂Measure.pi (fun _ => ν) =
      ∫ S, risk L ν (B (i.removeNth S)) ∂Measure.pi (fun _ => ν) := by
  let Q := Measure.pi fun _ : Fin n => ν
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i
  calc _ = ∫ p : Z × (Fin n → Z), L (B p.2) p.1 ∂ν.prod Q :=
        he.integral_comp' (fun p => L (B p.2) p.1)
    _ = ∫ T, risk L ν (B T) ∂Q := integral_prod_symm _
        (integrable_Icc (hB.comp measurable_swap) fun p => hb p.2 p.1)
    _ = ∫ p : Z × (Fin n → Z), risk L ν (B p.2) ∂ν.prod Q := by
        rw [integral_fun_snd (μ := ν) (ν := Q) (fun T => risk L ν (B T)), probReal_univ, one_smul]
    _ = _ := (he.integral_comp' (fun p => risk L ν (B p.2))).symm

private lemma integral_loo_gap_le (h : IsDeletionStable L A B β)
    (hA : Measurable fun p : (Fin (n + 1) → Z) × Z => L (A p.1) p.2)
    (hB : Measurable fun p : (Fin n → Z) × Z => L (B p.1) p.2)
    (ha : ∀ S z, L (A S) z ∈ Set.Icc 0 M) (hb : ∀ T z, L (B T) z ∈ Set.Icc 0 M) :
    ∫ S, (risk L ν (A S) - leaveOneOutRisk L B S) ∂Measure.pi (fun _ => ν) ≤ β := by
  let P := Measure.pi fun _ : Fin (n + 1) => ν
  let m : ℝ := (n + 1 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  let D (i : Fin (n + 1)) (S : Fin (n + 1) → Z) := L (B (i.removeNth S)) (S i)
  have hD (i) : Integrable (D i) P := integrable_Icc
    (hB.comp ((measurable_remove i).prodMk (measurable_pi_apply i))) fun S => hb _ _
  have hR : Integrable (fun S => risk L ν (A S)) P :=
    (integrable_Icc (μ := P.prod ν) hA fun p => ha _ _).integral_prod_left
  have hshort : Integrable (fun T => risk L ν (B T)) (Measure.pi fun _ => ν) :=
    (integrable_Icc (μ := (Measure.pi fun _ => ν).prod ν) hB fun p => hb _ _).integral_prod_left
  have hterm (i : Fin (n + 1)) : (∫ S, risk L ν (A S) ∂P) ≤ (∫ S, D i S ∂P) + β := by
    rw [show (∫ S, D i S ∂P) = _ from integral_held_out (ν := ν) i hB hb]
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i
    have hI : Integrable (fun S => risk L ν (B (i.removeNth S))) P :=
      (measurePreserving_snd.comp he).integrable_comp_of_integrable hshort
    calc _ ≤ ∫ S, (risk L ν (B (i.removeNth S)) + β) ∂P := by
              apply integral_mono hR (hI.add (integrable_const β))
              intro S
              have hh := risk_change (L := L) (ν := ν) (a := A S) (b := B (i.removeNth S))
                (hA.comp measurable_prodMk_left) (hB.comp measurable_prodMk_left)
                (ha S) (hb (i.removeNth S)) (h S i)
              exact sub_le_iff_le_add'.mp (abs_le.mp hh).2
         _ = _ := by rw [integral_add hI (integrable_const β)]; simp [P]
  change (∫ S, (risk L ν (A S) - (1 / m) * ∑ i, D i S) ∂P) ≤ β
  rw [integral_sub hR ((integrable_finsetSum _ fun i _ => hD i).const_mul _),
    integral_const_mul, integral_finsetSum _ fun i _ => hD i]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hs
  change m * _ ≤ _ + m * β at hs
  rw [one_div_mul_eq_div, sub_le_iff_le_add', ← sub_le_iff_le_add, le_div_iff₀ hm]
  linarith

-- Invert the upper tail with a common coordinate bound K/m. The zero-width case is a
-- constant gap, so there is no need to interpret an exponential with a zero denominator.
private lemma confidence_of_gap {m : ℕ} [NeZero m] {r e : (Fin m → Z) → ℝ} {b K δ : ℝ}
    (hδ : δ ∈ Set.Ioo 0 1) (hK : 0 ≤ K) (hf : Measurable fun S => r S - e S)
    (hmean : ∫ S, (r S - e S) ∂Measure.pi (fun _ => ν) ≤ b)
    (hc : ∀ S i z,
      |(r (Function.update S i z) - e (Function.update S i z)) - (r S - e S)| ≤ K / m) :
    1 - δ ≤ (Measure.pi fun _ : Fin m => ν).real
      {S | r S ≤ e S + b + K * √(log (1 / δ) / (2 * m))} := by
  let P := Measure.pi fun _ : Fin m => ν
  let f := fun S => r S - e S
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  rcases hK.eq_or_lt with rfl | hK
  · have hz (x y : Fin m → Z) : f x = f y := by
      have h := abs_sub_le_sum_of_bounded_differences (f := f) (c := fun _ => (0 : ℝ) / m) hc x y
      simpa [abs_nonpos_iff, sub_eq_zero] using h
    have hgood (S : Fin m → Z) : r S ≤ e S + b := by
      change ∫ x, f x ∂P ≤ b at hmean
      have hh : (∫ x, f x ∂P) = f S := calc
        _ = ∫ _ : Fin m → Z, f S ∂P := integral_congr_ae (.of_forall fun x => hz x S)
        _ = _ := by simp
      rw [hh] at hmean
      exact sub_le_iff_le_add'.mp hmean
    simp [hgood, hδ.1.le]
  let t := K * √(log (1 / δ) / (2 * m))
  let c : Fin m → NNReal := fun _ => ⟨K / m, by positivity⟩
  have ht : 0 ≤ t := mul_nonneg hK.le (sqrt_nonneg _)
  have htail := measureReal_sub_integral_ge_le_of_bounded_differences (μ := fun _ => ν)
    (f := f) (c := c) hf hc ht
  have hlog := log_nonneg (one_le_div hδ.1 |>.mpr hδ.2.le)
  have hexp : exp (-2 * t ^ 2 / ∑ i, (c i : ℝ) ^ 2) = δ := by
    have hpow : t ^ 2 = K ^ 2 * (log (1 / δ) / (2 * m)) := by
      rw [show t = _ from rfl, mul_pow, sq_sqrt (div_nonneg hlog (by positivity))]
    have hex : -2 * t ^ 2 / ∑ i, (c i : ℝ) ^ 2 = -log (1 / δ) := by
      rw [hpow]
      change -2 * _ / (∑ _ : Fin m, (K / m) ^ 2) = _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [hex, exp_neg, exp_log (one_div_pos.mpr hδ.1)]
    simp
  rw [hexp] at htail
  have hbad : MeasurableSet {S | t ≤ f S - ∫ x, f x ∂P} :=
    measurableSet_le measurable_const (hf.sub_const _)
  have hprob : 1 - δ ≤ P.real {S | t ≤ f S - ∫ x, f x ∂P}ᶜ := by
    rw [measureReal_compl hbad, probReal_univ]
    linarith
  refine hprob.trans (measureReal_mono fun S hS => ?_)
  change ¬ t ≤ f S - ∫ x, f x ∂P at hS
  change (∫ x, f x ∂P) ≤ b at hmean
  change r S ≤ e S + b + t
  dsimp only [f] at hS hmean
  linarith

/-- **Uniform deletion stability implies high-probability generalization.** Let `m = n+1`
examples have product law `νᵐ`. At sizes `m` and `n`, suppose the fitted loss profiles are
jointly measurable and take values in `[0,M]`. If removing any example changes every test
loss by at most `β`, then at confidence `1-δ` the population risk is bounded by the empirical
risk plus `2β + (4mβ+M)√(log(1/δ)/(2m))`. At the same confidence it is bounded by the
leave-one-out risk plus `β + (4mβ+M)√(log(1/δ)/(2m))`. These are two separate probability
statements. The shorter learner `B` is defined on `Fin 0 → Z` when `m = 1`.

Source: Bousquet and Elisseeff, *Stability and Generalization*, JMLR 2 (2002), Theorem 12,
inequalities (11) and (12). The product-measure proof works on any measurable example space
and for order-sensitive deterministic learners; it requires stability at only these two sizes. -/
theorem IsDeletionStable.highProbability_generalization (h : IsDeletionStable L A B β)
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (hA : Measurable fun p : (Fin (n + 1) → Z) × Z => L (A p.1) p.2)
    (hB : Measurable fun p : (Fin n → Z) × Z => L (B p.1) p.2)
    (ha : ∀ S z, L (A S) z ∈ Set.Icc 0 M) (hb : ∀ T z, L (B T) z ∈ Set.Icc 0 M)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    let m : ℝ := (n + 1 : ℕ)
    let t := (4 * m * β + M) * √(log (1 / δ) / (2 * m))
    let P := Measure.pi fun _ : Fin (n + 1) => ν
    (1 - δ ≤ P.real {S | risk L ν (A S) ≤ empiricalRisk L S (A S) + 2 * β + t}) ∧
    (1 - δ ≤ P.real {S | risk L ν (A S) ≤ leaveOneOutRisk L B S + β + t}) := by
  intro m t P
  obtain ⟨z₀⟩ := ν.nonempty_of_neZero
  have hβ : 0 ≤ β := (abs_nonneg _).trans (h (fun _ => z₀) 0 z₀)
  have hM := (ha (fun _ => z₀) z₀).1.trans (ha (fun _ => z₀) z₀).2
  have hm : 0 < m := by dsimp [m]; positivity
  let r := fun S => risk L ν (A S)
  have hr : Measurable r := hA.stronglyMeasurable.integral_prod_right'.measurable
  have hrisk (S i x) : |r (Function.update S i x) - r S| ≤ 2 * β :=
    risk_change (L := L) (hA.comp measurable_prodMk_left) (hA.comp measurable_prodMk_left)
      (ha _) (ha S) (replacement_abs h.isUniformlyStable S i x)
  have bound (e : (Fin (n + 1) → Z) → ℝ) (b : ℝ) (he : Measurable e)
      (hmean : ∫ S, (r S - e S) ∂P ≤ b)
      (hec : ∀ S i x, |e (Function.update S i x) - e S| ≤ 2 * β + M / m) :
      1 - δ ≤ P.real {S | r S ≤ e S + b + t} := by
    apply confidence_of_gap hδ (by positivity) (hr.sub he) hmean
    intro S i x
    rw [show (4 * m * β + M) / m = 4 * β + M / m by field_simp]
    have h₁ := abs_le.mp (hrisk S i x)
    have h₂ := abs_le.mp (hec S i x)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · apply bound (fun S => empiricalRisk L S (A S)) (2 * β)
    · exact (Finset.measurable_sum _ fun i _ => hA.comp (measurable_id.prodMk
        (measurable_pi_apply i))).const_mul _
    · have hem := abs_integral_empiricalRisk_sub_risk_le (ν := ν) hA
        (fun S z => (abs_of_nonneg (ha S z).1).trans_le (ha S z).2) h.isUniformlyStable
      simp_rw [show ∀ S, r S - empiricalRisk L S (A S) = -(empiricalRisk L S (A S) - r S) by
        intro S; ring, integral_neg]
      linarith [(abs_le.mp hem).1]
    · exact empirical_change h hβ ha
  · apply bound (leaveOneOutRisk L B) β
    · exact (Finset.measurable_sum _ fun i _ => hB.comp ((measurable_remove i).prodMk
        (measurable_pi_apply i))).const_mul _
    · exact integral_loo_gap_le h hA hB ha hb
    · exact loo_change h hβ hb

end CSLibExt.MachineLearning.GeneralizationBounds
