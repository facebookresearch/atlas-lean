/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Code.OSSS.Coding
import Code.OSSS.Lindeberg
import Code.Probability.ContinuousFKG

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace GrandCoupling

open OSSS.Monotonic OSSS.Coding StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]





noncomputable def Vcube (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))

instance (n : ℕ) : IsProbabilityMeasure (Vcube n) := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num
  unfold Vcube; infer_instance











lemma condProbBit_true_eq_open (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E)
    (e : E) :
    condProbBit μ F η e true = condProbOpen μ F η e := by
  unfold condProbBit condProbOpen condMass OpenAt
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hag : Agree F η ω
  · by_cases hb : ω e = true
    · rw [if_pos ⟨hag, hb⟩, if_pos hag, Set.indicator_of_mem (by exact hb)]; ring
    · rw [if_neg (by tauto)]; rw [Set.indicator_of_notMem (by simp [hb])]; ring
  · rw [if_neg (by tauto), if_neg hag]
    by_cases hb : ω e = true
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ω e = true} from hb)]; ring
    · rw [Set.indicator_of_notMem (by simp [hb])]; ring



lemma condProbClosed_eq_one_sub_open (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) (hF : 0 < condNorm μ F η) :
    condProbClosed μ F η e = 1 - condProbOpen μ F η e := by
  have h := condProbBit_true_add_false μ F η e hF.ne'
  rw [condProbBit_true_eq_open] at h
  unfold condProbClosed
  linarith





lemma condProbClosed_antitone {μ : ConfigSpace E → ℝ} (hmono : IsMonotonicMeasure μ)
    (F : Finset E) (e : E) (ξ ζ : ConfigSpace E) (hle : ∀ f ∈ F, ξ f ≤ ζ f)
    (hZξ : 0 < condNorm μ F ξ) (hZζ : 0 < condNorm μ F ζ) :
    condProbClosed μ F ζ e ≤ condProbClosed μ F ξ e := by
  rw [condProbClosed_eq_one_sub_open μ F ξ e hZξ,
      condProbClosed_eq_one_sub_open μ F ζ e hZζ]
  have := hmono e F ξ ζ hle hZξ hZζ
  linarith





lemma decide_ge_mono {a a' thr thr' : ℝ} (ha : a ≤ a') (hthr : thr' ≤ thr) :
    decide (a ≥ thr) ≤ decide (a' ≥ thr') := by
  by_cases h : a ≥ thr
  · have h' : a' ≥ thr' := le_trans hthr (le_trans h ha)
    rw [decide_eq_true h, decide_eq_true h']
  · rw [decide_eq_false h]; exact bot_le








lemma codePrefix_mono_u {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (hle : u ≤ u') (k : ℕ) :
    codePrefix μ σ u k ≤ codePrefix μ σ u' k := by
  induction k with
  | zero => intro e; simp [codePrefix]
  | succ k ih =>
    by_cases hk : k < n
    · intro e
      conv_lhs => unfold codePrefix
      conv_rhs => unfold codePrefix
      simp only [hk, dif_pos]
      by_cases hek : e = σ ⟨k, hk⟩
      · subst hek
        rw [Function.update_self, Function.update_self]
        have hthr : condProbClosed μ (prefixSet σ k) (codePrefix μ σ u' k) (σ ⟨k, hk⟩)
            ≤ condProbClosed μ (prefixSet σ k) (codePrefix μ σ u k) (σ ⟨k, hk⟩) :=
          condProbClosed_antitone hmono (prefixSet σ k) (σ ⟨k, hk⟩)
            (codePrefix μ σ u k) (codePrefix μ σ u' k) (fun f _ => ih f)
            (condNorm_pos hpos _ _) (condNorm_pos hpos _ _)
        exact decide_ge_mono (hle ⟨k, hk⟩) hthr
      · rw [Function.update_of_ne hek, Function.update_of_ne hek]; exact ih e
    · intro e
      conv_lhs => unfold codePrefix
      conv_rhs => unfold codePrefix
      simp only [hk, dif_neg, not_false_iff]; exact ih e





lemma codeMap_mono_u {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) :
    Monotone (fun u : Fin n → ℝ => codeMap μ σ u) :=
  fun u u' hle => codePrefix_mono_u hpos hmono σ u u' hle n







lemma measurable_codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) :
    Measurable (fun u : Fin n → ℝ => codeMap μ (σ : Fin n → E) u) := by
  apply measurable_to_countable'
  intro x
  show MeasurableSet {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x}
  have hrw : {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x}
      = ⋂ t : Fin n, {u : Fin n → ℝ |
          x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)} := by
    ext u; simp only [Set.mem_setOf_eq, Set.mem_iInter]; exact codeMap_eq_iff μ σ x u
  rw [hrw]
  apply MeasurableSet.iInter
  intro t
  by_cases hbit : x ((σ : Fin n → E) t)
  · have hset : {u : Fin n → ℝ | x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)}
        = {u : Fin n → ℝ | u t ≥ thr μ (σ : Fin n → E) x t} := by
      ext u; simp only [Set.mem_setOf_eq, hbit]
      constructor
      · intro h; have := h.symm; rw [decide_eq_true_eq] at this; exact this
      · intro h; symm; rw [decide_eq_true_eq]; exact h
    rw [hset]; exact measurableSet_le measurable_const (measurable_pi_apply t)
  · have hbit' : x ((σ : Fin n → E) t) = false := by
      cases h : x ((σ : Fin n → E) t); rfl; exact absurd h hbit
    have hset : {u : Fin n → ℝ | x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)}
        = {u : Fin n → ℝ | u t < thr μ (σ : Fin n → E) x t} := by
      ext u; simp only [Set.mem_setOf_eq, hbit']
      constructor
      · intro h; rw [eq_comm, decide_eq_false_iff_not, not_le] at h; exact h
      · intro h; symm; rw [decide_eq_false_iff_not, not_le]; exact h
    rw [hset]; exact measurableSet_lt (measurable_pi_apply t) measurable_const



lemma measurable_g_codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) :
    Measurable (fun u : Fin n → ℝ => g (codeMap μ (σ : Fin n → E) u)) :=
  (measurable_of_finite g).comp (measurable_codeMap μ σ)




noncomputable def rawInterval (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (x : ConfigSpace E) (t : Fin n) : Set ℝ :=
  if x (σ t) then Set.Ici (thr μ σ x t) else Set.Iio (thr μ σ x t)



lemma vcube_rawInterval (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) {n : ℕ}
    (σ : Fin n → E) (x : ConfigSpace E) (t : Fin n) :
    (volume.restrict (Set.Icc (0:ℝ) 1) (rawInterval μ σ x t)).toReal
      = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) (x (σ t)) := by
  obtain ⟨h0, h1⟩ := thr_mem_Icc μ hpos σ x t
  have hsum := condProbBit_true_add_false μ (prefixSet σ (t : ℕ)) x (σ t)
    (OSSS.Monotonic.condNorm_pos hpos _ _).ne'
  have hthr_eq : thr μ σ x t = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) false := rfl
  unfold rawInterval
  by_cases hbit : x (σ t)
  · simp only [hbit, if_true]
    rw [Measure.restrict_apply' measurableSet_Icc]
    have hint : Set.Ici (thr μ σ x t) ∩ Set.Icc (0:ℝ) 1 = Set.Icc (thr μ σ x t) 1 := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨ha, _, ha1⟩; exact ⟨ha, ha1⟩
      · rintro ⟨ha, ha1⟩; exact ⟨ha, le_trans h0 ha, ha1⟩
    rw [hint, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    rw [hthr_eq] at *; linarith
  · simp only [hbit, Bool.false_eq_true, if_false]
    rw [Measure.restrict_apply' measurableSet_Icc]
    have hint : Set.Iio (thr μ σ x t) ∩ Set.Icc (0:ℝ) 1 = Set.Ico (0:ℝ) (thr μ σ x t) := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨ha, ha0, _⟩; exact ⟨ha0, ha⟩
      · rintro ⟨ha0, ha⟩; exact ⟨ha, ha0, le_trans (le_of_lt ha) h1⟩
    rw [hint, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal h0, hthr_eq]



lemma codeMap_fibre_eq_rawbox (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (x : ConfigSpace E) :
    {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x}
      = Set.univ.pi (fun t => rawInterval μ (σ : Fin n → E) x t) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [codeMap_eq_iff μ σ x u]
  apply forall_congr'
  intro t
  unfold rawInterval
  by_cases hbit : x ((σ : Fin n → E) t)
  · simp only [hbit, if_true, Set.mem_Ici]
    constructor
    · intro h; have := h.symm; rw [decide_eq_true_eq] at this; exact this
    · intro h; symm; rw [decide_eq_true_eq]; exact h
  · simp only [hbit, Bool.false_eq_true, if_false, Set.mem_Iio]
    constructor
    · intro h; rw [eq_comm, decide_eq_false_iff_not, not_le] at h; exact h
    · intro h; symm; rw [decide_eq_false_iff_not, not_le]; exact h







lemma vcube_fibre (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal = μ x := by
  rw [codeMap_fibre_eq_rawbox μ σ x]
  unfold Vcube
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  rw [← codeProb_eq_mass μ hpos hμ1 σ x]
  apply Finset.prod_congr rfl
  intro t _
  exact vcube_rawInterval μ hpos (σ : Fin n → E) x t









theorem integral_g_codeMap (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∑ x, g x * μ x := by
  have hms : ∀ x : ConfigSpace E,
      MeasurableSet {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x} :=
    fun x => (measurable_codeMap μ σ) (measurableSet_singleton x)
  have hpt : (fun u => g (codeMap μ (σ : Fin n → E) u))
      = (fun u => ∑ x, g x
          * (Set.indicator {u | codeMap μ (σ : Fin n → E) u = x} (fun _ => (1:ℝ)) u)) := by
    funext u
    rw [Finset.sum_eq_single (codeMap μ (σ : Fin n → E) u)]
    · rw [Set.indicator_of_mem
        (by simp : u ∈ {u' | codeMap μ (σ : Fin n → E) u' = codeMap μ (σ : Fin n → E) u})]; ring
    · intro x _ hx
      rw [Set.indicator_of_notMem
        (by simp only [Set.mem_setOf_eq]; exact fun h => hx h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hpt, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_const_mul, integral_indicator_const (1:ℝ) (hms x), smul_eq_mul, mul_one]
    rw [show (Vcube n).real {u | codeMap μ (σ : Fin n → E) u = x}
        = ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal from rfl]
    rw [vcube_fibre μ hpos hμ1 σ x]
  · intro x _
    exact Integrable.const_mul (Integrable.indicator (integrable_const 1) (hms x)) _






def Wt {n : ℕ} (U V : Fin n → ℝ) (s : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < s then V i else U i



lemma Wt_mono_V {n : ℕ} (U : Fin n → ℝ) (s : ℕ) :
    Monotone (fun V : Fin n → ℝ => Wt U V s) := by
  intro V V' hle i
  unfold Wt
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact hle i
  · simp only [h, if_false]; exact le_refl _


lemma measurable_Wt {n : ℕ} (U : Fin n → ℝ) (s : ℕ) :
    Measurable (fun V : Fin n → ℝ => Wt U V s) := by
  apply measurable_pi_lambda
  intro i; unfold Wt
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact measurable_pi_apply i
  · simp only [h, if_false]; exact measurable_const







lemma f_codeMap_mono {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (U : Fin n → ℝ) (s : ℕ) :
    Monotone (fun V : Fin n → ℝ => f (codeMap μ σ (Wt U V s))) :=
  fun _ _ hle => hf ((codeMap_mono_u hpos hmono σ) ((Wt_mono_V U s) hle))





lemma coord_codeMap_mono {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) (e : E) (U : Fin n → ℝ) (s : ℕ) :
    Monotone (fun V : Fin n → ℝ => Lindeberg.coord e (codeMap μ σ (Wt U V s))) :=
  fun _ _ hle => Lindeberg.coord_mono e ((codeMap_mono_u hpos hmono σ) ((Wt_mono_V U s) hle))



lemma measurable_f_codeMap_Wt (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (s : ℕ) :
    Measurable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (Wt U V s))) :=
  (measurable_g_codeMap μ σ f).comp (measurable_Wt U s)


lemma measurable_coord_codeMap_Wt (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (e : E) (U : Fin n → ℝ) (s : ℕ) :
    Measurable (fun V : Fin n → ℝ => Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s))) :=
  (measurable_g_codeMap μ σ (Lindeberg.coord e)).comp (measurable_Wt U s)


lemma abs_coord_le_one (e : E) (ω : ConfigSpace E) : |Lindeberg.coord e ω| ≤ 1 := by
  unfold Lindeberg.coord; split <;> norm_num
















theorem grandCoupling_fkg_cross {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (U : Fin n → ℝ)
    (s₁ s₂ : ℕ) :
    (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n) := by
  unfold Vcube
  refine continuous_fkg n
    (measurable_f_codeMap_Wt μ σ f U s₁)
    (measurable_coord_codeMap_Wt μ σ e U s₂)
    (fun V => hfC _)
    (fun V => abs_coord_le_one e _)
    (f_codeMap_mono hpos hmono (σ : Fin n → E) hf U s₁)
    (coord_codeMap_mono hpos hmono (σ : Fin n → E) e U s₂)
















theorem osss_grand_coupling {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (U : Fin n → ℝ) (t : ℕ) :
    ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1)))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
    ∧ ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n)) :=
  ⟨grandCoupling_fkg_cross hpos hmono σ hf hfC e U (t - 1) t,
   grandCoupling_fkg_cross hpos hmono σ hf hfC e U t (t - 1)⟩







section FK

open StatMech.OSSS.MonotonicFK



theorem fk_codeMap_mono {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {n : ℕ} (σ : Fin n → Sym2 V) :
    Monotone (fun u : Fin n → ℝ => codeMap (fkMass G p q) σ u) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact codeMap_mono_u (fun ω => fkMass_pos G hp hp1 hq0 ω) (fkMass_isMonotonic G hp hp1 hq) σ




theorem fk_grandCoupling_fkg_cross {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    {f : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf)
    (e : Sym2 V) (U : Fin n → ℝ) (s₁ s₂ : ℕ) :
    (∫ Vv, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₁)) ∂(Vcube n))
        * (∫ Vv, Lindeberg.coord e (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₂)) ∂(Vcube n))
      ≤ ∫ Vv, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₁))
            * Lindeberg.coord e (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₂)) ∂(Vcube n) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact grandCoupling_fkg_cross (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_isMonotonic G hp hp1 hq) σ hf hfC e U s₁ s₂

end FK

end GrandCoupling

end OSSS

end StatMech
