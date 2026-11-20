/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.OSSS.Integration
import Code.OSSS.BetaThresholdBound
import Code.FK.WiredDomChain
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators
open Filter Topology Real Finset

set_option linter.style.longLine false

namespace StatMech
namespace OSSS
namespace LogCesaroLimit

open BetaThresholdBound


noncomputable def harmonicReal (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 (n + 1), 1 / (i : ℝ)

lemma harmonicReal_eq (n : ℕ) : harmonicReal n = (harmonic n : ℝ) := by
  rw [harmonicReal, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  · intro i _
    rw [one_div]


theorem harmonicReal_div_log_tendsto_one :
    Tendsto (fun n => harmonicReal n / Real.log (n : ℝ)) atTop (nhds 1) := by
  have hdiff : Tendsto (fun n : ℕ => harmonicReal n - Real.log (n : ℝ)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    simpa only [harmonicReal_eq] using tendsto_harmonic_sub_log
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto
      (fun n : ℕ => (harmonicReal n - Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (nhds 0) := hdiff.div_atTop hlog
  have hadd : Tendsto
      (fun n : ℕ => (harmonicReal n - Real.log (n : ℝ)) / Real.log (n : ℝ) + 1)
      atTop (nhds 1) := by
    simpa using hzero.add_const 1
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  field_simp
  ring


noncomputable def logCesaro (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / Real.log (n : ℝ)) * ∑ i ∈ Finset.Ico 1 (n + 1), u i / (i : ℝ)

private theorem weighted_error_tendsto_zero {u : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds 0)) :
    Tendsto (fun n => logCesaro u n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hu (ε / 4) (by positivity))
  let N := max N₀ 1
  have hN1 : 1 ≤ N := le_max_right _ _
  have hN : ∀ n ≥ N, dist (u n) 0 < ε / 4 :=
    fun n hn => hN₀ n (le_trans (le_max_left _ _) hn)
  let C : ℝ := ∑ i ∈ Finset.Ico 1 N, |u i| / (i : ℝ)
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg i)
  have hhead : Tendsto (fun n : ℕ => C / Real.log (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hratio := harmonicReal_div_log_tendsto_one
  have hevHead : ∀ᶠ n : ℕ in atTop, C / Real.log (n : ℝ) < ε / 2 :=
    hhead.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  have hevRatio : ∀ᶠ n in atTop, harmonicReal n / Real.log (n : ℝ) < 2 :=
    hratio.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
  rw [← eventually_atTop]
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 2, hevHead, hevRatio]
      with n hnN hn2 hheadn hrat
  rw [Real.dist_eq]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsplit :
      (∑ i ∈ Finset.Ico 1 (n + 1), u i / (i : ℝ)) =
        (∑ i ∈ Finset.Ico 1 N, u i / (i : ℝ)) +
          ∑ i ∈ Finset.Ico N (n + 1), u i / (i : ℝ) := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_union, Finset.mem_Ico]
        omega
      · intro i _
        rfl
    · rw [Finset.disjoint_left]
      intro i hi hj
      simp only [Finset.mem_Ico] at hi hj
      omega
  have htailAbs :
      |∑ i ∈ Finset.Ico N (n + 1), u i / (i : ℝ)|
        ≤ (ε / 4) * harmonicReal n := by
    calc
      |∑ i ∈ Finset.Ico N (n + 1), u i / (i : ℝ)|
          ≤ ∑ i ∈ Finset.Ico N (n + 1), |u i / (i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico N (n + 1), (ε / 4) * (1 / (i : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Finset.mem_Ico] at hi
        have hui := hN i hi.1
        rw [Real.dist_eq, sub_zero] at hui
        have hi0 : 0 < (i : ℝ) := by
          exact_mod_cast (show 0 < i by omega)
        rw [abs_div, abs_of_pos hi0, one_div]
        exact mul_le_mul_of_nonneg_right (le_of_lt hui) (inv_nonneg.mpr hi0.le)
      _ ≤ ∑ i ∈ Finset.Ico 1 (n + 1), (ε / 4) * (1 / (i : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_Ico] at hi ⊢
          omega
        · intro i _ _
          positivity
      _ = (ε / 4) * harmonicReal n := by
        rw [harmonicReal, Finset.mul_sum]
  have hheadAbs :
      |∑ i ∈ Finset.Ico 1 N, u i / (i : ℝ)| ≤ C := by
    calc
      |∑ i ∈ Finset.Ico 1 N, u i / (i : ℝ)|
          ≤ ∑ i ∈ Finset.Ico 1 N, |u i / (i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ = C := by
        unfold C
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (i : ℝ) by positivity)]
  unfold logCesaro
  rw [hsplit, mul_add]
  have hone : 1 / Real.log (n : ℝ) ≥ 0 := by positivity
  calc
    |1 / Real.log (n : ℝ) * ∑ i ∈ Finset.Ico 1 N, u i / (i : ℝ) +
        1 / Real.log (n : ℝ) * ∑ i ∈ Finset.Ico N (n + 1), u i / (i : ℝ) - 0|
        = |1 / Real.log (n : ℝ) * ∑ i ∈ Finset.Ico 1 N, u i / (i : ℝ) +
            1 / Real.log (n : ℝ) * ∑ i ∈ Finset.Ico N (n + 1), u i / (i : ℝ)| := by rw [sub_zero]
    _ ≤ |1 / Real.log (n : ℝ) * ∑ i ∈ Finset.Ico 1 N, u i / (i : ℝ)| +
        |1 / Real.log (n : ℝ) * ∑ i ∈ Finset.Ico N (n + 1), u i / (i : ℝ)|
          := abs_add_le _ _
    _
        ≤ C / Real.log (n : ℝ) +
          (1 / Real.log (n : ℝ)) * ((ε / 4) * harmonicReal n) := by
      simp only [abs_mul, abs_of_nonneg hone]
      exact add_le_add
        (by simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hheadAbs hone)
        (mul_le_mul_of_nonneg_left htailAbs hone)
    _ < ε / 2 + (ε / 4) * 2 := by
      have htailFinal :
          (1 / Real.log (n : ℝ)) * ((ε / 4) * harmonicReal n) < (ε / 4) * 2 := by
        have he4 : 0 < ε / 4 := by positivity
        calc
          (1 / Real.log (n : ℝ)) * ((ε / 4) * harmonicReal n)
              = (ε / 4) * (harmonicReal n / Real.log (n : ℝ)) := by
                rw [div_eq_mul_inv]
                ring
          _ < (ε / 4) * 2 := mul_lt_mul_of_pos_left hrat he4
      exact add_lt_add hheadn htailFinal
    _ = ε := by ring


theorem logCesaro_tendsto {u : ℕ → ℝ} {l : ℝ} (hu : Tendsto u atTop (nhds l)) :
    Tendsto (fun n => logCesaro u n) atTop (nhds l) := by
  have herr : Tendsto (fun n => u n - l) atTop (nhds 0) := by
    simpa using hu.sub_const l
  have hzero := weighted_error_tendsto_zero herr
  have hnorm : Tendsto (fun n => l * (harmonicReal n / Real.log (n : ℝ))) atTop (nhds l) := by
    simpa using harmonicReal_div_log_tendsto_one.const_mul l
  have hdecomp : ∀ᶠ n in atTop,
      logCesaro u n = logCesaro (fun i => u i - l) n +
        l * (harmonicReal n / Real.log (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    unfold logCesaro harmonicReal
    have hsum :
        (∑ i ∈ Finset.Ico 1 (n + 1), u i / (i : ℝ)) =
          (∑ i ∈ Finset.Ico 1 (n + 1), (u i - l) / (i : ℝ)) +
            l * ∑ i ∈ Finset.Ico 1 (n + 1), 1 / (i : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : (i : ℝ) ≠ 0 := by
        simp only [Finset.mem_Ico] at hi
        exact_mod_cast (show i ≠ 0 by omega)
      field_simp
      ring
    rw [hsum]
    field_simp
  have hadd : Tendsto
      (fun n => logCesaro (fun i => u i - l) n + l * (harmonicReal n / Real.log (n : ℝ)))
      atTop (nhds l) := by
    simpa using hzero.add hnorm
  exact hadd.congr' (hdecomp.mono fun _ h => h.symm)


theorem meanLogTerm_tendsto {fseq : ℕ → ℝ → ℝ} {x l : ℝ}
    (h : Tendsto (fun n => fseq n x) atTop (nhds l)) :
    Tendsto (fun n => Integration.meanLogTerm fseq n x) atTop (nhds l) := by
  simpa only [Integration.meanLogTerm, logCesaro] using logCesaro_tendsto h



theorem logRatio_partialSum_tendsto_one {u : ℕ → ℝ} {l : ℝ}
    (hu : Tendsto u atTop (nhds l)) (hl : 0 < l) :
    Tendsto
      (BetaThresholdBound.logRatio
        (fun n => ∑ k ∈ Finset.range n, u k))
      atTop (nhds 1) := by
  let S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, u k
  let avg : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * S n
  have havg : Tendsto avg atTop (nhds l) := by
    simpa [avg, S] using hu.cesaro
  have hlogavg : Tendsto (fun n => Real.log (avg n)) atTop
      (nhds (Real.log l)) := havg.log hl.ne'
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto
      (fun n => Real.log (avg n) / Real.log (n : ℝ)) atTop (nhds 0) :=
    hlogavg.div_atTop hlogn
  have hone : Tendsto
      (fun n => 1 + Real.log (avg n) / Real.log (n : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  apply hone.congr'
  have havgPos : ∀ᶠ n in atTop, 0 < avg n :=
    havg.eventually (Ioi_mem_nhds hl)
  filter_upwards [Filter.eventually_ge_atTop 2, havgPos] with n hn havgn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlogn0 : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  have hS : S n = (n : ℝ) * avg n := by
    unfold avg
    field_simp
  unfold BetaThresholdBound.logRatio
  change 1 + Real.log (avg n) / Real.log (n : ℝ) =
    Real.log (S n) / Real.log (n : ℝ)
  rw [hS, Real.log_mul hn0 havgn.ne']
  field_simp



theorem wiredBox_logCesaro_tendsto {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto
      (fun n => logCesaro
        (fun k => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) k) n)
      atTop (nhds (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))) :=
  logCesaro_tendsto (FK.boxBoundaryConnProfile_tendsto hp hp1)






theorem thresholdSet_upward {Sgf : ℝ → ℕ → ℝ}
    (hmono : ∀ {a b : ℝ}, a ≤ b → ∀ n, Sgf a n ≤ Sgf b n)
    (hpos : ∀ b n, 2 ≤ n → 0 < Sgf b n)
    (hcob : ∀ b, IsCoboundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
    (hbdd : ∀ b, IsBoundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
    {a b : ℝ} (hab : a ≤ b) (ha : a ∈ thresholdSet Sgf) :
    b ∈ thresholdSet Sgf := by
  have hev : ∀ᶠ n : ℕ in atTop, logRatio (Sgf a) n ≤ logRatio (Sgf b) n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    unfold logRatio
    exact (div_le_div_iff_of_pos_right hlogn).2
      (Real.log_le_log (hpos a n hn) (hmono hab n))
  exact ha.trans (limsup_le_limsup hev (hcob a) (hbdd b))




theorem one_le_limsup_of_beta1_lt {Sgf : ℝ → ℕ → ℝ}
    (hne : (thresholdSet Sgf).Nonempty)
    (hmono : ∀ {a b : ℝ}, a ≤ b → ∀ n, Sgf a n ≤ Sgf b n)
    (hpos : ∀ b n, 2 ≤ n → 0 < Sgf b n)
    (hcob : ∀ b, IsCoboundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
    (hbdd : ∀ b, IsBoundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
    {b : ℝ} (hb : beta1 Sgf < b) :
    1 ≤ limsup (logRatio (Sgf b)) atTop := by
  unfold beta1 at hb
  obtain ⟨a, ha, hab⟩ := exists_lt_of_csInf_lt hne hb
  exact thresholdSet_upward hmono hpos hcob hbdd hab.le ha




theorem thresholdRate_limit_data {Sgf : ℝ → ℕ → ℝ}
    (hne : (thresholdSet Sgf).Nonempty)
    (hmono : ∀ {a b : ℝ}, a ≤ b → ∀ n, Sgf a n ≤ Sgf b n)
    (hpos : ∀ b n, 2 ≤ n → 0 < Sgf b n)
    (hcob : ∀ b, IsCoboundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
    (hbdd : ∀ b, IsBoundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
    {b : ℝ} (hb : beta1 Sgf < b) :
    ∃ (mseq : ℕ → ℝ) (m : ℝ), Tendsto mseq atTop (nhds m) ∧ 1 ≤ m := by
  let m := limsup (logRatio (Sgf b)) atTop
  exact ⟨fun _ => m, m, tendsto_const_nhds, one_le_limsup_of_beta1_lt hne hmono hpos hcob hbdd hb⟩






theorem meanField_lower_of_limsup {T : ℕ → ℝ → ℝ} {rate error : ℕ → ℝ}
    {β' β fβ fβ' : ℝ} (hββ : β' ≤ β)
    (hTβ : Tendsto (fun n => T n β) atTop (nhds fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (nhds fβ'))
    (herror : Tendsto error atTop (nhds 0))
    (hcob : IsCoboundedUnder (· ≤ ·) atTop rate)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop rate)
    (hm1 : 1 ≤ limsup rate atTop)
    (hbound : ∀ᶠ n in atTop,
      (β - β') * (rate n + error n) ≤ T n β - T n β') :
    β - β' ≤ fβ - fβ' := by
  obtain ⟨s, hsrate, hs⟩ := exists_seq_tendsto_limsup hcob hbdd
  have hmseq : Tendsto (fun j => rate (s j) + error (s j)) atTop
      (nhds (limsup rate atTop)) := by
    simpa using hsrate.add (herror.comp hs)
  exact Integration.meanField_lower
    (fun j x => T (s j) x) (fun j => rate (s j) + error (s j))
    β' β fβ fβ' (limsup rate atTop) hββ hm1
    (hTβ.comp hs) (hTβ'.comp hs) hmseq (hs.eventually hbound)







theorem meanField_lower_of_threshold_rate
    (fseq fpseq : ℕ → ℝ → ℝ) (Sig : ℕ → ℝ → ℝ)
    (β' β fβ fβ' C : ℝ) (hββ : β' ≤ β)
    (hf : ∀ i x, x ∈ Set.Icc β' β →
      HasDerivAt (fun x => fseq i x) (fpseq i x) x)
    (hSrec : ∀ i x, Sig (i + 1) x = Sig i x + fseq i x)
    (hfnn : ∀ i x, 1 ≤ i → x ∈ Set.Icc β' β → 0 ≤ fseq i x)
    (hSpos : ∀ i x, 1 ≤ i → x ∈ Set.Icc β' β → 0 < Sig i x)
    (hdiff : ∀ i : ℕ, ∀ x, 1 ≤ i → x ∈ Set.Icc β' β →
      ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x)
    (hSmono : ∀ n x, 1 ≤ n → x ∈ Set.Icc β' β → Sig n β' ≤ Sig (n + 1) x)
    (hS1le : ∀ x ∈ Set.Icc β' β, Sig 1 x ≤ C)
    (hTβ : Tendsto (fun n => Integration.meanLogTerm fseq n β) atTop (nhds fβ))
    (hTβ' : Tendsto (fun n => Integration.meanLogTerm fseq n β') atTop (nhds fβ'))
    (hcob : IsCoboundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig n β')))
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig n β')))
    (hm1 : 1 ≤ limsup (logRatio (fun n => Sig n β')) atTop) :
    β - β' ≤ fβ - fβ' := by
  let err : ℕ → ℝ := fun n => -Real.log C / Real.log (n : ℝ)
  have herr : Tendsto err atTop (nhds 0) := by
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    simpa [err] using (tendsto_const_nhds.div_atTop hlog :
      Tendsto (fun n : ℕ => -Real.log C / Real.log (n : ℝ)) atTop (nhds 0))
  apply meanField_lower_of_limsup hββ hTβ hTβ' herr hcob hbdd hm1
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : 1 ≤ n := by omega
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply Integration.integrated_meanField fseq fpseq Sig n β' β
    (logRatio (fun n => Sig n β') n + err n) hββ hlogn hf hSrec hfnn hSpos hdiff
  intro x hx
  have hSn : 0 < Sig n β' := hSpos n β' hn1 ⟨le_rfl, hββ⟩
  have hSnext : 0 < Sig (n + 1) x := hSpos (n + 1) x (by omega) hx
  have hS1 : 0 < Sig 1 x := hSpos 1 x le_rfl hx
  have hlogLeft : Real.log (Sig n β') ≤ Real.log (Sig (n + 1) x) :=
    Real.log_le_log hSn (hSmono n x hn1 hx)
  have hlogRight : Real.log (Sig 1 x) ≤ Real.log C :=
    Real.log_le_log hS1 (hS1le x hx)
  unfold logRatio err
  calc
    Real.log ((fun n => Sig n β') n) / Real.log (n : ℝ) +
        -Real.log C / Real.log (n : ℝ)
        = (Real.log (Sig n β') - Real.log C) / Real.log (n : ℝ) := by ring
    _ ≤ (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log (n : ℝ) :=
      (div_le_div_iff_of_pos_right hlogn).2 (by linarith)




theorem meanField_lower_at_threshold {f : ℝ → ℝ} {β₁ β : ℝ} (hβ : β₁ < β)
    (hfnn : ∀ β', β₁ < β' → β' < β → 0 ≤ f β')
    (hinterior : ∀ β', β₁ < β' → β' < β →
      β - β' ≤ f β - f β') :
    β - β₁ ≤ f β := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min ε (β - β₁) / 2
  have hgap : 0 < β - β₁ := sub_pos.mpr hβ
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδε : δ ≤ ε := by
    dsimp [δ]
    have := min_le_left ε (β - β₁)
    linarith
  have hδgap : δ < β - β₁ := by
    dsimp [δ]
    have := min_le_right ε (β - β₁)
    linarith
  let β' := β₁ + δ
  have hβ'1 : β₁ < β' := by dsimp [β']; linarith
  have hβ'2 : β' < β := by dsimp [β']; linarith
  have hb := hinterior β' hβ'1 hβ'2
  have hf' := hfnn β' hβ'1 hβ'2
  dsimp [β'] at hb hf' ⊢
  linarith

end LogCesaroLimit
end OSSS
end StatMech
