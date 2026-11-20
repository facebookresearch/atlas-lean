/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Code.Percolation.SubcriticalDecay
import Code.Percolation.BurtonKeane
import Code.Percolation.PcNontrivial

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}






















theorem gronwall_dct (f f' : ℝ → ℝ) (a p : ℝ) (ha0 : 0 < a) (hap : a < p) (hp1 : p < 1)
    (hcont : ContinuousOn f (Icc a p))
    (hub : ∀ t ∈ Icc a p, f t ≤ 1)
    (hfa : 0 ≤ f a)
    (hderiv : ∀ t ∈ Ioo a p, HasDerivAt f (f' t) t)
    (hdiff_ineq : ∀ t ∈ Ioo a p, f' t ≥ (1 / (t * (1 - t))) * (1 - f t)) :
    f p ≥ (p - a) / (p * (1 - a)) := by
  have h1tpos : ∀ t ∈ Icc a p, (0 : ℝ) < 1 - t := fun t ht => by
    have : t ≤ p := ht.2; linarith
  
  set g : ℝ → ℝ := fun t => (1 - f t) * (t / (1 - t)) with hg
  have hμcont : ContinuousOn (fun t => t / (1 - t)) (Icc a p) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact (h1tpos t ht).ne'
  have hgcont : ContinuousOn g (Icc a p) := ContinuousOn.mul (by fun_prop) hμcont
  have hint : interior (Icc a p) = Ioo a p := interior_Icc
  
  have hgderiv : ∀ t ∈ Ioo a p, HasDerivAt g
      (-(f' t) * (t / (1 - t)) + (1 - f t) * (1 / (1 - t) ^ 2)) t := by
    intro t ht
    have h1t : (0 : ℝ) < 1 - t := by have := ht.2; linarith
    have hfd : HasDerivAt (fun t => 1 - f t) (-(f' t)) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).sub (hderiv t ht)
    have hμd : HasDerivAt (fun t => t / (1 - t)) (1 / (1 - t) ^ 2) t := by
      have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
        simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      have := h1.div h2 h1t.ne'
      convert this using 1; field_simp; ring
    exact hfd.mul hμd
  
  have hgderiv_nonpos : ∀ t ∈ Ioo a p,
      (-(f' t) * (t / (1 - t)) + (1 - f t) * (1 / (1 - t) ^ 2)) ≤ 0 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans ha0 ht.1
    have h1t : (0 : ℝ) < 1 - t := by have := ht.2; linarith
    have htIcc : t ∈ Icc a p := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hfle : f t ≤ 1 := hub t htIcc
    have hdi := hdiff_ineq t ht
    have hμpos : (0 : ℝ) ≤ t / (1 - t) := by positivity
    have key : (1 / (t * (1 - t))) * (1 - f t) * (t / (1 - t)) = (1 - f t) * (1 / (1 - t) ^ 2) := by
      field_simp
    have step : (1 / (t * (1 - t))) * (1 - f t) * (t / (1 - t)) ≤ f' t * (t / (1 - t)) :=
      mul_le_mul_of_nonneg_right hdi hμpos
    rw [key] at step
    nlinarith [step]
  
  have hgmono : AntitoneOn g (Icc a p) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a p) hgcont
    · rw [hint]; intro t ht; exact (hgderiv t ht).differentiableAt.differentiableWithinAt
    · rw [hint]; intro t ht; rw [(hgderiv t ht).deriv]; exact hgderiv_nonpos t ht
  
  have hgle : g p ≤ g a :=
    hgmono ⟨le_refl a, le_of_lt hap⟩ ⟨le_of_lt hap, le_refl p⟩ (le_of_lt hap)
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hppos : (0 : ℝ) < p := lt_trans ha0 hap
  have hga_le : g a ≤ a / (1 - a) := by
    rw [hg]; simp only
    have hμa : (0 : ℝ) ≤ a / (1 - a) := by positivity
    nlinarith [hfa, hμa]
  have hcomb : (1 - f p) * (p / (1 - p)) ≤ a / (1 - a) := le_trans hgle hga_le
  have hkey : (1 - f p) * p / (1 - p) ≤ a / (1 - a) := by rw [← mul_div_assoc] at hcomb; exact hcomb
  rw [div_le_div_iff₀ h1p h1a] at hkey
  rw [ge_iff_le, div_le_iff₀ (by positivity)]
  nlinarith [hkey]









noncomputable def crossProbReal (d n : ℕ) (t : ℝ) : ℝ :=
  if ht : 0 ≤ t ∧ t ≤ 1 then crossProb d t.toNNReal (Real.toNNReal_le_one.mpr ht.2) n else 0


theorem crossProbReal_eq (d n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    crossProbReal d n (p : ℝ) = crossProb d p hp n := by
  unfold crossProbReal
  rw [dif_pos ⟨p.coe_nonneg, by exact_mod_cast hp⟩]
  congr 1
  exact Real.toNNReal_coe


theorem crossProbReal_le_one (d n : ℕ) (t : ℝ) : crossProbReal d n t ≤ 1 := by
  unfold crossProbReal; split
  · exact crossProb_le_one _ _ _ _
  · norm_num


theorem crossProbReal_nonneg (d n : ℕ) (t : ℝ) : 0 ≤ crossProbReal d n t := by
  unfold crossProbReal; split
  · exact crossProb_nonneg _ _ _ _
  · norm_num









theorem measurableSet_crossingEvent' (n : ℕ) : MeasurableSet (crossingEvent d n) := by
  have hrw : crossingEvent d n
      = ⋃ v ∈ {v : Site d | v ∉ box d (n - 1)}, {ω | Connected d ω (origin d) v} := by
    ext ω
    simp only [mem_crossingEvent, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun ⟨v, hc, hb⟩ => ⟨v, hb, hc⟩, fun ⟨v, hb, hc⟩ => ⟨v, hc, hb⟩⟩
  rw [hrw]
  exact MeasurableSet.biUnion (Set.to_countable _)
    (fun v _ => measurableSet_connected (origin d) v)




theorem percolationEvent_eq_iInter :
    percolationEvent d = ⋂ n : ℕ, crossingEvent d (n + 1) := by
  ext ω
  rw [mem_percolationEvent, cluster_infinite_iff]
  simp only [Set.mem_iInter, mem_crossingEvent, Nat.add_sub_cancel]
  exact ⟨fun h n => let ⟨y, hb, hc⟩ := h n; ⟨y, hc, hb⟩,
         fun h n => let ⟨v, hc, hb⟩ := h n; ⟨v, hb, hc⟩⟩




theorem tendsto_crossProb_theta (p : ℝ≥0) (hp : p ≤ 1) :
    Tendsto (fun n => crossProb d p hp (n + 1)) atTop (𝓝 (theta d p hp)) := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp with hμ
  have hanti : Antitone (fun n => crossingEvent d (n + 1)) :=
    fun m n hmn => crossingEvent_antitone (m + 1) (n + 1) (by omega)
  have hmeas : ∀ n, NullMeasurableSet (crossingEvent d (n + 1)) μ :=
    fun n => (measurableSet_crossingEvent' (n + 1)).nullMeasurableSet
  have htend := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
  rw [← percolationEvent_eq_iInter] at htend
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp htend






theorem theta_eq_zero_of_crossProb_decay (p : ℝ≥0) (hp : p ≤ 1)
    (hdecay : ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) :
    theta d p hp = 0 := by
  obtain ⟨c, hc, C, _, hbound⟩ := hdecay
  have htend : Tendsto (fun n => crossProb d p hp (n + 1)) atTop (𝓝 (theta d p hp)) :=
    tendsto_crossProb_theta p hp
  refine le_antisymm ?_ (theta_nonneg d p hp)
  have hexp : Tendsto (fun n : ℕ => (-c) * ((n : ℝ) + 1)) atTop atBot := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => c * ((n : ℝ) + 1)) atTop atTop := h1.const_mul_atTop hc
    simpa [neg_mul] using tendsto_neg_atBot_iff.mpr h2
  have hbnd : Tendsto (fun n : ℕ => C * Real.exp ((-c) * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_atBot.comp hexp).const_mul C)
  refine le_of_tendsto_of_tendsto htend hbnd (Filter.Eventually.of_forall (fun n => ?_))
  convert hbound (n + 1) using 3
  push_cast; ring











theorem theta_ge_meanField (q : ℝ≥0) (hq : q ≤ 1)
    (a : ℝ) (ha0 : 0 < a) (haq : a < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    (F' : ℕ → ℝ → ℝ)
    (hcont : ∀ n, ContinuousOn (crossProbReal d (n + 1)) (Icc a (q : ℝ)))
    (hderiv : ∀ n, ∀ t ∈ Ioo a (q : ℝ), HasDerivAt (crossProbReal d (n + 1)) (F' n t) t)
    (hdiffineq : ∀ n, ∀ t ∈ Ioo a (q : ℝ),
        F' n t ≥ (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t)) :
    theta d q hq ≥ ((q : ℝ) - a) / ((q : ℝ) * (1 - a)) := by
  have hbound : ∀ n, crossProb d q hq (n + 1) ≥ ((q : ℝ) - a) / ((q : ℝ) * (1 - a)) := by
    intro n
    have hg := gronwall_dct (crossProbReal d (n + 1)) (F' n) a (q : ℝ) ha0 haq hq1
      (hcont n) (fun t _ => crossProbReal_le_one d (n + 1) t)
      (crossProbReal_nonneg d (n + 1) a) (hderiv n) (hdiffineq n)
    rwa [crossProbReal_eq d (n + 1) q hq] at hg
  exact ge_of_tendsto (tendsto_crossProb_theta q hq) (Filter.Eventually.of_forall hbound)



theorem theta_pos_of_meanField (q : ℝ≥0) (hq : q ≤ 1)
    (a : ℝ) (ha0 : 0 < a) (haq : a < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    (F' : ℕ → ℝ → ℝ)
    (hcont : ∀ n, ContinuousOn (crossProbReal d (n + 1)) (Icc a (q : ℝ)))
    (hderiv : ∀ n, ∀ t ∈ Ioo a (q : ℝ), HasDerivAt (crossProbReal d (n + 1)) (F' n t) t)
    (hdiffineq : ∀ n, ∀ t ∈ Ioo a (q : ℝ),
        F' n t ≥ (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t)) :
    0 < theta d q hq := by
  have hbound := theta_ge_meanField q hq a ha0 haq hq1 F' hcont hderiv hdiffineq
  have hpos : 0 < ((q : ℝ) - a) / ((q : ℝ) * (1 - a)) := by
    have hqpos : (0 : ℝ) < q := lt_trans ha0 haq
    have h1a : (0 : ℝ) < 1 - a := by linarith
    apply div_pos (by linarith) (by positivity)
  linarith [hbound, hpos]







theorem tildePc_le_pc
    (hsub : ∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) :
    tildePc d ≤ pc d := by
  
  have hsubset : tildePcSet d ⊆ subcriticalSet d := by
    intro p hp
    obtain ⟨hp1, _⟩ := (mem_tildePcSet (p := p)).mp hp
    exact ⟨hp1, theta_eq_zero_of_crossProb_decay p hp1 (hsub p hp hp1)⟩
  unfold tildePc pc
  rcases (tildePcSet d).eq_empty_or_nonempty with hempty | hne
  · rw [hempty, csSup_empty]; exact bot_le
  · exact csSup_le_csSup subcriticalSet_bddAbove hne hsubset






theorem pc_le_tildePc
    (htheta_one : ∀ h1 : (1 : ℝ≥0) ≤ 1, theta d 1 h1 ≠ 0)
    (hmf : ∀ q : ℝ≥0, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 → 0 < theta d q hq) :
    pc d ≤ tildePc d := by
  unfold pc
  rcases (subcriticalSet d).eq_empty_or_nonempty with hempty | hne
  · rw [hempty, csSup_empty]; exact bot_le
  · refine csSup_le hne ?_
    intro q hq
    obtain ⟨hq1, hθ⟩ := (mem_subcriticalSet (p := q)).mp hq
    by_contra hlt
    rw [not_le] at hlt
    
    rcases lt_or_eq_of_le hq1 with hqlt1 | hqeq1
    · 
      have hqlt1' : (q : ℝ) < 1 := by exact_mod_cast hqlt1
      exact absurd hθ (ne_of_gt (hmf q hq1 hlt hqlt1'))
    · 
      subst hqeq1
      exact htheta_one hq1 hθ




theorem tildePc_eq_pc
    (htheta_one : ∀ h1 : (1 : ℝ≥0) ≤ 1, theta d 1 h1 ≠ 0)
    (hsub : ∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n))
    (hmf : ∀ q : ℝ≥0, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 → 0 < theta d q hq) :
    tildePc d = pc d :=
  le_antisymm (tildePc_le_pc hsub) (pc_le_tildePc htheta_one hmf)






















theorem sharpness (htildePc_pos : 0 < (tildePc d : ℝ))
    (htheta_one : ∀ h1 : (1 : ℝ≥0) ≤ 1, theta d 1 h1 ≠ 0)
    (hsub : ∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n))
    (F' : ℕ → ℝ≥0 → ℝ → ℝ)
    (hcont : ∀ q : ℝ≥0, tildePc d < q → (q : ℝ) < 1 → ∀ n,
        ContinuousOn (crossProbReal d (n + 1)) (Icc (tildePc d : ℝ) (q : ℝ)))
    (hderiv : ∀ q : ℝ≥0, tildePc d < q → (q : ℝ) < 1 → ∀ n,
        ∀ t ∈ Ioo (tildePc d : ℝ) (q : ℝ), HasDerivAt (crossProbReal d (n + 1)) (F' n q t) t)
    (hdiffineq : ∀ q : ℝ≥0, tildePc d < q → (q : ℝ) < 1 → ∀ n,
        ∀ t ∈ Ioo (tildePc d : ℝ) (q : ℝ),
        F' n q t ≥ (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t)) :
    tildePc d = pc d ∧
      (∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) ∧
      (∀ q : ℝ≥0, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 →
        theta d q hq ≥ ((q : ℝ) - (tildePc d : ℝ)) / ((q : ℝ) * (1 - (tildePc d : ℝ)))) := by
  
  have hmf : ∀ q : ℝ≥0, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 → 0 < theta d q hq := by
    intro q hq hlt hqlt1
    exact theta_pos_of_meanField q hq (tildePc d : ℝ) htildePc_pos
      (by exact_mod_cast hlt) hqlt1 (F' · q)
      (hcont q hlt hqlt1) (hderiv q hlt hqlt1) (hdiffineq q hlt hqlt1)
  refine ⟨tildePc_eq_pc htheta_one hsub hmf, hsub, ?_⟩
  intro q hq hlt hqlt1
  exact theta_ge_meanField q hq (tildePc d : ℝ) htildePc_pos
    (by exact_mod_cast hlt) hqlt1 (F' · q)
    (hcont q hlt hqlt1) (hderiv q hlt hqlt1) (hdiffineq q hlt hqlt1)

end Percolation

end StatMech
