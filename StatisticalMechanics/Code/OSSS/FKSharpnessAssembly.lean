/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































































import Code.OSSS.Lindeberg
import Code.OSSS.SharpnessFK
import Code.OSSS.Integration
import Code.FK.RussoDerivative
import Code.FK.FKQ2Sharp
import Code.Inequalities.IncreasingEvent

open scoped BigOperators Classical
open Finset Real Set Filter Topology

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace OSSS

open StatMech.OSSS.Lindeberg
open StatMech.OSSS.SharpnessFK
open StatMech.FK
open MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V]















theorem lind_var_indicator {μ : ConfigSpace (Sym2 V) → ℝ}
    (f : ConfigSpace (Sym2 V) → ℝ) (hf : ∀ ω, f ω = 0 ∨ f ω = 1) :
    Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) := by
  unfold Lindeberg.var Lindeberg.cov
  have hsq : Lindeberg.mean μ (fun ω => f ω * f ω) = Lindeberg.mean μ f := by
    unfold Lindeberg.mean
    apply Finset.sum_congr rfl
    intro ω _
    rcases hf ω with h | h <;> simp only [h] <;> ring
  rw [hsq]; ring























theorem fk_poincare_indicator (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A) :
    fkProbOf G p q A * (1 - fkProbOf G p q A)
      ≤ ∑ e, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
  classical
  have hvar := Lindeberg.fk_monotonic_poincare G hp hp1 hq
    (f := A.indicator (fun _ => (1 : ℝ)))
    (hA.indicator_monotone)
    (StatMech.indicator_nonneg' A)
    (fun ω => by rw [Set.indicator_apply]; split_ifs <;> norm_num)
  rwa [lind_var_indicator (A.indicator (fun _ => (1 : ℝ)))
      (fun ω => by
        by_cases h : ω ∈ A
        · right; rw [Set.indicator_of_mem h]
        · left; rw [Set.indicator_of_notMem h])] at hvar



























theorem fk_differential_inequality (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (hbridge : ∑ e, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)) :
    russoPrefactor p * (fkProbOf G p q A * (1 - fkProbOf G p q A))
      ≤ deriv (fun p => fkProbOf G p q A) p := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hpoin := fk_poincare_indicator G hp hp1 hq A hA
  rw [hbridge] at hpoin
  refine le_trans ?_ (FK.russo_bound G hp hp1 hq0 A)
  exact mul_le_mul_of_nonneg_left hpoin (russoPrefactor_pos hp hp1).le




























theorem fk_subcritical_decay (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℝ} (hq : 1 ≤ q) (A : Set (ConfigSpace (Sym2 V)))
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hdi : ∀ x ∈ Icc a b,
       russoPrefactor x * (fkProbOf G x q A * (1 - fkProbOf G x q A))
        ≤ deriv (fun p => fkProbOf G p q A) x)
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x q A ≤ 1 - κ)
    (rate : ℝ) (hrate : 0 < rate)
    (hrlb : ∀ x ∈ Icc a b, rate ≤ russoPrefactor x * κ) :
    fkProbOf G a q A ≤ Real.exp (-(rate * (b - a))) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set θn : ℝ → ℝ := fun x => fkProbOf G x q A with hθn
  set θn' : ℝ → ℝ := fun x => deriv (fun p => fkProbOf G p q A) x with hθn'
  
  have hxbounds : ∀ x ∈ Icc a b, 0 < x ∧ x < 1 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
  
  have hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    show HasDerivAt θn (deriv (fun p => fkProbOf G p q A) x) x
    have hda := FK.hasDerivAt_fkProbOf G hx0 hx1 hq0 A
    rw [hda.deriv]; exact hda
  
  have hθnn : ∀ x ∈ Icc a b, 0 ≤ θn x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    exact FK.fkProbOf_nonneg G hx0 hx1 hq0 A
  
  have hineq : ∀ x ∈ Icc a b, rate * θn x ≤ θn' x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    have hθ := hθnn x hx
    have hfac : θn x * κ ≤ θn x * (1 - θn x) :=
      mul_le_mul_of_nonneg_left (by have := hθub x hx; linarith) hθ
    have hpref_nn : 0 ≤ russoPrefactor x := (russoPrefactor_pos hx0 hx1).le
    calc rate * θn x ≤ (russoPrefactor x * κ) * θn x :=
            mul_le_mul_of_nonneg_right (hrlb x hx) hθ
      _ = russoPrefactor x * (θn x * κ) := by ring
      _ ≤ russoPrefactor x * (θn x * (1 - θn x)) :=
            mul_le_mul_of_nonneg_left hfac hpref_nn
      _ ≤ θn' x := hdi x hx
  have hθa : 0 ≤ θn a := hθnn a (left_mem_Icc.2 hab.le)
  have hθb : θn b ≤ 1 := by have := hθub b (right_mem_Icc.2 hab.le); linarith
  
  have hfin := subcritical_decay a b rate hab hrate θn θn' hd hineq hθa hθb
  exact hfin.2.1




























theorem fk_q2_crossing_decay_poincare (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hbridge : ∀ p ∈ Icc a b,
      ∑ e, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
        = ∑ e ∈ G.edgeFinset, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    (hθub : ∀ p ∈ Icc a b, fkProbOf G p 2 A ≤ 1 - κ) :
    fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a))) := by
  
  have hFKcov : ∀ p ∈ Icc a b, ((1 : ℕ) : ℝ) * 1
        * (fkProbOf G p 2 A * (1 - fkProbOf G p 2 A))
      ≤ 1 * ∑ e ∈ G.edgeFinset,
          fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
    intro p hp
    rw [Set.mem_Icc] at hp
    have hp0 : 0 < p := lt_of_lt_of_le ha0 hp.1
    have hp1 : p < 1 := lt_of_le_of_lt hp.2 hb1
    have hpoin := fk_poincare_indicator G hp0 hp1 (by norm_num : (1 : ℝ) ≤ 2) A hA
    rw [hbridge p (Set.mem_Icc.2 hp)] at hpoin
    simp only [Nat.cast_one, one_mul]
    exact hpoin
  
  have hdiff : ∀ p ∈ Icc a b,
      HasDerivAt (fun p => fkProbOf G p 2 A) (deriv (fun p => fkProbOf G p 2 A) p) p := by
    intro p hp
    rw [Set.mem_Icc] at hp
    have hp0 : 0 < p := lt_of_lt_of_le ha0 hp.1
    have hp1 : p < 1 := lt_of_le_of_lt hp.2 hb1
    have hda := FK.hasDerivAt_fkProbOf G hp0 hp1 (by norm_num : (0 : ℝ) < 2) A
    rw [hda.deriv]; exact hda
  
  have h := FK.fk_q2_crossing_decay G (n := 1) le_rfl A 1 1 κ one_pos one_pos hκ
    a b hab ha0 hb1 hdiff hFKcov hθub
  have he : (4 * ((1 : ℕ) : ℝ) * 1 * κ / 1 * (b - a)) = 4 * κ * (b - a) := by
    push_cast; ring
  rwa [he] at h



























theorem fk_meanField_lower
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    β - β' ≤ fβ - fβ' :=
  Integration.meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound


























theorem fk_sharpness_both (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℝ} (hq : 1 ≤ q) (A : Set (ConfigSpace (Sym2 V)))
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hdi : ∀ x ∈ Icc a b,
       russoPrefactor x * (fkProbOf G x q A * (1 - fkProbOf G x q A))
        ≤ deriv (fun p => fkProbOf G p q A) x)
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x q A ≤ 1 - κ)
    (rate : ℝ) (hrate : 0 < rate)
    (hrlb : ∀ x ∈ Icc a b, rate ≤ russoPrefactor x * κ)
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    (fkProbOf G a q A ≤ Real.exp (-(rate * (b - a))))
      ∧ (β - β' ≤ fβ - fβ') :=
  ⟨fk_subcritical_decay G hq A a b κ hab ha0 hb1 hκ hdi hθub rate hrate hrlb,
   fk_meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound⟩






















theorem potts_decay_of_fk_sharpness (q : ℝ) (hq : 2 ≤ q)
    (c pottsCorr θ : ℝ)
    (hES : pottsCorr = (q - 1) / q * θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_decay : θ ≤ Real.exp (-c)) :
    0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-c) :=
  SharpnessFK.potts_decay_of_fk q hq c pottsCorr θ hES hθ_nonneg hθ_decay

end OSSS
end StatMech
