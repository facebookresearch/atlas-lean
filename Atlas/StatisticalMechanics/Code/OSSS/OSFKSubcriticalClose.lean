/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































































import Code.OSSS.HBridgeClose

open scoped BigOperators Classical
open Finset Real Set Filter Topology

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace OSSS
namespace OSFKSubcriticalClose

open StatMech.FK
open StatMech.OSSS.OSFKAssemblyClose
open StatMech.OSSS.BetaCMatch
open StatMech.OSSS.HBridgeClose

variable {V : Type*} [Fintype V] [DecidableEq V]



























theorem ofs_fk_q2_subcritical_decay_connEvent (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hθub : ∀ s ∈ Icc a b, fkProbOf G s 2 (connEvent G x y) ≤ 1 - κ) :
    fkProbOf G a 2 (connEvent G x y) ≤ Real.exp (-(4 * κ * (b - a))) :=
  hbg_fk_q2_subcritical_decay_connEvent G x y a b κ hab ha0 hb1 hκ hθub












theorem ofs_subcritical_bound_satisfiable {x y : V} (hxy : x ≠ y) (s : ℝ) :
    fkProbOf (⊥ : SimpleGraph V) s 2 (connEvent ⊥ x y) = 0 := by
  unfold fkProbOf fkMean
  apply Finset.sum_eq_zero
  intro ω _
  rw [Set.indicator_apply]
  simp only [mem_connEvent]
  rw [if_neg, zero_mul]
  intro hreach
  
  have hbot : openSub (⊥ : SimpleGraph V) ω = ⊥ := by
    ext a b
    simp only [openSub_adj, SimpleGraph.bot_adj, false_and]
  rw [hbot] at hreach
  exact hxy (SimpleGraph.reachable_bot.mp hreach)







theorem ofs_decay_self_at_diagonal (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    fkProbOf G s 2 (connEvent G x x) = 1 := by
  unfold fkProbOf
  rw [connEvent_self]
  
  have h1 : (Set.univ.indicator (fun _ => (1 : ℝ)) : ConfigSpace (Sym2 V) → ℝ)
      = fun _ => (1 : ℝ) := by
    funext ω; rw [Set.indicator_of_mem (Set.mem_univ ω)]
  rw [h1]
  exact fkMean_one G s 2 hs hs1 (by norm_num)
























theorem ofs_supercritical_meanField
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    β - β' ≤ fβ - fβ' :=
  ofa_fk_meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound














theorem ofs_betaC_eq_threshold (Θ : ℝ → ℝ) (β₁ : ℝ)
    (hP1 : ∀ b₀, b₀ < β₁ → Θ b₀ = 0)
    (hP2 : ∀ b₀, β₁ < b₀ → 0 < Θ b₀) :
    sSup (bcm_subcriticalSet Θ) = β₁ :=
  ofa_betaC_eq_threshold Θ β₁ hP1 hP2



























theorem ofs_fk_q2_sharpness_connEvent_minimal (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hθub : ∀ s ∈ Icc a b, fkProbOf G s 2 (connEvent G x y) ≤ 1 - κ)
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hboundMF : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β')
    (Θ : ℝ → ℝ) (β₁ : ℝ)
    (hP1 : ∀ b₀, b₀ < β₁ → Θ b₀ = 0)
    (hP2 : ∀ b₀, β₁ < b₀ → 0 < Θ b₀) :
    (fkProbOf G a 2 (connEvent G x y) ≤ Real.exp (-(4 * κ * (b - a))))
      ∧ (β - β' ≤ fβ - fβ')
      ∧ sSup (bcm_subcriticalSet Θ) = β₁ :=
  hbg_fk_q2_sharpness_connEvent G x y a b κ hab ha0 hb1 hκ hθub
    T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hboundMF Θ β₁ hP1 hP2
















theorem ofs_summary (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (hxy : x ≠ y) (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1)
    (hκ : 0 < κ)
    (hθub : ∀ s ∈ Icc a b, fkProbOf G s 2 (connEvent G x y) ≤ 1 - κ) :
    (fkProbOf G a 2 (connEvent G x y) ≤ Real.exp (-(4 * κ * (b - a))))
      ∧ (fkProbOf (⊥ : SimpleGraph V) a 2 (connEvent ⊥ x y) = 0) :=
  ⟨ofs_fk_q2_subcritical_decay_connEvent G x y a b κ hab ha0 hb1 hκ hθub,
   ofs_subcritical_bound_satisfiable hxy a⟩

end OSFKSubcriticalClose
end OSSS
end StatMech
