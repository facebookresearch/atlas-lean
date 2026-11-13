/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Code.OSSS.OSFKAssemblyClose
import Code.FK.TwoPoint
import Code.FK.FiniteEnergy

open scoped BigOperators Classical
open Finset Real Set Filter Topology

namespace StatMech
namespace OSSS
namespace HBridgeClose

open StatMech.FK
open StatMech.OSSS.OSFKAssemblyClose
open StatMech.OSSS.BetaCMatch

variable {V : Type*} [Fintype V] [DecidableEq V]





noncomputable def flipE (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) :=
  Function.update ω e (!ω e)

@[simp] theorem flipE_self (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    flipE e ω e = !ω e := by unfold flipE; simp

theorem flipE_of_ne {e e' : Sym2 V} (h : e' ≠ e) (ω : ConfigSpace (Sym2 V)) :
    flipE e ω e' = ω e' := by unfold flipE; rw [Function.update_of_ne h]


theorem flipE_flipE (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : flipE e (flipE e ω) = ω := by
  funext e'
  by_cases h : e' = e
  · subst h; simp
  · rw [flipE_of_ne h, flipE_of_ne h]


noncomputable def flipEquiv (e : Sym2 V) : ConfigSpace (Sym2 V) ≃ ConfigSpace (Sym2 V) where
  toFun := flipE e
  invFun := flipE e
  left_inv := flipE_flipE e
  right_inv := flipE_flipE e

@[simp] theorem flipEquiv_apply (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    flipEquiv e ω = flipE e ω := rfl



theorem coord_add_flip (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    coord e ω + coord e (flipE e ω) = 1 := by
  unfold coord
  simp only [flipE_self]
  cases ω e <;> simp



theorem mean_mul_coord_of_flip_invariant
    (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V)
    (hμ : ∀ ω, μ (flipE e ω) = μ ω)
    (f : ConfigSpace (Sym2 V) → ℝ) (hf : ∀ ω, f (flipE e ω) = f ω) :
    Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) =
      Lindeberg.mean μ f / 2 := by
  have hreindex : Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) =
      ∑ ω, f ω * Lindeberg.coord e (flipE e ω) * μ ω := by
    have hre :
        (∑ ω, (f ω * Lindeberg.coord e ω) * μ ω) =
          ∑ ω, (f (flipE e ω) * Lindeberg.coord e (flipE e ω)) * μ (flipE e ω) :=
      (Equiv.sum_comp (flipEquiv e)
        (fun ω => (f ω * Lindeberg.coord e ω) * μ ω)).symm
    unfold Lindeberg.mean
    rw [hre]
    apply Finset.sum_congr rfl
    intro ω _
    rw [hf, hμ]
  have hpair : ∀ ω, Lindeberg.coord e ω + Lindeberg.coord e (flipE e ω) = 1 := by
    intro ω
    unfold Lindeberg.coord
    simp only [flipE_self]
    cases ω e <;> simp
  have htwice :
      Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) +
        Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) =
          Lindeberg.mean μ f := by
    nth_rewrite 2 [hreindex]
    unfold Lindeberg.mean
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    rw [← add_mul, ← mul_add, hpair, mul_one]
  linarith



theorem cov_coord_of_flip_invariant
    (μ : ConfigSpace (Sym2 V) → ℝ) (hμ1 : ∑ ω, μ ω = 1) (e : Sym2 V)
    (hμ : ∀ ω, μ (flipE e ω) = μ ω)
    (f : ConfigSpace (Sym2 V) → ℝ) (hf : ∀ ω, f (flipE e ω) = f ω) :
    Lindeberg.cov μ f (Lindeberg.coord e) = 0 := by
  have hfc := mean_mul_coord_of_flip_invariant μ e hμ f hf
  have hc := mean_mul_coord_of_flip_invariant μ e hμ (fun _ => (1 : ℝ)) (fun _ => rfl)
  have hone : Lindeberg.mean μ (fun _ => (1 : ℝ)) = 1 :=
    Lindeberg.mean_const μ hμ1 1
  simp only [one_mul, hone] at hc
  unfold Lindeberg.cov
  rw [hfc, hc]
  ring



theorem covariance_support_bridge
    (μ : ConfigSpace (Sym2 V) → ℝ) (hμ1 : ∑ ω, μ ω = 1)
    (S : Finset (Sym2 V)) (f : ConfigSpace (Sym2 V) → ℝ)
    (hμ : ∀ e ∉ S, ∀ ω, μ (flipE e ω) = μ ω)
    (hf : ∀ e ∉ S, ∀ ω, f (flipE e ω) = f ω) :
    ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) =
      ∑ e ∈ S, Lindeberg.cov μ f (Lindeberg.coord e) := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  exact cov_coord_of_flip_invariant μ hμ1 e (hμ e he) f (hf e he)



variable (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℝ)



theorem openSub_flipE {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    openSub G (flipE e ω) = openSub G ω := by
  ext a b
  simp only [openSub_adj]
  refine and_congr_right (fun hadj => ?_)
  have hmem : s(a, b) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hadj
  have hne : s(a, b) ≠ e := by rintro rfl; exact he hmem
  rw [flipE_of_ne hne]



theorem fkWeight_flipE {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q (flipE e ω) = fkWeight G p q ω := by
  unfold fkWeight
  congr 1
  · 
    unfold edgeProduct
    apply Finset.prod_congr rfl
    intro e' he'
    have hne : e' ≠ e := by rintro rfl; exact he he'
    rw [flipE_of_ne hne]
  · 
    rw [numClusters_congr_openSub G (openSub_flipE G he ω)]




theorem hbg_fkProb_flipE {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    fkProb G p q (flipE e ω) = fkProb G p q ω := by
  unfold fkProb
  rw [fkWeight_flipE G p q he ω]




theorem fkMean_flip (g : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    fkMean G p q g = ∑ ω, g (flipE e ω) * fkProb G p q (flipE e ω) :=
  (Equiv.sum_comp (flipEquiv e) (fun ω => g ω * fkProb G p q ω)).symm




theorem fkMean_mul_coord_off {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (f : ConfigSpace (Sym2 V) → ℝ) (hf : ∀ ω, f (flipE e ω) = f ω) :
    fkMean G p q (fun ω => f ω * coord e ω) = fkMean G p q f / 2 := by
  have hreindex : fkMean G p q (fun ω => f ω * coord e ω)
      = ∑ ω, f ω * coord e (flipE e ω) * fkProb G p q ω := by
    rw [fkMean_flip G p q (fun ω => f ω * coord e ω) e]
    apply Finset.sum_congr rfl
    intro ω _
    rw [hf ω, hbg_fkProb_flipE G p q he ω]
  have hsum2 : fkMean G p q (fun ω => f ω * coord e ω)
        + fkMean G p q (fun ω => f ω * coord e ω) = fkMean G p q f := by
    nth_rewrite 2 [hreindex]
    rw [show fkMean G p q (fun ω => f ω * coord e ω)
        = ∑ ω, f ω * coord e ω * fkProb G p q ω from rfl, ← Finset.sum_add_distrib]
    unfold fkMean
    apply Finset.sum_congr rfl
    intro ω _
    have hc := coord_add_flip e ω
    have hrw : f ω * coord e ω * fkProb G p q ω + f ω * coord e (flipE e ω) * fkProb G p q ω
        = f ω * (coord e ω + coord e (flipE e ω)) * fkProb G p q ω := by ring
    rw [hrw, hc, mul_one]
  linarith


theorem fkMean_one (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkMean G p q (fun _ => (1 : ℝ)) = 1 := by
  unfold fkMean
  simp only [one_mul]
  exact fkProb_sum_eq_one G hp hp1 hq





theorem hbg_fkCov_coord_off (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (f : ConfigSpace (Sym2 V) → ℝ) (hf : ∀ ω, f (flipE e ω) = f ω) :
    fkCov G p q f (coord e) = 0 := by
  unfold fkCov
  have h1 : fkMean G p q (fun ω => f ω * coord e ω) = fkMean G p q f / 2 :=
    fkMean_mul_coord_off G p q he f hf
  have h2 : fkMean G p q (coord e) = 1 / 2 := by
    have := fkMean_mul_coord_off G p q he (fun _ => (1 : ℝ)) (fun _ => rfl)
    simp only [one_mul] at this
    rw [this, fkMean_one G p q hp hp1 hq]
  rw [h1, h2]; ring






theorem hbg_bridge (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (f : ConfigSpace (Sym2 V) → ℝ)
    (hf : ∀ e ∉ G.edgeFinset, ∀ ω, f (flipE e ω) = f ω) :
    ∑ e, fkCov G p q f (coord e)
      = ∑ e ∈ G.edgeFinset, fkCov G p q f (coord e) := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  exact hbg_fkCov_coord_off G p q hp hp1 hq he f (hf e he)






theorem hbg_event_bridge (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V)))
    (hA : ∀ e ∉ G.edgeFinset, ∀ ω, (flipE e ω ∈ A ↔ ω ∈ A)) :
    ∑ e, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e)
      = ∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e) := by
  apply hbg_bridge G p q hp hp1 hq
  intro e he ω
  unfold Set.indicator
  by_cases h : ω ∈ A
  · rw [if_pos h, if_pos ((hA e he ω).mpr h)]
  · rw [if_neg h, if_neg (fun hc => h ((hA e he ω).mp hc))]









theorem hbg_connEvent_offGraph {x y : V} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    flipE e ω ∈ connEvent G x y ↔ ω ∈ connEvent G x y := by
  simp only [mem_connEvent]
  rw [openSub_flipE G he ω]


theorem hbg_connEvent_bridge (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : V) :
    ∑ e, fkCov G p q ((connEvent G x y).indicator (fun _ => (1 : ℝ))) (coord e)
      = ∑ e ∈ G.edgeFinset,
          fkCov G p q ((connEvent G x y).indicator (fun _ => (1 : ℝ))) (coord e) :=
  hbg_event_bridge G p q hp hp1 hq (connEvent G x y)
    (fun _ he ω => hbg_connEvent_offGraph G he ω)














theorem hbg_fk_q2_subcritical_decay_connEvent (x y : V)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hθub : ∀ s ∈ Icc a b, fkProbOf G s 2 (connEvent G x y) ≤ 1 - κ) :
    fkProbOf G a 2 (connEvent G x y) ≤ Real.exp (-(4 * κ * (b - a))) :=
  ofa_fk_q2_subcritical_decay G (connEvent G x y) (connEvent_isIncreasing G x y)
    a b κ hab ha0 hb1 hκ
    (fun s hs => by
      have hs' := (Set.mem_Icc.mp hs)
      exact hbg_connEvent_bridge G s 2 (lt_of_lt_of_le ha0 hs'.1)
        (lt_of_le_of_lt hs'.2 hb1) (by norm_num) x y)
    hθub






theorem hbg_fk_q2_sharpness_connEvent (x y : V)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
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
  ofa_fk_q2_sharpness G (connEvent G x y) (connEvent_isIncreasing G x y)
    a b κ hab ha0 hb1 hκ
    (fun s hs => by
      have hs' := (Set.mem_Icc.mp hs)
      exact hbg_connEvent_bridge G s 2 (lt_of_lt_of_le ha0 hs'.1)
        (lt_of_le_of_lt hs'.2 hb1) (by norm_num) x y)
    hθub T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hboundMF Θ β₁ hP1 hP2






theorem hbg_potts_decay (q : ℝ) (hq : 2 ≤ q) (c pottsCorr θ : ℝ)
    (hES : pottsCorr = (q - 1) / q * θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_decay : θ ≤ Real.exp (-c)) :
    0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-c) :=
  ofa_potts_decay q hq c pottsCorr θ hES hθ_nonneg hθ_decay

end HBridgeClose
end OSSS
end StatMech
