/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Code.OSSS.SharpnessUncond
import Code.OSSS.RevealmentCrossBox
import Code.OSSS.RevealmentSum

open scoped BigOperators
open Finset
open Real Set
open StatMech.Lattice

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace OSSS

open StatMech.OSSS
open StatMech.OSSS.CovLowerBound
open StatMech.OSSS.SharpnessFK
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.TreeComplete
open StatMech.OSSS.DecisionTree
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

section Lattice

variable {d : ℕ}













































theorem cov_crossbox_uncond {n : ℕ} (hn : 1 ≤ n)
    {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (l : List E) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (Λ : Finset (Site d)) (hΛne : Λ.Nonempty)
    (μ : Site d → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μ x j)
    (ru rv : E → ℕ) (hru : ∀ e, ru e ≤ n) (hrv : ∀ e, rv e ≤ n)
    (hΛu : ∀ e, endU e ∈ Λ) (hΛv : ∀ e, endV e ∈ Λ)
    (hcompu : ∀ e k, expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μ (endU e) ((k : ℤ) - (ru e : ℤ)).natAbs)
    (hcompv : ∀ e k, expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μ (endV e) ((k : ℤ) - (rv e : ℤ)).natAbs)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false) :
    (n : ℝ) * c₀
        * (expect ν ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ)))))
      ≤ (4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j))
          * ∑ e, cov ν (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) := by
  classical
  
  haveI hne : Nonempty (↥(Finset.Icc 1 n)) :=
    ⟨⟨1, by rw [Finset.mem_Icc]; exact ⟨le_refl 1, hn⟩⟩⟩
  set A : Set (ConfigSpace E) := crossEvent edge o (vertexBoundary d n) with hA0
  set Dval : ℝ := 4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) with hDdef
  
  have hAinc : IsIncreasing A := by
    rw [hA0]; unfold crossEvent; exact connectedToSet_increasing edge o (vertexBoundary d n)
  
  set T : ↥(Finset.Icc 1 n) → DecisionTree E :=
    fun k => crossTree endU endV o (vertexBoundary d n) l (disc₀ (k : ℕ)) with hTdef
  
  
  have hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)) := by
    intro k
    funext ω
    have hk1 : 1 ≤ (k : ℕ) := (Finset.mem_Icc.mp k.2).1
    have hkn : (k : ℕ) ≤ n := (Finset.mem_Icc.mp k.2).2
    have hokm1 : o ∈ box d ((k : ℕ) - 1) := ho (k : ℕ) hk1
    have heval := evalR_crossTree_connected (E := E) (d := d) hinj hcoh hadj
      (k : ℕ) n hk1 hkn o hokm1 l hl (disc₀ (k : ℕ))
      (hdisc₀sup (k : ℕ)) (hoB (k : ℕ)) ω
    rw [hTdef]; rw [heval]
    by_cases hconn : ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n)
    · have hmem : ω ∈ A := by rw [hA0]; exact hconn
      rw [if_pos hconn, Set.indicator_of_mem hmem]
    · have hmem : ω ∉ A := by rw [hA0]; exact hconn
      rw [if_neg hconn, Set.indicator_of_notMem hmem]
  
  
  set R : ↥(Finset.Icc 1 n) → E → ℝ :=
    fun k e => expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d (k : ℕ)) then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d (k : ℕ)) then (1 : ℝ) else 0) with hRdef
  have hR : ∀ k e, reveal ν (T k) e ≤ R k e := by
    intro k e
    rw [hTdef, hRdef]
    exact reveal_crossTree_le_connected (E := E) (d := d) hν hinj hcoh hadj o
      (vertexBoundary d n) (k : ℕ) l (disc₀ (k : ℕ)) (hdisc₀sub (k : ℕ)) e
  
  have hD : ∀ e, (∑ k, R k e) ≤ Dval := by
    intro e
    rw [hRdef, hDdef]
    rw [Finset.sum_coe_sort (Finset.Icc 1 n)
      (fun k => expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
            + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0))]
    exact revealment_family_sum_le Λ hΛne μ hμ n (ru e) (rv e) (hru e) (hrv e)
      (endU e) (endV e) (hΛu e) (hΛv e)
      (fun k => expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0))
      (fun k => expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0))
      (fun k => hcompu e k) (fun k => hcompv e k)
  
  have hDnn : 0 ≤ Dval := by
    rw [hDdef]
    apply mul_nonneg (by norm_num)
    obtain ⟨x₀, hx₀⟩ := hΛne
    refine le_trans ?_ (Finset.le_sup' (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) hx₀)
    exact Finset.sum_nonneg (fun j _ => hμ x₀ j)
  
  have hcard : (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) = n := by
    rw [Fintype.card_coe, Nat.card_Icc]
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub]
  have hmain := covSum_ge_of_indicator (κ := ↥(Finset.Icc 1 n)) hν hAinc T hT R hR
    c₀ hc₀nn hc₀ Dval hDnn hD
  rw [hcard] at hmain
  exact hmain


























theorem osss_differential_inequality_uncond (n : ℕ) (c₀ cR D θ θ' S : ℝ)
    (hD : 0 < D) (hcR : 0 < cR)
    (hcov : (n : ℝ) * c₀ * (θ * (1 - θ)) ≤ D * S)
    (hRussoEq : θ' = cR * S) :
    (n : ℝ) * c₀ * cR / D * (θ * (1 - θ)) ≤ θ' :=
  differential_inequality n c₀ cR D θ θ' S hD hcov (le_of_eq hRussoEq.symm) hcR.le














theorem theta_mul_one_sub_ge_of_bounded {θ κ : ℝ} (hθnn : 0 ≤ θ) (hθub : θ ≤ 1 - κ) :
    θ * κ ≤ θ * (1 - θ) :=
  mul_le_mul_of_nonneg_left (by linarith) hθnn





































theorem osss_subcritical_decay_uncond (n : ℕ) (c₀ cR D κ : ℝ) (a b : ℝ) (hab : a < b)
    (hD : 0 < D) (hcR : 0 < cR) (hc₀ : 0 < c₀) (hn : 1 ≤ n) (hκ : 0 < κ)
    (θn θn' S : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
    (hcov : ∀ x ∈ Icc a b, (n : ℝ) * c₀ * (θn x * (1 - θn x)) ≤ D * S x)
    (hRusso : ∀ x ∈ Icc a b, θn' x = cR * S x)
    (hθnn : ∀ x ∈ Icc a b, 0 ≤ θn x)
    (hθub : ∀ x ∈ Icc a b, θn x ≤ 1 - κ)
    (hθa : 0 ≤ θn a) (hθb : θn b ≤ 1) :
    θn a ≤ Real.exp (-((n : ℝ) * c₀ * cR / D * κ * (b - a))) := by
  set rate : ℝ := (n : ℝ) * c₀ * cR / D * κ with hrate0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hqpos : 0 < (n : ℝ) * c₀ * cR / D :=
    div_pos (mul_pos (mul_pos hnpos hc₀) hcR) hD
  have hrate : 0 < rate := by rw [hrate0]; exact mul_pos hqpos hκ
  
  have hineq : ∀ x ∈ Icc a b, rate * θn x ≤ θn' x := by
    intro x hx
    have hdi := osss_differential_inequality_uncond n c₀ cR D (θn x) (θn' x) (S x)
      hD hcR (hcov x hx) (hRusso x hx)
    have hfac : θn x * κ ≤ θn x * (1 - θn x) :=
      theta_mul_one_sub_ge_of_bounded (hθnn x hx) (hθub x hx)
    calc rate * θn x = (n : ℝ) * c₀ * cR / D * (θn x * κ) := by rw [hrate0]; ring
      _ ≤ (n : ℝ) * c₀ * cR / D * (θn x * (1 - θn x)) :=
            mul_le_mul_of_nonneg_left hfac hqpos.le
      _ ≤ θn' x := hdi
  
  have hfin := subcritical_decay a b rate hab hrate θn θn' hd hineq hθa hθb
  rw [hrate0] at hfin
  exact hfin.2.1



































theorem osss_crossing_decay_uncond {n : ℕ} (hn : 1 ≤ n)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (l : List E) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (Λ : Finset (Site d)) (hΛne : Λ.Nonempty)
    (ru rv : E → ℕ) (hru : ∀ e, ru e ≤ n) (hrv : ∀ e, rv e ≤ n)
    (hΛu : ∀ e, endU e ∈ Λ) (hΛv : ∀ e, endV e ∈ Λ)
    (ν : ℝ → E → Bool → ℝ) (hν : ∀ x, IsProbWeight (ν x))
    (μ : ℝ → Site d → ℕ → ℝ) (hμ : ∀ x p j, 0 ≤ μ x p j)
    (hcompu : ∀ x e k, expect (ν x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μ x (endU e) ((k : ℤ) - (ru e : ℤ)).natAbs)
    (hcompv : ∀ x e k, expect (ν x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μ x (endV e) ((k : ℤ) - (rv e : ℤ)).natAbs)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (hc₀le : ∀ x e, c₀ ≤ ν x e true * ν x e false)
    (cR κ : ℝ) (a b : ℝ) (hab : a < b) (hcR : 0 < cR) (hκ : 0 < κ)
    (Dval : ℝ) (hDpos : 0 < Dval)
    (hDeq : ∀ x ∈ Icc a b, Dval = 4 * Λ.sup' hΛne (fun y => ∑ j ∈ Finset.range (n + 1), μ x y j))
    (θn' S : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt
        (fun x => expect (ν x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ)))) (θn' x) x)
    (hScov : ∀ x ∈ Icc a b,
        S x = ∑ e, cov (ν x) (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))))
    (hRusso : ∀ x ∈ Icc a b, θn' x = cR * S x)
    (hθnn : ∀ x ∈ Icc a b, 0 ≤ expect (ν x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))))
    (hθub : ∀ x ∈ Icc a b, expect (ν x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ 1 - κ)
    (hθa : 0 ≤ expect (ν a) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))))
    (hθb : expect (ν b) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ 1) :
    expect (ν a) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ)))
      ≤ Real.exp (-((n : ℝ) * c₀ * cR / Dval * κ * (b - a))) := by
  classical
  set θn : ℝ → ℝ :=
    fun x => expect (ν x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) with hθndef
  
  have hcov : ∀ x ∈ Icc a b, (n : ℝ) * c₀ * (θn x * (1 - θn x)) ≤ Dval * S x := by
    intro x hx
    have hbase := cov_crossbox_uncond (E := E) (d := d) hn (hν x) hinj hcoh hadj o ho l hl
      disc₀ hdisc₀sub hdisc₀sup hoB Λ hΛne (μ x) (hμ x) ru rv hru hrv hΛu hΛv
      (hcompu x) (hcompv x) c₀ hc₀.le (hc₀le x)
    rw [hθndef, hScov x hx, hDeq x hx]
    exact hbase
  
  exact osss_subcritical_decay_uncond n c₀ cR Dval κ a b hab hDpos hcR hc₀ hn hκ
    θn θn' S hd hcov hRusso hθnn hθub hθa hθb

end Lattice

end OSSS
end StatMech
