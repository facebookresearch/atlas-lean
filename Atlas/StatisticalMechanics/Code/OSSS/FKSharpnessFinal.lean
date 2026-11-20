/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Code.OSSS.FKSharpnessUncond
import Code.Inequalities.Russo
import Code.BeffaraDC.RussoInfluence
import Code.BeffaraDC.RussoHamming

open scoped BigOperators
open Finset
open Real Set
open StatMech.Lattice

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace OSSS

open StatMech.OSSS.CovLowerBound
open StatMech.OSSS.SharpnessFK
open StatMech.OSSS.RevealmentConstruction
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

















lemma expect_bernoulliWeight (x : ℝ) (g : ConfigSpace E → ℝ) :
    expect (bernoulliWeight (E := E) x) g = StatMech.BeffaraDC.expect x g := by
  unfold expect StatMech.BeffaraDC.expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  show weight (bernoulliWeight x) ω * g ω = g ω * StatMech.configWeight x ω
  rw [show weight (bernoulliWeight (E := E) x) ω = StatMech.configWeight x ω from rfl]
  ring




lemma expect_indicator_bernoulli (x : ℝ) (A : Set (ConfigSpace E)) :
    expect (bernoulliWeight (E := E) x) (A.indicator (fun _ => (1 : ℝ))) = StatMech.prob x A := by
  rw [expect_bernoulliWeight]; exact StatMech.BeffaraDC.expect_indicator x A



lemma coordI_eq_openEdge_indicator (e : E) :
    coordI (E := E) e = (StatMech.BeffaraDC.openEdge e).indicator (fun _ => (1 : ℝ)) := by
  funext ω; unfold coordI; rw [StatMech.BeffaraDC.openEdge_indicator]







lemma cov_coordI_indicator_bernoulli (x : ℝ) (A : Set (ConfigSpace E)) (e : E) :
    cov (bernoulliWeight (E := E) x) (coordI e) (A.indicator (fun _ => (1 : ℝ)))
      = StatMech.prob x (A ∩ StatMech.BeffaraDC.openEdge e)
        - StatMech.prob x (StatMech.BeffaraDC.openEdge e) * StatMech.prob x A := by
  unfold cov
  rw [coordI_eq_openEdge_indicator]
  have h1 : expect (bernoulliWeight (E := E) x)
      (fun ω => (StatMech.BeffaraDC.openEdge e).indicator (fun _ => (1 : ℝ)) ω
        * A.indicator (fun _ => (1 : ℝ)) ω)
      = StatMech.prob x (A ∩ StatMech.BeffaraDC.openEdge e) := by
    rw [← expect_indicator_bernoulli]
    congr 1
    funext ω
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ StatMech.BeffaraDC.openEdge e <;> simp_all
  rw [h1, expect_indicator_bernoulli, expect_indicator_bernoulli]























theorem hasDerivAt_crossing_bernoulli (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (fun x => expect (bernoulliWeight (E := E) x) (A.indicator (fun _ => (1 : ℝ))))
      ((1 / (x * (1 - x)))
        * ∑ e, cov (bernoulliWeight (E := E) x) (coordI e) (A.indicator (fun _ => (1 : ℝ)))) x := by
  have hfun : (fun x => expect (bernoulliWeight (E := E) x) (A.indicator (fun _ => (1 : ℝ))))
      = (fun x => StatMech.prob x A) := by
    funext x; rw [expect_indicator_bernoulli]
  rw [hfun]
  have hd := StatMech.hasDerivAt_prob_eq_sum_pivotalProb A hA x
  have hval : (∑ e, StatMech.pivotalProb x A e)
      = (1 / (x * (1 - x)))
          * ∑ e, cov (bernoulliWeight (E := E) x) (coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
    have hne : x * (1 - x) ≠ 0 := mul_ne_zero hx0 (by intro h; exact hx1 (by linarith))
    rw [Finset.sum_congr rfl (fun e _ => cov_coordI_indicator_bernoulli x A e)]
    rw [StatMech.BeffaraDC.sum_cov_eq x A hA]
    field_simp
  rw [hval] at hd
  exact hd










lemma expect_indicator_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (A : Set (ConfigSpace E)) :
    0 ≤ expect ν (A.indicator (fun _ => (1 : ℝ))) := by
  apply expect_nonneg hν
  intro ω
  rw [Set.indicator_apply]
  split_ifs <;> norm_num



lemma expect_indicator_le_one {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (A : Set (ConfigSpace E)) :
    expect ν (A.indicator (fun _ => (1 : ℝ))) ≤ 1 := by
  have h := expect_mono hν (g := A.indicator (fun _ => (1 : ℝ))) (h := fun _ => (1 : ℝ))
    (fun ω => by rw [Set.indicator_apply]; split_ifs <;> norm_num)
  rwa [expect_one hν] at h

section Lattice

variable {d : ℕ}






























theorem pointwise_di_bernoulli {n : ℕ} (hn : 1 ≤ n)
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
    (μ : Site d → ℕ → ℝ) (hμ : ∀ y j, 0 ≤ μ y j)
    (ru rv : E → ℕ) (hru : ∀ e, ru e ≤ n) (hrv : ∀ e, rv e ≤ n)
    (hΛu : ∀ e, endU e ∈ Λ) (hΛv : ∀ e, endV e ∈ Λ)
    (Dval : ℝ) (hDpos : 0 < Dval)
    (hDeq : Dval = 4 * Λ.sup' hΛne (fun y => ∑ j ∈ Finset.range (n + 1), μ y j))
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hcompu : ∀ e k, expect (bernoulliWeight (E := E) x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μ (endU e) ((k : ℤ) - (ru e : ℤ)).natAbs)
    (hcompv : ∀ e k, expect (bernoulliWeight (E := E) x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μ (endV e) ((k : ℤ) - (rv e : ℤ)).natAbs)
    (κ : ℝ)
    (hθub : expect (bernoulliWeight (E := E) x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ 1 - κ) :
    (n : ℝ) * κ / Dval
        * expect (bernoulliWeight (E := E) x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ)))
      ≤ (1 / (x * (1 - x)))
          * ∑ e, cov (bernoulliWeight (E := E) x) (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) := by
  set θ := expect (bernoulliWeight (E := E) x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) with hθdef
  set S := ∑ e, cov (bernoulliWeight (E := E) x) (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) with hSdef
  have hxx : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  
  have hbase := cov_crossbox_uncond (E := E) (d := d) hn
    (bernoulliWeight_isProbWeight hx0.le hx1.le) hinj hcoh hadj o ho l hl
    disc₀ hdisc₀sub hdisc₀sup hoB Λ hΛne μ hμ ru rv hru hrv hΛu hΛv
    hcompu hcompv (x * (1 - x)) hxx.le
    (fun e => by
      show x * (1 - x) ≤ bernoulliWeight (E := E) x e true * bernoulliWeight (E := E) x e false
      unfold bernoulliWeight; simp)
  rw [← hθdef, ← hSdef, ← hDeq] at hbase
  
  have hθnn : 0 ≤ θ := expect_indicator_nonneg (bernoulliWeight_isProbWeight hx0.le hx1.le) _
  
  have hfac : θ * κ ≤ θ * (1 - θ) := mul_le_mul_of_nonneg_left (by linarith) hθnn
  
  have hstep : (n : ℝ) * (x * (1 - x)) * (θ * κ) ≤ Dval * S := by
    refine le_trans ?_ hbase
    apply mul_le_mul_of_nonneg_left hfac
    exact mul_nonneg (by positivity) hxx.le
  
  rw [div_mul_eq_mul_div, one_div, inv_mul_eq_div, div_le_div_iff₀ hDpos hxx]
  calc (n : ℝ) * κ * θ * (x * (1 - x))
      = (n : ℝ) * (x * (1 - x)) * (θ * κ) := by ring
    _ ≤ Dval * S := hstep
    _ = S * Dval := by ring








































theorem osss_fk_sharpness_final {n : ℕ} (hn : 1 ≤ n)
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
    (μ : Site d → ℕ → ℝ) (hμ : ∀ y j, 0 ≤ μ y j)
    (ru rv : E → ℕ) (hru : ∀ e, ru e ≤ n) (hrv : ∀ e, rv e ≤ n)
    (hΛu : ∀ e, endU e ∈ Λ) (hΛv : ∀ e, endV e ∈ Λ)
    (Dval : ℝ) (hDpos : 0 < Dval)
    (hDeq : Dval = 4 * Λ.sup' hΛne (fun y => ∑ j ∈ Finset.range (n + 1), μ y j))
    (κ : ℝ) (hκ : 0 < κ) (a b : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1)
    (hcompu : ∀ x ∈ Icc a b, ∀ e k, expect (bernoulliWeight (E := E) x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μ (endU e) ((k : ℤ) - (ru e : ℤ)).natAbs)
    (hcompv : ∀ x ∈ Icc a b, ∀ e k, expect (bernoulliWeight (E := E) x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μ (endV e) ((k : ℤ) - (rv e : ℤ)).natAbs)
    (hθub : ∀ x ∈ Icc a b, expect (bernoulliWeight (E := E) x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ 1 - κ) :
    expect (bernoulliWeight (E := E) a) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ)))
      ≤ Real.exp (-((n : ℝ) * κ / Dval * (b - a))) := by
  
  have hAinc : IsIncreasing (crossEvent edge o (vertexBoundary d n)) := by
    unfold crossEvent
    exact connectedToSet_increasing edge o (vertexBoundary d n)
  set θn : ℝ → ℝ :=
    fun x => expect (bernoulliWeight (E := E) x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) with hθndef
  set θn' : ℝ → ℝ :=
    fun x => (1 / (x * (1 - x)))
      * ∑ e, cov (bernoulliWeight (E := E) x) (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) with hθn'def
  set rate : ℝ := (n : ℝ) * κ / Dval with hratedef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hrate : 0 < rate := by
    rw [hratedef]; exact div_pos (mul_pos hnpos hκ) hDpos
  
  have hxbounds : ∀ x ∈ Icc a b, 0 < x ∧ x < 1 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
  
  have hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    rw [hθndef, hθn'def]
    exact hasDerivAt_crossing_bernoulli (crossEvent edge o (vertexBoundary d n)) hAinc
      hx0.ne' (by intro h; exact (lt_irrefl (1 : ℝ)) (h ▸ hx1))
  
  have hineq : ∀ x ∈ Icc a b, rate * θn x ≤ θn' x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    rw [hratedef, hθndef, hθn'def]
    exact pointwise_di_bernoulli hn hinj hcoh hadj o ho l hl disc₀
      hdisc₀sub hdisc₀sup hoB Λ hΛne μ hμ ru rv hru hrv hΛu hΛv Dval hDpos hDeq
      x hx0 hx1 (hcompu x hx) (hcompv x hx) κ (hθub x hx)
  
  have hθa : 0 ≤ θn a := by
    rw [hθndef]
    obtain ⟨ha0', ha1'⟩ := hxbounds a (left_mem_Icc.2 hab.le)
    exact expect_indicator_nonneg (bernoulliWeight_isProbWeight ha0'.le ha1'.le) _
  have hθb : θn b ≤ 1 := by
    rw [hθndef]
    obtain ⟨hb0', hb1'⟩ := hxbounds b (right_mem_Icc.2 hab.le)
    exact expect_indicator_le_one (bernoulliWeight_isProbWeight hb0'.le hb1'.le) _
  
  have hfin := subcritical_decay a b rate hab hrate θn θn' hd hineq hθa hθb
  exact hfin.2.1

end Lattice

end OSSS
end StatMech
