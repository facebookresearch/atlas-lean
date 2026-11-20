/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Code.OSSS.CovLowerBound
import Code.OSSS.Revealment

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech
namespace OSSS.SharpnessFK

open StatMech.OSSS
open StatMech.OSSS.CovLowerBound
open StatMech.OSSS.Revealment
open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {ν : E → Bool → ℝ}
















theorem var_indicator (f : ConfigSpace E → ℝ) (hf : ∀ ω, f ω = 0 ∨ f ω = 1) :
    var ν f = expect ν f * (1 - expect ν f) := by
  unfold var cov
  have hsq : expect ν (fun ω => f ω * f ω) = expect ν f := by
    unfold expect
    apply Finset.sum_congr rfl
    intro ω _
    rcases hf ω with h | h <;> simp only [h] <;> ring
  rw [hsq]; ring

omit [Fintype E] [DecidableEq E] in

lemma indicator_zero_or_one (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    A.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ A.indicator (fun _ => (1 : ℝ)) ω = 1 := by
  by_cases h : ω ∈ A
  · right; rw [Set.indicator_of_mem h]
  · left; rw [Set.indicator_of_notMem h]



theorem var_eventIndicator (A : Set (ConfigSpace E)) :
    var ν (A.indicator (fun _ => (1 : ℝ)))
      = expect ν (A.indicator (fun _ => (1 : ℝ)))
        * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))) :=
  var_indicator _ (indicator_zero_or_one A)




















theorem covSum_ge_of_indicator {κ : Type*} [Fintype κ] [Nonempty κ]
    (hν : IsProbWeight ν) {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    (T : κ → DecisionTree E)
    (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → E → ℝ) (hR : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hD : ∀ e, (∑ k, R k e) ≤ D) :
    (Fintype.card κ : ℝ) * c₀
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ D * ∑ e, cov ν (coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
  have hmain := cov_lower_bound hν hA (f := A.indicator (fun _ => (1 : ℝ))) rfl
    T hT R hR c₀ hc₀nn hc₀ D hDnn hD
  rwa [var_eventIndicator A] at hmain

















theorem gronwall_lower (a b lam : ℝ) (hab : a ≤ b) (f f' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x) :
    Real.exp (lam * (b - a)) * f a ≤ f b := by
  
  
  set h : ℝ → ℝ := fun x => f x * Real.exp (-lam * x) with hh
  have hderiv : ∀ x ∈ Icc a b,
      HasDerivAt h ((f' x - lam * f x) * Real.exp (-lam * x)) x := by
    intro x hx
    have hlin : HasDerivAt (fun y : ℝ => -lam * y) (-lam) x := by
      simpa using (hasDerivAt_id x).const_mul (-lam)
    have h1 : HasDerivAt (fun y => Real.exp (-lam * y)) (Real.exp (-lam * x) * (-lam)) x :=
      (Real.hasDerivAt_exp (-lam * x)).comp x hlin
    have hp := (hd x hx).mul h1
    convert hp using 1; ring
  
  have hmono : MonotoneOn h (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun x hx => (hderiv x (by simpa using hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x (mem_Icc_of_Ioo hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x (mem_Icc_of_Ioo hx)).deriv]
      apply mul_nonneg
      · have := hineq x (mem_Icc_of_Ioo hx); linarith
      · exact (Real.exp_pos _).le
  
  have hle := hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  rw [hh] at hle
  simp only [] at hle
  have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_pos (lam * b)).le
  have e1 : Real.exp (-lam * a) * Real.exp (lam * b) = Real.exp (lam * (b - a)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-lam * b) * Real.exp (lam * b) = 1 := by
    rw [← Real.exp_add, show -lam * b + lam * b = 0 by ring, Real.exp_zero]
  have lhs : f a * Real.exp (-lam * a) * Real.exp (lam * b)
      = Real.exp (lam * (b - a)) * f a := by rw [mul_assoc, e1]; ring
  have rhs : f b * Real.exp (-lam * b) * Real.exp (lam * b) = f b := by
    rw [mul_assoc, e2, mul_one]
  rw [lhs, rhs] at hmul
  exact hmul






















theorem differential_inequality (n : ℕ) (c₀ cR D θ θ' S : ℝ)
    (hD : 0 < D)
    (hcov : (n : ℝ) * c₀ * (θ * (1 - θ)) ≤ D * S)
    (hRusso : cR * S ≤ θ')
    (hcR : 0 ≤ cR) :
    (n : ℝ) * c₀ * cR / D * (θ * (1 - θ)) ≤ θ' := by
  have hSlb : (n : ℝ) * c₀ * (θ * (1 - θ)) / D ≤ S := by
    rw [div_le_iff₀ hD]; linarith [hcov]
  have hmul : cR * ((n : ℝ) * c₀ * (θ * (1 - θ)) / D) ≤ cR * S :=
    mul_le_mul_of_nonneg_left hSlb hcR
  calc (n : ℝ) * c₀ * cR / D * (θ * (1 - θ))
      = cR * ((n : ℝ) * c₀ * (θ * (1 - θ)) / D) := by ring
    _ ≤ cR * S := hmul
    _ ≤ θ' := hRusso




























theorem subcritical_decay (a b rate : ℝ) (hab : a < b) (hrate : 0 < rate)
    (θn θn' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
    (hineq : ∀ x ∈ Icc a b, rate * θn x ≤ θn' x)
    (hθa : 0 ≤ θn a) (hθb : θn b ≤ 1) :
    0 ≤ θn a ∧ θn a ≤ Real.exp (-(rate * (b - a)))
      ∧ Real.exp (-(rate * (b - a))) < 1 := by
  refine ⟨hθa, ?_, ?_⟩
  · 
    have hg := gronwall_lower a b rate hab.le θn θn' hd hineq
    have h1 : Real.exp (rate * (b - a)) * θn a ≤ 1 := hg.trans hθb
    have hpos := Real.exp_pos (rate * (b - a))
    have key : θn a ≤ 1 / Real.exp (rate * (b - a)) := by
      rw [le_div_iff₀ hpos]; linarith [h1]
    rw [Real.exp_neg]; rwa [one_div] at key
  · 
    rw [Real.exp_lt_one_iff]
    have hpos : 0 < rate * (b - a) := mul_pos hrate (by linarith)
    linarith




theorem subcritical_decay_box (a b c : ℝ) (n : ℕ) (hab : a < b)
    (hc : 0 < c) (hn : 1 ≤ n) (θn θn' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
    (hineq : ∀ x ∈ Icc a b, (c * n) * θn x ≤ θn' x)
    (hθa : 0 ≤ θn a) (hθb : θn b ≤ 1) :
    θn a ≤ Real.exp (-(c * n * (b - a))) := by
  have hrate : 0 < c * (n : ℝ) := by
    apply mul_pos hc
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  exact (subcritical_decay a b (c * n) hab hrate θn θn' hd hineq hθa hθb).2.1
























theorem potts_decay_of_fk (q : ℝ) (hq : 2 ≤ q) (c pottsCorr fkCross : ℝ)
    (hES : pottsCorr = (q - 1) / q * fkCross)
    (hfk_nonneg : 0 ≤ fkCross) (hfk_decay : fkCross ≤ Real.exp (-c)) :
    0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-c) := by
  have hqpos : 0 < q := by linarith
  have hcoef_nonneg : 0 ≤ (q - 1) / q := by
    apply div_nonneg (by linarith) hqpos.le
  have hcoef_le_one : (q - 1) / q ≤ 1 := by
    rw [div_le_one hqpos]; linarith
  constructor
  · rw [hES]; exact mul_nonneg hcoef_nonneg hfk_nonneg
  · rw [hES]
    calc (q - 1) / q * fkCross
        ≤ 1 * fkCross := mul_le_mul_of_nonneg_right hcoef_le_one hfk_nonneg
      _ = fkCross := one_mul _
      _ ≤ Real.exp (-c) := hfk_decay

end OSSS.SharpnessFK
end StatMech
