/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2
import Code.Sharpness.GHSFull
import Code.Ising.AizenmanBarsky
import Code.Ising.GHSThreePoint

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]







noncomputable def isingExp3 (β h : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ) : ℝ :=
  ∑ a : ConfigSpace V, ∑ b : ConfigSpace V, ∑ c : ConfigSpace V,
    isingProb G β h a * isingProb G β h b * isingProb G β h c * F a b c






theorem isingExp3_factor (β h : ℝ) (f g k : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b c => f a * g b * k c)
      = isingExpectation G β h f * isingExpectation G β h g * isingExpectation G β h k := by
  unfold isingExp3 isingExpectation
  simp only []
  
  have hc : ∀ a b : ConfigSpace V,
      (∑ c : ConfigSpace V,
          isingProb G β h a * isingProb G β h b * isingProb G β h c * (f a * g b * k c))
        = (isingProb G β h a * f a) * (isingProb G β h b * g b)
            * (∑ c : ConfigSpace V, isingProb G β h c * k c) := by
    intro a b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_); ring
  have hb : ∀ a : ConfigSpace V,
      (∑ b : ConfigSpace V, ∑ c : ConfigSpace V,
          isingProb G β h a * isingProb G β h b * isingProb G β h c * (f a * g b * k c))
        = (isingProb G β h a * f a)
            * (∑ b : ConfigSpace V, isingProb G β h b * g b)
            * (∑ c : ConfigSpace V, isingProb G β h c * k c) := by
    intro a
    rw [Finset.sum_congr rfl (fun b _ => hc a b), ← Finset.sum_mul, ← Finset.mul_sum,
      mul_assoc]
  rw [Finset.sum_congr rfl (fun a _ => hb a), ← Finset.sum_mul, ← Finset.sum_mul]


@[simp] theorem isingExp3_one (β h : ℝ) :
    isingExp3 G β h (fun _ _ _ => (1 : ℝ)) = 1 := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp3_factor_c (β h : ℝ) (k : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun _ _ c => k c) = isingExpectation G β h k := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) k
  simpa [h1] using this


theorem isingExp3_factor_b (β h : ℝ) (g : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun _ b _ => g b) = isingExpectation G β h g := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h (fun _ => (1:ℝ)) g (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp3_factor_a (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a _ _ => f a) = isingExpectation G β h f := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h f (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp3_factor_ab (β h : ℝ) (f g : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b _ => f a * g b)
      = isingExpectation G β h f * isingExpectation G β h g := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h f g (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp3_factor_ac (β h : ℝ) (f k : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a _ c => f a * k c)
      = isingExpectation G β h f * isingExpectation G β h k := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h f (fun _ => (1:ℝ)) k
  simpa [h1] using this


theorem isingExp3_factor_bc (β h : ℝ) (g k : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun _ b c => g b * k c)
      = isingExpectation G β h g * isingExpectation G β h k := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h (fun _ => (1:ℝ)) g k
  simpa [h1] using this


theorem isingExp3_add (β h : ℝ)
    (F₁ F₂ : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b c => F₁ a b c + F₂ a b c)
      = isingExp3 G β h F₁ + isingExp3 G β h F₂ := by
  unfold isingExp3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring


theorem isingExp3_const_mul (β h : ℝ) (r : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b c => r * F a b c) = r * isingExp3 G β h F := by
  unfold isingExp3
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring







def dvar (a b c : ConfigSpace V) (w : V) : ℝ := spin b w + spin c w - 2 * spin a w

@[simp] lemma dvar_apply (a b c : ConfigSpace V) (w : V) :
    dvar a b c w = spin b w + spin c w - 2 * spin a w := rfl













theorem isingExp3_eq_iterated (β h : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp3 G β h F
      = isingExpectation G β h
          (fun a => isingExpectation G β h
            (fun b => isingExpectation G β h (fun c => F a b c))) := by
  unfold isingExp3 isingExpectation
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring



theorem isingExp3_finset_sum (β h : ℝ) {ι : Type*} (s : Finset ι)
    (F : ι → ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b c => ∑ i ∈ s, F i a b c)
      = ∑ i ∈ s, isingExp3 G β h (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [isingExp3]
  | @insert j s hj IH =>
    have hrw : (fun a b c => ∑ i ∈ insert j s, F i a b c)
        = (fun a b c => F j a b c + ∑ i ∈ s, F i a b c) := by
      funext a b c; rw [Finset.sum_insert hj]
    rw [hrw, isingExp3_add, IH, Finset.sum_insert hj]







theorem ghsDV_three_replica_expand (β h : ℝ) (o x y : V) :
    isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y)
      = (-6) * (isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x * spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s x)
              * isingExpectation G β h (fun s => spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s y)
              * isingExpectation G β h (fun s => spin s x)
          + 2 * isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x)
              * isingExpectation G β h (fun s => spin s y)) := by
  have hexp : (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y)
      = (fun a b c =>
          (1:ℝ) * ((spin b o * (spin b x * (spin b y))))
          + (1:ℝ) * ((spin b o * (spin b x)) * (spin c y))
          + (-2:ℝ) * ((spin a y) * (spin b o * (spin b x)))
          + (1:ℝ) * ((spin b o * (spin b y)) * (spin c x))
          + (1:ℝ) * ((spin b o) * (spin c x * (spin c y)))
          + (-2:ℝ) * ((spin a y) * (spin b o) * (spin c x))
          + (-2:ℝ) * ((spin a x) * (spin b o * (spin b y)))
          + (-2:ℝ) * ((spin a x) * (spin b o) * (spin c y))
          + (4:ℝ) * ((spin a x * (spin a y)) * (spin b o))
          + (1:ℝ) * ((spin b x * (spin b y)) * (spin c o))
          + (1:ℝ) * ((spin b x) * (spin c o * (spin c y)))
          + (-2:ℝ) * ((spin a y) * (spin b x) * (spin c o))
          + (1:ℝ) * ((spin b y) * (spin c o * (spin c x)))
          + (1:ℝ) * ((spin c o * (spin c x * (spin c y))))
          + (-2:ℝ) * ((spin a y) * (spin c o * (spin c x)))
          + (-2:ℝ) * ((spin a x) * (spin b y) * (spin c o))
          + (-2:ℝ) * ((spin a x) * (spin c o * (spin c y)))
          + (4:ℝ) * ((spin a x * (spin a y)) * (spin c o))
          + (-2:ℝ) * ((spin a o) * (spin b x * (spin b y)))
          + (-2:ℝ) * ((spin a o) * (spin b x) * (spin c y))
          + (4:ℝ) * ((spin a o * (spin a y)) * (spin b x))
          + (-2:ℝ) * ((spin a o) * (spin b y) * (spin c x))
          + (-2:ℝ) * ((spin a o) * (spin c x * (spin c y)))
          + (4:ℝ) * ((spin a o * (spin a y)) * (spin c x))
          + (4:ℝ) * ((spin a o * (spin a x)) * (spin b y))
          + (4:ℝ) * ((spin a o * (spin a x)) * (spin c y))
          + (-8:ℝ) * ((spin a o * (spin a x * (spin a y))))
          ) := by
    funext a b c; simp only [dvar_apply]; ring
  rw [hexp]
  simp only [isingExp3_add, isingExp3_const_mul, isingExp3_factor,
    isingExp3_factor_a, isingExp3_factor_b, isingExp3_factor_c,
    isingExp3_factor_ab, isingExp3_factor_ac, isingExp3_factor_bc]
  ring










theorem ghsDV_ursell_eq_three_replica (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y)
      = (-(1/6)) * isingExp3 G β h
          (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y) := by
  rw [ghsThreePoint_eq_ursell, ghsDV_three_replica_expand]
  ring









theorem ghsDV_ghs_iff_three_replica_nonneg (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y)
      ↔ 0 ≤ isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y) := by
  have hid := ghsDV_ursell_eq_three_replica G β h o x y
  rw [← sub_nonneg (a := ghsBoundSym G β h o s(x, y))]
  constructor
  · intro hle; nlinarith [hle, hid]
  · intro hge; nlinarith [hge, hid]











noncomputable def isingExp2 (β h : ℝ) (F : ConfigSpace V → ConfigSpace V → ℝ) : ℝ :=
  ∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
    isingProb G β h a * isingProb G β h b * F a b


theorem isingExp2_factor (β h : ℝ) (f g : ConfigSpace V → ℝ) :
    isingExp2 G β h (fun a b => f a * g b)
      = isingExpectation G β h f * isingExpectation G β h g := by
  unfold isingExp2 isingExpectation
  simp only []
  have hb : ∀ a : ConfigSpace V,
      (∑ b : ConfigSpace V, isingProb G β h a * isingProb G β h b * (f a * g b))
        = (isingProb G β h a * f a) * (∑ b : ConfigSpace V, isingProb G β h b * g b) := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_); ring
  rw [Finset.sum_congr rfl (fun a _ => hb a), ← Finset.sum_mul]


theorem isingExp2_add (β h : ℝ) (F₁ F₂ : ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp2 G β h (fun a b => F₁ a b + F₂ a b)
      = isingExp2 G β h F₁ + isingExp2 G β h F₂ := by
  unfold isingExp2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_); ring


theorem isingExp2_const_mul (β h : ℝ) (r : ℝ) (F : ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp2 G β h (fun a b => r * F a b) = r * isingExp2 G β h F := by
  unfold isingExp2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_); ring


theorem isingExp2_factor_a (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExp2 G β h (fun a _ => f a) = isingExpectation G β h f := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp2_factor G β h f (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp2_factor_b (β h : ℝ) (g : ConfigSpace V → ℝ) :
    isingExp2 G β h (fun _ b => g b) = isingExpectation G β h g := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp2_factor G β h (fun _ => (1:ℝ)) g
  simpa [h1] using this



noncomputable def uvar (a b : ConfigSpace V) (w : V) : ℝ := (spin a w - spin b w) / 2


noncomputable def tvar (a b : ConfigSpace V) (w : V) : ℝ := (spin a w + spin b w) / 2







theorem ghsDV_cov2_eq_two_uu (β h : ℝ) (o x : V) :
    cov2 G β h o x = 2 * isingExp2 G β h (fun a b => uvar a b o * uvar a b x) := by
  have hexp : (fun a b => uvar a b o * uvar a b x)
      = (fun a b =>
          (1/4 : ℝ) * (spin a o * spin a x)
          + (-1/4 : ℝ) * (spin a o * spin b x)
          + (-1/4 : ℝ) * (spin a x * spin b o)
          + (1/4 : ℝ) * (spin b o * spin b x)) := by
    funext a b; simp only [uvar]; ring
  rw [hexp]
  simp only [isingExp2_add, isingExp2_const_mul, isingExp2_factor,
    isingExp2_factor_a, isingExp2_factor_b]
  unfold cov2
  ring






theorem ghsDV_uu_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x : V) (hox : o ≠ x) :
    0 ≤ isingExp2 G β h (fun a b => uvar a b o * uvar a b x) := by
  have hc := cov2_nonneg G β h hβ hh o x hox
  rw [ghsDV_cov2_eq_two_uu] at hc
  linarith



theorem ghsDV_onePt_eq_tt (β h : ℝ) (o : V) :
    onePt G β h o = isingExp2 G β h (fun a b => tvar a b o) := by
  have hexp : (fun a b => tvar a b o)
      = (fun a b => (1/2 : ℝ) * spin a o + (1/2 : ℝ) * spin b o) := by
    funext a b; simp only [tvar]; ring
  rw [hexp]
  simp only [isingExp2_add, isingExp2_const_mul, isingExp2_factor_a, isingExp2_factor_b]
  unfold onePt
  ring



theorem ghsDV_tt_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ isingExp2 G β h (fun a b => tvar a b o) := by
  have hsp : (0 : ℝ) ≤ onePt G β h o := expectation_spin_nonneg G β h hβ hh o
  rwa [ghsDV_onePt_eq_tt] at hsp












theorem ghsDV_of_three_replica_nonneg (β h : ℝ) (o : V)
    (hsign : ∀ e ∈ G.edgeFinset, ∀ x y : V, e = s(x, y) →
      0 ≤ isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y)) :
    GHSThreePointSym G β h o := by
  intro e he
  induction e with
  | h x y =>
    exact (ghsDV_ghs_iff_three_replica_nonneg G β h o x y).mpr (hsign _ he x y rfl)

end Ising

end StatMech
