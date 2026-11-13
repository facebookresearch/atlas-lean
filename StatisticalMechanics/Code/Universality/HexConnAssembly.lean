/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































































import Mathlib
import Code.Universality.HexConnEndgame
import Code.Universality.HexSurgerySeams

namespace StatMech.Universality

open Filter Topology
open scoped Topology Real NNReal














theorem hexConnAssembly_summable_zero (c : ℕ → ℝ) :
    Summable (fun n => c n * (0 : ℝ) ^ n) := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Set.finite_singleton 0)
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  simp only [Set.mem_singleton_iff]
  by_contra hne
  exact hn (by rw [zero_pow hne, mul_zero])














theorem hexConnAssembly_conv (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (Col : ∀ T, HexColumn T hexChiE)
    (HW : ∀ x, 0 < x → x < hexChiE →
      ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
    ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => c n * x ^ n) := by
  intro x hx0 hxlt
  rcases eq_or_lt_of_le hx0 with hx | hxpos
  · subst hx; exact hexConnAssembly_summable_zero c
  · exact hexZ_conv_seams_closed c x hxpos hxlt hc Col (HW x hxpos hxlt)



































theorem hex_connective_constant_assembled
    (c lam tau ups : ℕ → ℝ)
    (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
    
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = ups)
    
    (Col : ∀ T, HexColumn T hexChiE)
    (HW : ∀ x, 0 < x → x < hexChiE →
      ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) := by
  
  have hdiv : ¬ Summable (fun n => c n * hexChiE ^ n) :=
    hexZ_chi_div_seams_closed c lam tau ups hbdry hlamMono hυpos hυnn hτnn
      Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc
  
  have hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => c n * x ^ n) :=
    hexConnAssembly_conv c (fun n => le_trans zero_le_one (hge n)) Col HW
  
  exact hex_connective_constant c hge hsub hdiv hconv

end StatMech.Universality
