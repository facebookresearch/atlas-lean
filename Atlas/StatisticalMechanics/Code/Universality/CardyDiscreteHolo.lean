/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Mathlib

namespace StatMech.Universality

open Complex











noncomputable def cardyOmega : ℂ := Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I)


theorem cardyOmega_cube : cardyOmega ^ 3 = 1 := by
  unfold cardyOmega
  rw [← Complex.exp_nat_mul,
      show (3 : ℕ) * ((2 * Real.pi / 3 : ℝ) * Complex.I)
        = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact_mod_cast Complex.exp_two_pi_mul_I


theorem cardyOmega_ne_one : cardyOmega ≠ 1 := by
  unfold cardyOmega
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.exp_ofReal_mul_I_re] at hre
  simp only [Complex.one_re] at hre
  have hc : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [hc] at hre; norm_num at hre




theorem cardyOmega_sum_zero : 1 + cardyOmega + cardyOmega ^ 2 = 0 := by
  have h3 : cardyOmega ^ 3 - 1 = 0 := by rw [cardyOmega_cube]; ring
  have hfac : cardyOmega ^ 3 - 1 = (cardyOmega - 1) * (1 + cardyOmega + cardyOmega ^ 2) := by
    ring
  rw [hfac] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) cardyOmega_ne_one
  · exact h









noncomputable def cardyWpow (k : ZMod 3) : ℂ := cardyOmega ^ (k.val)

@[simp] theorem cardyWpow_zero : cardyWpow 0 = 1 := by simp [cardyWpow]

@[simp] theorem cardyWpow_one : cardyWpow 1 = cardyOmega := by
  show cardyOmega ^ (1 : ZMod 3).val = cardyOmega
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]

@[simp] theorem cardyWpow_two : cardyWpow 2 = cardyOmega ^ 2 := by
  show cardyOmega ^ (2 : ZMod 3).val = cardyOmega ^ 2
  rw [show (2 : ZMod 3).val = 2 from rfl]




theorem cardyWpow_succ (k : ZMod 3) : cardyWpow (k + 1) = cardyOmega * cardyWpow k := by
  fin_cases k
  · show cardyWpow ((0 : ZMod 3) + 1) = cardyOmega * cardyWpow (0 : ZMod 3)
    rw [show ((0 : ZMod 3) + 1) = 1 from rfl, cardyWpow_one, cardyWpow_zero]; ring
  · show cardyWpow ((1 : ZMod 3) + 1) = cardyOmega * cardyWpow (1 : ZMod 3)
    rw [show ((1 : ZMod 3) + 1) = 2 from rfl, cardyWpow_two, cardyWpow_one]; ring
  · show cardyWpow ((2 : ZMod 3) + 1) = cardyOmega * cardyWpow (2 : ZMod 3)
    rw [show ((2 : ZMod 3) + 1) = 0 from rfl, cardyWpow_zero, cardyWpow_two]
    rw [show cardyOmega * cardyOmega ^ 2 = cardyOmega ^ 3 by ring, cardyOmega_cube]


theorem cardyWpow_sum_zero : cardyWpow 0 + cardyWpow 1 + cardyWpow 2 = 0 := by
  rw [cardyWpow_zero, cardyWpow_one, cardyWpow_two]; exact cardyOmega_sum_zero






























structure CardyLocalConfig where
  
  Ω : Type
  
  [fin : Fintype Ω]
  
  rot : Ω → Ω
  
  rot_bij : Function.Bijective rot
  
  arc : Ω → ZMod 3
  
  arc_rot : ∀ ω, arc (rot ω) = arc ω + 1
  
  weight : Ω → ℂ
  
  weight_rot : ∀ ω, weight (rot ω) = weight ω

namespace CardyLocalConfig

attribute [instance] CardyLocalConfig.fin

variable (L : CardyLocalConfig)



noncomputable def crossingFun (x : ZMod 3) : ℂ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => L.arc ω = x), L.weight ω



noncomputable def cardyS : ℂ := ∑ ω, cardyWpow (L.arc ω) * L.weight ω





theorem cardyS_eq_combination :
    L.cardyS = L.crossingFun 0 + cardyOmega * L.crossingFun 1
        + cardyOmega ^ 2 * L.crossingFun 2 := by
  unfold cardyS crossingFun
  
  rw [← Finset.sum_fiberwise Finset.univ L.arc (fun ω => cardyWpow (L.arc ω) * L.weight ω)]
  
  have hfib : ∀ j : ZMod 3,
      (∑ ω ∈ Finset.univ.filter (fun ω => L.arc ω = j),
          cardyWpow (L.arc ω) * L.weight ω)
        = cardyWpow j * ∑ ω ∈ Finset.univ.filter (fun ω => L.arc ω = j), L.weight ω := by
    intro j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [hω.2]
  
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hfib 0, hfib 1, hfib 2, cardyWpow_zero, cardyWpow_one, cardyWpow_two]
  ring









theorem colorSwap_S_zero : L.cardyS = 0 := by
  
  have hself : L.cardyS = cardyOmega * L.cardyS := by
    calc L.cardyS
        = ∑ ω, cardyWpow (L.arc (L.rot ω)) * L.weight (L.rot ω) := by
          unfold cardyS
          exact (Fintype.sum_bijective L.rot L.rot_bij _ _ (fun ω => rfl)).symm
      _ = ∑ ω, cardyOmega * (cardyWpow (L.arc ω) * L.weight ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [L.arc_rot, L.weight_rot, cardyWpow_succ]; ring
      _ = cardyOmega * L.cardyS := by rw [cardyS, Finset.mul_sum]
  have hfac : (1 - cardyOmega) * L.cardyS = 0 := by
    rw [sub_mul, one_mul, ← hself, sub_self]
  have h1w : (1 : ℂ) - cardyOmega ≠ 0 :=
    sub_ne_zero.mpr (fun h => cardyOmega_ne_one h.symm)
  exact (mul_eq_zero.mp hfac).resolve_left h1w




theorem crossingCombination_zero :
    L.crossingFun 0 + cardyOmega * L.crossingFun 1
        + cardyOmega ^ 2 * L.crossingFun 2 = 0 := by
  rw [← cardyS_eq_combination]; exact L.colorSwap_S_zero

end CardyLocalConfig














noncomputable def triContour (F : ℂ → ℂ) (z : Fin 3 → ℂ) : ℂ :=
  ∑ i : Fin 3, F ((z i + z (i + 1)) / 2) * (z (i + 1) - z i)



theorem triContour_expand (F : ℂ → ℂ) (z : Fin 3 → ℂ) :
    triContour F z =
      F ((z 0 + z 1) / 2) * (z 1 - z 0)
      + F ((z 1 + z 2) / 2) * (z 2 - z 1)
      + F ((z 2 + z 0) / 2) * (z 0 - z 2) := by
  unfold triContour
  rw [Fin.sum_univ_three]
  rw [show ((0 : Fin 3) + 1) = 1 from rfl, show ((1 : Fin 3) + 1) = 2 from rfl,
      show ((2 : Fin 3) + 1) = 0 from rfl]





noncomputable def triFace (v d : ℂ) : Fin 3 → ℂ := ![v + d, v + cardyOmega * d, v + cardyOmega ^ 2 * d]










theorem triContour_eq_cardyS (F : ℂ → ℂ) (v d : ℂ) :
    triContour F (triFace v d)
      = (cardyOmega - 1) * d * ( F ((triFace v d 0 + triFace v d 1) / 2)
          + cardyOmega * F ((triFace v d 1 + triFace v d 2) / 2)
          + cardyOmega ^ 2 * F ((triFace v d 2 + triFace v d 0) / 2) ) := by
  rw [triContour_expand]
  have e1 : triFace v d 1 - triFace v d 0 = (cardyOmega - 1) * d := by
    show (v + cardyOmega * d) - (v + d) = (cardyOmega - 1) * d; ring
  have e2 : triFace v d 2 - triFace v d 1 = cardyOmega * (cardyOmega - 1) * d := by
    show (v + cardyOmega ^ 2 * d) - (v + cardyOmega * d) = cardyOmega * (cardyOmega - 1) * d; ring
  have e3 : triFace v d 0 - triFace v d 2 = cardyOmega ^ 2 * (cardyOmega - 1) * d := by
    show (v + d) - (v + cardyOmega ^ 2 * d) = cardyOmega ^ 2 * (cardyOmega - 1) * d
    rw [show cardyOmega ^ 2 * (cardyOmega - 1) * d = (cardyOmega ^ 3 - cardyOmega ^ 2) * d by ring,
        cardyOmega_cube]; ring
  rw [e1, e2, e3]; ring













noncomputable def cardyObservable (L : CardyLocalConfig) (v d : ℂ) : ℂ → ℂ := fun z =>
  if z = (triFace v d 0 + triFace v d 1) / 2 then L.crossingFun 0
  else if z = (triFace v d 1 + triFace v d 2) / 2 then L.crossingFun 1
  else if z = (triFace v d 2 + triFace v d 0) / 2 then L.crossingFun 2
  else 0



















theorem cardyDiscrete_CR (L : CardyLocalConfig) (v d : ℂ)
    (hpq : (triFace v d 0 + triFace v d 1) / 2 ≠ (triFace v d 1 + triFace v d 2) / 2)
    (hpr : (triFace v d 0 + triFace v d 1) / 2 ≠ (triFace v d 2 + triFace v d 0) / 2)
    (hqr : (triFace v d 1 + triFace v d 2) / 2 ≠ (triFace v d 2 + triFace v d 0) / 2) :
    triContour (cardyObservable L v d) (triFace v d) = 0 := by
  rw [triContour_eq_cardyS]
  
  have h0 : cardyObservable L v d ((triFace v d 0 + triFace v d 1) / 2) = L.crossingFun 0 := by
    unfold cardyObservable; rw [if_pos rfl]
  have h1 : cardyObservable L v d ((triFace v d 1 + triFace v d 2) / 2) = L.crossingFun 1 := by
    unfold cardyObservable
    rw [if_neg hpq.symm, if_pos rfl]
  have h2 : cardyObservable L v d ((triFace v d 2 + triFace v d 0) / 2) = L.crossingFun 2 := by
    unfold cardyObservable
    rw [if_neg hpr.symm, if_neg hqr.symm, if_pos rfl]
  rw [h0, h1, h2, L.crossingCombination_zero, mul_zero]














theorem cardyDiscrete_CR_closedPath (L : CardyLocalConfig)
    {ι : Type*} (faces : Finset ι) (tri : ι → ℂ × ℂ)
    (hdist : ∀ i ∈ faces,
      (triFace (tri i).1 (tri i).2 0 + triFace (tri i).1 (tri i).2 1) / 2
          ≠ (triFace (tri i).1 (tri i).2 1 + triFace (tri i).1 (tri i).2 2) / 2 ∧
      (triFace (tri i).1 (tri i).2 0 + triFace (tri i).1 (tri i).2 1) / 2
          ≠ (triFace (tri i).1 (tri i).2 2 + triFace (tri i).1 (tri i).2 0) / 2 ∧
      (triFace (tri i).1 (tri i).2 1 + triFace (tri i).1 (tri i).2 2) / 2
          ≠ (triFace (tri i).1 (tri i).2 2 + triFace (tri i).1 (tri i).2 0) / 2) :
    ∑ i ∈ faces,
      triContour (cardyObservable L (tri i).1 (tri i).2) (triFace (tri i).1 (tri i).2) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨hpq, hpr, hqr⟩ := hdist i hi
  exact cardyDiscrete_CR L (tri i).1 (tri i).2 hpq hpr hqr

end StatMech.Universality
