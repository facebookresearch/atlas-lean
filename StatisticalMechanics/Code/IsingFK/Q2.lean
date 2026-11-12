/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Mathlib
import Code.FK.Potts
import Code.Ising.Gibbs
import Code.Foundations.ConfigSpace

open scoped BigOperators

namespace StatMech

namespace IsingFK

open Potts Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]







noncomputable def toIsing (σ : V → Fin 2) : ConfigSpace V := fun x => finTwoEquiv (σ x)

omit [Fintype V] [DecidableEq V] in


theorem toIsing_bijective : Function.Bijective (toIsing (V := V)) := by
  unfold toIsing
  refine ⟨fun a b hab => ?_, fun s => ⟨fun x => finTwoEquiv.symm (s x), ?_⟩⟩
  · funext x; exact finTwoEquiv.injective (congrFun hab x)
  · funext x; simp

omit [Fintype V] [DecidableEq V] in


theorem sigma_eq_iff (σ : V → Fin 2) (x y : V) :
    (σ x = σ y) ↔ (toIsing σ x = toIsing σ y) := by
  unfold toIsing
  exact ⟨fun h => by rw [h], fun h => finTwoEquiv.injective h⟩



omit [Fintype V] [DecidableEq V] in


theorem bond_eq_two_mul_ite (s : ConfigSpace V) (x y : V) :
    bond s s(x, y) = 2 * (if s x = s y then (1 : ℝ) else 0) - 1 := by
  rw [bond_mk]; unfold spin
  by_cases hx : s x = true <;> by_cases hy : s y = true <;> simp [hx, hy] <;> norm_num

omit [Fintype V] [DecidableEq V] in


theorem monoIndicator_toIsing (σ : V → Fin 2) (e : Sym2 V) :
    monoIndicator σ e = bond (toIsing σ) e / 2 + 1 / 2 := by
  induction e with
  | _ x y =>
    rw [monoIndicator_mk, bond_eq_two_mul_ite]
    by_cases hx : σ x = σ y
    · rw [if_pos hx, if_pos ((sigma_eq_iff σ x y).mp hx)]; norm_num
    · rw [if_neg hx, if_neg (fun h => hx ((sigma_eq_iff σ x y).mpr h))]; norm_num

omit [DecidableEq V] in


theorem agreement_eq_bondSum (σ : V → Fin 2) :
    agreement G σ
      = (∑ e ∈ G.edgeFinset, bond (toIsing σ) e) / 2 + (G.edgeFinset.card : ℝ) / 2 := by
  unfold agreement
  rw [Finset.sum_congr rfl (fun e _ => monoIndicator_toIsing σ e),
    Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
  ring



omit [DecidableEq V] in




theorem isingWeight_toIsing (βI βP J : ℝ) (h : βP * J = 2 * βI) (σ : V → Fin 2) :
    isingWeight G βI 0 (toIsing σ)
      = Real.exp (-βI * G.edgeFinset.card) * pottsWeight G βP J σ := by
  unfold isingWeight pottsWeight hamiltonian
  rw [agreement_eq_bondSum G σ, ← Real.exp_add]
  congr 1
  simp only [zero_mul, sub_zero]
  rw [h]; ring




theorem isingZ_eq (βI βP J : ℝ) (h : βP * J = 2 * βI) :
    isingZ G βI 0 = Real.exp (-βI * G.edgeFinset.card) * pottsZ G 2 βP J := by
  unfold isingZ pottsZ
  rw [← (Equiv.ofBijective _ toIsing_bijective).sum_comp (isingWeight G βI 0),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Equiv.ofBijective_apply]
  exact isingWeight_toIsing G βI βP J h σ






theorem isingProb_eq_pottsProb (βI βP J : ℝ) (h : βP * J = 2 * βI) (σ : V → Fin 2) :
    isingProb G βI 0 (toIsing σ) = pottsProb G 2 βP J σ := by
  unfold isingProb pottsProb
  rw [isingWeight_toIsing G βI βP J h σ, isingZ_eq G βI βP J h,
    mul_div_mul_left _ _ (Real.exp_pos _).ne']




theorem isingProb_eq_pottsProb' (βI βP J : ℝ) (h : βP * J = 2 * βI) (s : ConfigSpace V) :
    isingProb G βI 0 s
      = pottsProb G 2 βP J ((Equiv.ofBijective _ toIsing_bijective).symm s) := by
  have := isingProb_eq_pottsProb G βI βP J h
    ((Equiv.ofBijective _ toIsing_bijective).symm s)
  rwa [show toIsing ((Equiv.ofBijective _ toIsing_bijective).symm s) = s from
    (Equiv.ofBijective _ toIsing_bijective).apply_symm_apply s] at this






noncomputable def betaOfP (p : ℝ) : ℝ := -(1 / 2) * Real.log (1 - p)


noncomputable def pOfBeta (β : ℝ) : ℝ := 1 - Real.exp (-2 * β)


theorem pOfBeta_strictMonoOn : StrictMonoOn pOfBeta (Set.Ici (0 : ℝ)) := by
  intro a _ b _ hab
  unfold pOfBeta
  have : Real.exp (-2 * b) < Real.exp (-2 * a) := Real.exp_lt_exp.mpr (by linarith)
  linarith


theorem pOfBeta_mem_Ico (β : ℝ) (hβ : 0 ≤ β) : pOfBeta β ∈ Set.Ico (0 : ℝ) 1 := by
  unfold pOfBeta
  refine ⟨?_, ?_⟩
  · have : Real.exp (-2 * β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  · have : 0 < Real.exp (-2 * β) := Real.exp_pos _
    linarith


theorem betaOfP_pOfBeta (β : ℝ) : betaOfP (pOfBeta β) = β := by
  unfold betaOfP pOfBeta
  rw [sub_sub_cancel, Real.log_exp]; ring



theorem pOfBeta_betaOfP (p : ℝ) (hp : p < 1) : pOfBeta (betaOfP p) = p := by
  unfold pOfBeta betaOfP
  have h1 : (0 : ℝ) < 1 - p := by linarith
  rw [show -2 * (-(1 / 2) * Real.log (1 - p)) = Real.log (1 - p) by ring, Real.exp_log h1]
  ring





theorem pOfBeta_bijOn : Set.BijOn pOfBeta (Set.Ici (0 : ℝ)) (Set.Ico (0 : ℝ) 1) := by
  refine ⟨fun β hβ => pOfBeta_mem_Ico β hβ, pOfBeta_strictMonoOn.injOn, ?_⟩
  intro p hp
  refine ⟨betaOfP p, ?_, pOfBeta_betaOfP p hp.2⟩
  
  have h1 : (0 : ℝ) < 1 - p := by have := hp.2; linarith
  have h2 : 1 - p ≤ 1 := by have := hp.1; linarith
  have : Real.log (1 - p) ≤ 0 := Real.log_nonpos h1.le h2
  simp only [Set.mem_Ici, betaOfP]
  linarith

end IsingFK

end StatMech
