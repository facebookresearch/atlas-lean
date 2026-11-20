/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace StatMech

namespace Sharpness

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]





noncomputable def totalSpin (s : ConfigSpace V) : ℝ := ∑ x, spin s x





theorem hasDerivAt_isingWeight (β h : ℝ) (s : ConfigSpace V) :
    HasDerivAt (fun h => isingWeight G β h s)
      (isingWeight G β h s * (β * ∑ x, spin s x)) h := by
  unfold isingWeight hamiltonian
  set E := ∑ e ∈ G.edgeFinset, bond s e with hE
  set M := ∑ x, spin s x with hM
  have hrw : (fun h => Real.exp (-β * (-E - h * M)))
      = (fun h => Real.exp ((β * E) + h * (β * M))) := by funext h; congr 1; ring
  rw [hrw]
  have hlin : HasDerivAt (fun h : ℝ => h * (β * M)) (β * M) h := by
    simpa using (hasDerivAt_id h).mul_const (β * M)
  have hd : HasDerivAt (fun h : ℝ => (β * E) + h * (β * M)) (β * M) h := by
    simpa using hlin.const_add (β * E)
  have hcomp := (Real.hasDerivAt_exp ((β * E) + h * (β * M))).comp h hd
  have hval : Real.exp (-β * (-E - h * M)) = Real.exp ((β * E) + h * (β * M)) := by
    congr 1; ring
  rw [hval]; exact hcomp



theorem hasDerivAt_num (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun h => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      (∑ s : ConfigSpace V, f s * (isingWeight G β h s * (β * ∑ x, spin s x))) h := by
  have hpt : (fun h => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      = ∑ s : ConfigSpace V, (fun h => f s * isingWeight G β h s) := by rw [Finset.sum_fn]
  rw [hpt]
  exact HasDerivAt.sum (fun s _ => (hasDerivAt_isingWeight G β h s).const_mul (f s))



theorem hasDerivAt_isingZ (β h : ℝ) :
    HasDerivAt (fun h => isingZ G β h)
      (∑ s : ConfigSpace V, isingWeight G β h s * (β * ∑ x, spin s x)) h := by
  have h1 := hasDerivAt_num G β h (fun _ => 1)
  simp only [one_mul] at h1
  exact h1




theorem expectation_eq_div (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h f
      = (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h := by
  unfold isingExpectation isingProb
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  rw [div_mul_eq_mul_div, mul_comm]









theorem hasDerivAt_expectation (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun h => isingExpectation G β h f)
      (β * (isingExpectation G β h (fun s => f s * totalSpin s)
            - isingExpectation G β h f * isingExpectation G β h totalSpin)) h := by
  have hN := hasDerivAt_num G β h f
  have hZ : HasDerivAt (fun h => isingZ G β h)
      (∑ s : ConfigSpace V, isingWeight G β h s * (β * ∑ x, spin s x)) h :=
    hasDerivAt_isingZ G β h
  have hZne : isingZ G β h ≠ 0 := isingZ_ne_zero G β h
  have hfun : (fun h => isingExpectation G β h f)
      = (fun h => (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h) := by
    funext h; exact expectation_eq_div G β h f
  rw [hfun]
  have hdiv := hN.div hZ hZne
  have e1 : isingExpectation G β h (fun s => f s * totalSpin s)
      = (∑ s : ConfigSpace V, (f s * totalSpin s) * isingWeight G β h s) / isingZ G β h :=
    expectation_eq_div G β h _
  have e2 : isingExpectation G β h f
      = (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h :=
    expectation_eq_div G β h f
  have e3 : isingExpectation G β h totalSpin
      = (∑ s : ConfigSpace V, totalSpin s * isingWeight G β h s) / isingZ G β h :=
    expectation_eq_div G β h totalSpin
  set Z := isingZ G β h with hZdef
  set A := ∑ s : ConfigSpace V, (f s * totalSpin s) * isingWeight G β h s with hAdef
  set B := ∑ s : ConfigSpace V, f s * isingWeight G β h s with hBdef
  set C := ∑ s : ConfigSpace V, totalSpin s * isingWeight G β h s with hCdef
  have hN'eq :
      (∑ s : ConfigSpace V, f s * (isingWeight G β h s * (β * ∑ x, spin s x))) = β * A := by
    rw [hAdef, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; unfold totalSpin; ring
  have hZ'eq :
      (∑ s : ConfigSpace V, isingWeight G β h s * (β * ∑ x, spin s x)) = β * C := by
    rw [hCdef, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; unfold totalSpin; ring
  rw [e1, e2, e3]
  have hval : β * (A / Z - B / Z * (C / Z))
      = ((∑ s : ConfigSpace V, f s * (isingWeight G β h s * (β * ∑ x, spin s x))) * Z
          - B * (∑ s : ConfigSpace V, isingWeight G β h s * (β * ∑ x, spin s x))) / Z ^ 2 := by
    rw [hN'eq, hZ'eq]
    field_simp
  rw [hval]
  exact hdiv




theorem expectation_sum (β h : ℝ) {ι : Type*} (s : Finset ι) (f : ι → ConfigSpace V → ℝ) :
    isingExpectation G β h (fun cfg => ∑ i ∈ s, f i cfg)
      = ∑ i ∈ s, isingExpectation G β h (f i) := by
  unfold isingExpectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]



theorem expectation_totalSpin (β h : ℝ) :
    isingExpectation G β h totalSpin
      = ∑ x, isingExpectation G β h (fun s => spin s x) := by
  have : (totalSpin : ConfigSpace V → ℝ) = (fun cfg => ∑ x, (fun y s => spin s y) x cfg) := by
    funext cfg; rfl
  rw [this, expectation_sum]


theorem expectation_mul_totalSpin (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => f s * totalSpin s)
      = ∑ x, isingExpectation G β h (fun s => f s * spin s x) := by
  have hrw : (fun s => f s * totalSpin s)
      = (fun cfg => ∑ x, (fun y s => f s * spin s y) x cfg) := by
    funext s; unfold totalSpin; rw [Finset.mul_sum]
  rw [hrw, expectation_sum]




theorem spinProd_singleton (x : V) :
    spinProd ({x} : Finset V) = (fun s => spin s x) := by
  funext s; rw [spinProd]; simp


theorem spinProd_pair (x y : V) (hxy : x ≠ y) :
    spinProd ({x, y} : Finset V) = (fun s => spin s x * spin s y) := by
  funext s; rw [spinProd, Finset.prod_pair hxy]


theorem symmDiff_singleton_pair (x y : V) (hxy : x ≠ y) :
    symmDiff ({x} : Finset V) {y} = {x, y} := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> tauto
  · rintro (h1 | h1)
    · left; exact ⟨h1, by rw [h1]; exact hxy⟩
    · right; exact ⟨h1, by rw [h1]; exact hxy.symm⟩




theorem expectation_spin_le_one (β h : ℝ) (x : V) :
    isingExpectation G β h (fun s => spin s x) ≤ 1 := by
  unfold isingExpectation
  calc ∑ s : ConfigSpace V, isingProb G β h s * spin s x
      ≤ ∑ s : ConfigSpace V, isingProb G β h s * 1 := by
        apply Finset.sum_le_sum
        intro s _
        refine mul_le_mul_of_nonneg_left ?_ (isingProb_nonneg G β h s)
        rcases spin_eq_pm s x with hp | hp
        · rw [hp]
        · rw [hp]; norm_num
    _ = 1 := by simp [isingProb_sum_eq_one G β h]


theorem expectation_spin_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x : V) :
    0 ≤ isingExpectation G β h (fun s => spin s x) := by
  have hg := gks_first G β h hβ hh {x}
  rwa [spinProd_singleton] at hg


theorem expectation_spin_bounds (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x : V) :
    0 ≤ isingExpectation G β h (fun s => spin s x)
      ∧ isingExpectation G β h (fun s => spin s x) ≤ 1 :=
  ⟨expectation_spin_nonneg G β h hβ hh x, expectation_spin_le_one G β h x⟩







theorem cov_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x y : V) (hxy : x ≠ y) :
    isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y)
      ≤ isingExpectation G β h (fun s => spin s x * spin s y) := by
  have h2 := gks_second G β h hβ hh {x} {y}
  rw [spinProd_singleton, spinProd_singleton, symmDiff_singleton_pair x y hxy,
    spinProd_pair x y hxy] at h2
  exact h2










theorem hasDerivAt_magnetization (β h : ℝ) (o : V) :
    HasDerivAt (fun h => isingExpectation G β h (fun s => spin s o))
      (β * (isingExpectation G β h (fun s => spin s o * totalSpin s)
            - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpin))
      h :=
  hasDerivAt_expectation G β h (fun s => spin s o)



theorem deriv_magnetization_eq_sum_cov (β h : ℝ) (o : V) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) h
      = β * ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x)
            - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x)) := by
  rw [(hasDerivAt_magnetization G β h o).deriv]
  rw [expectation_mul_totalSpin, expectation_totalSpin, Finset.mul_sum, Finset.sum_sub_distrib]




theorem deriv_magnetization_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ deriv (fun h => isingExpectation G β h (fun s => spin s o)) h := by
  rw [deriv_magnetization_eq_sum_cov]
  refine mul_nonneg hβ (Finset.sum_nonneg (fun x _ => ?_))
  by_cases hxo : x = o
  · subst hxo
    
    have hsq : (fun s => spin s x * spin s x) = (fun _ : ConfigSpace V => (1 : ℝ)) := by
      funext s; exact spin_sq s x
    rw [hsq]
    have hone : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
      unfold isingExpectation
      simp [isingProb_sum_eq_one G β h]
    rw [hone]
    have hb := expectation_spin_bounds G β h hβ hh x
    nlinarith [hb.1, hb.2]
  · have := cov_nonneg G β h hβ hh o x (Ne.symm hxo)
    linarith




def flipCfg (s : ConfigSpace V) : ConfigSpace V := fun x => ! s x


theorem spin_flipCfg (s : ConfigSpace V) (x : V) : spin (flipCfg s) x = - spin s x := by
  unfold flipCfg spin; cases h : s x <;> simp [h]


theorem bond_flipCfg (s : ConfigSpace V) (e : Sym2 V) : bond (flipCfg s) e = bond s e := by
  induction e with
  | h a b =>
    rw [bond_mk, bond_mk]; unfold flipCfg spin
    cases ha : s a <;> cases hb : s b <;> simp [ha, hb]


def flipEquiv : ConfigSpace V ≃ ConfigSpace V where
  toFun := flipCfg
  invFun := flipCfg
  left_inv := by intro s; funext x; unfold flipCfg; cases s x <;> rfl
  right_inv := by intro s; funext x; unfold flipCfg; cases s x <;> rfl




theorem magnetization_zero_field (β : ℝ) (o : V) :
    isingExpectation G β 0 (fun s => spin s o) = 0 := by
  unfold isingExpectation
  have key : ∀ s, isingProb G β 0 (flipCfg s) * spin (flipCfg s) o
      = - (isingProb G β 0 s * spin s o) := by
    intro s
    have hsp : spin (flipCfg s) o = - spin s o := spin_flipCfg s o
    have hprob : isingProb G β 0 (flipCfg s) = isingProb G β 0 s := by
      unfold isingProb isingWeight hamiltonian
      congr 2
      simp only [zero_mul, sub_zero]
      congr 2
      exact Finset.sum_congr rfl (fun e _ => bond_flipCfg s e)
    rw [hsp, hprob]; ring
  have hS : (∑ s : ConfigSpace V, isingProb G β 0 s * spin s o)
      = ∑ s : ConfigSpace V, isingProb G β 0 (flipCfg s) * spin (flipCfg s) o :=
    (Equiv.sum_comp (flipEquiv (V := V)) (fun s => isingProb G β 0 s * spin s o)).symm
  rw [Finset.sum_congr rfl (fun s _ => key s), Finset.sum_neg_distrib] at hS
  linarith












theorem ghs_susceptibility_bound (β h : ℝ) (hh : 0 < h) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) h
        ≤ isingExpectation G β h (fun s => spin s o) / h
      ∧ deriv (fun h => isingExpectation G β h (fun s => spin s o)) h ≤ 1 / h := by
  set φ : ℝ → ℝ := fun h => isingExpectation G β h (fun s => spin s o) with hφ
  have hdiff : DifferentiableAt ℝ φ h := (hasDerivAt_magnetization G β h o).differentiableAt
  have hphi0 : φ 0 = 0 := magnetization_zero_field G β o
  
  have hslope := hconc.deriv_le_slope (x := 0) (y := h)
    (mem_Ici.mpr le_rfl) (mem_Ici.mpr hh.le) hh hdiff
  rw [slope_def_field, hphi0, sub_zero, sub_zero] at hslope
  refine ⟨hslope, ?_⟩
  
  have hle1 : φ h ≤ 1 := expectation_spin_le_one G β h o
  have hdivle : φ h / h ≤ 1 / h := (div_le_div_iff_of_pos_right hh).mpr hle1
  exact hslope.trans hdivle

end Sharpness

end StatMech
