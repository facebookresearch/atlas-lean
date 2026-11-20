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

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]









noncomputable def negHam (h : ℝ) (s : ConfigSpace V) : ℝ :=
  (∑ e ∈ G.edgeFinset, bond s e) + h * ∑ x, spin s x



theorem hasDerivAt_isingWeight_beta (β h : ℝ) (s : ConfigSpace V) :
    HasDerivAt (fun β => isingWeight G β h s)
      (isingWeight G β h s * negHam G h s) β := by
  unfold isingWeight hamiltonian negHam
  set E := ∑ e ∈ G.edgeFinset, bond s e with hE
  set M := ∑ x, spin s x with hM
  have hrw : (fun β => Real.exp (-β * (-E - h * M)))
      = (fun β => Real.exp (β * (E + h * M))) := by funext β; congr 1; ring
  rw [hrw]
  have hlin : HasDerivAt (fun β : ℝ => β * (E + h * M)) (E + h * M) β := by
    simpa using (hasDerivAt_id β).mul_const (E + h * M)
  have hcomp := (Real.hasDerivAt_exp (β * (E + h * M))).comp β hlin
  have hval : Real.exp (-β * (-E - h * M)) = Real.exp (β * (E + h * M)) := by
    congr 1; ring
  rw [hval]; exact hcomp



theorem hasDerivAt_num_beta (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      (∑ s : ConfigSpace V, f s * (isingWeight G β h s * negHam G h s)) β := by
  have hpt : (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      = ∑ s : ConfigSpace V, (fun β => f s * isingWeight G β h s) := by rw [Finset.sum_fn]
  rw [hpt]
  exact HasDerivAt.sum (fun s _ => (hasDerivAt_isingWeight_beta G β h s).const_mul (f s))



theorem hasDerivAt_isingZ_beta (β h : ℝ) :
    HasDerivAt (fun β => isingZ G β h)
      (∑ s : ConfigSpace V, isingWeight G β h s * negHam G h s) β := by
  have h1 := hasDerivAt_num_beta G β h (fun _ => 1)
  simp only [one_mul] at h1
  exact h1







theorem hasDerivAt_expectation_beta (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun β => isingExpectation G β h f)
      (isingExpectation G β h (fun s => f s * negHam G h s)
            - isingExpectation G β h f * isingExpectation G β h (negHam G h)) β := by
  have hN := hasDerivAt_num_beta G β h f
  have hZ := hasDerivAt_isingZ_beta G β h
  have hZne : isingZ G β h ≠ 0 := isingZ_ne_zero G β h
  have hfun : (fun β => isingExpectation G β h f)
      = (fun β => (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h) := by
    funext β; exact expectation_eq_div G β h f
  rw [hfun]
  have hdiv := hN.div hZ hZne
  have e1 : isingExpectation G β h (fun s => f s * negHam G h s)
      = (∑ s : ConfigSpace V, (f s * negHam G h s) * isingWeight G β h s) / isingZ G β h :=
    expectation_eq_div G β h _
  have e2 : isingExpectation G β h f
      = (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h :=
    expectation_eq_div G β h f
  have e3 : isingExpectation G β h (negHam G h)
      = (∑ s : ConfigSpace V, negHam G h s * isingWeight G β h s) / isingZ G β h :=
    expectation_eq_div G β h (negHam G h)
  set Z := isingZ G β h with hZdef
  set A := ∑ s : ConfigSpace V, (f s * negHam G h s) * isingWeight G β h s with hAdef
  set B := ∑ s : ConfigSpace V, f s * isingWeight G β h s with hBdef
  set C := ∑ s : ConfigSpace V, negHam G h s * isingWeight G β h s with hCdef
  have hN'eq :
      (∑ s : ConfigSpace V, f s * (isingWeight G β h s * negHam G h s)) = A := by
    rw [hAdef]; apply Finset.sum_congr rfl; intro s _; ring
  have hZ'eq :
      (∑ s : ConfigSpace V, isingWeight G β h s * negHam G h s) = C := by
    rw [hCdef]; apply Finset.sum_congr rfl; intro s _; ring
  rw [e1, e2, e3]
  have hval : (A / Z - B / Z * (C / Z))
      = ((∑ s : ConfigSpace V, f s * (isingWeight G β h s * negHam G h s)) * Z
          - B * (∑ s : ConfigSpace V, isingWeight G β h s * negHam G h s)) / Z ^ 2 := by
    rw [hN'eq, hZ'eq]; field_simp
  rw [hval]
  exact hdiv




theorem expectation_add (β h : ℝ) (f g : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => f s + g s)
      = isingExpectation G β h f + isingExpectation G β h g := by
  unfold isingExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _; ring


theorem expectation_const_mul (β h : ℝ) (c : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => c * f s) = c * isingExpectation G β h f := by
  unfold isingExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _; ring





noncomputable def cov2 (β h : ℝ) (x y : V) : ℝ :=
  isingExpectation G β h (fun s => spin s x * spin s y)
    - isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y)


noncomputable def onePt (β h : ℝ) (x : V) : ℝ := isingExpectation G β h (fun s => spin s x)




noncomputable def cov3sym (β h : ℝ) (o : V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y =>
    isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
      - isingExpectation G β h (fun s => spin s o)
          * isingExpectation G β h (fun s => spin s x * spin s y), by
    intro a b
    have h1 : (fun s : ConfigSpace V => spin s o * (spin s a * spin s b))
        = (fun s => spin s o * (spin s b * spin s a)) := by funext s; ring
    have h2 : (fun s : ConfigSpace V => spin s a * spin s b)
        = (fun s => spin s b * spin s a) := by funext s; ring
    simp only []; rw [h1, h2]⟩ e

@[simp] theorem cov3sym_mk (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y)
      = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x * spin s y) := rfl




noncomputable def ghsBoundSym (β h : ℝ) (o : V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => cov2 G β h o x * onePt G β h y + cov2 G β h o y * onePt G β h x,
    fun a b => by ring⟩ e

@[simp] theorem ghsBoundSym_mk (β h : ℝ) (o x y : V) :
    ghsBoundSym G β h o s(x, y)
      = cov2 G β h o x * onePt G β h y + cov2 G β h o y * onePt G β h x := rfl







noncomputable def bondEnergySusceptibility (β h : ℝ) (o : V) : ℝ :=
  ∑ e ∈ G.edgeFinset, cov3sym G β h o e


noncomputable def susceptibility (β h : ℝ) (o : V) : ℝ :=
  ∑ x, cov2 G β h o x











theorem expectation_negHam_cov_expand (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => f s * negHam G h s)
        - isingExpectation G β h f * isingExpectation G β h (negHam G h)
      = (∑ e ∈ G.edgeFinset,
          (isingExpectation G β h (fun s => f s * bond s e)
            - isingExpectation G β h f * isingExpectation G β h (fun s => bond s e)))
        + h * ∑ x,
          (isingExpectation G β h (fun s => f s * spin s x)
            - isingExpectation G β h f * isingExpectation G β h (fun s => spin s x)) := by
  
  have hnum : isingExpectation G β h (fun s => f s * negHam G h s)
      = (∑ e ∈ G.edgeFinset, isingExpectation G β h (fun s => f s * bond s e))
        + h * ∑ x, isingExpectation G β h (fun s => f s * spin s x) := by
    have step1 : (fun s => f s * negHam G h s)
        = (fun s => (fun s => f s * ∑ e ∈ G.edgeFinset, bond s e) s
              + (fun s => h * (f s * ∑ x, spin s x)) s) := by
      funext s; unfold negHam; ring
    rw [step1, expectation_add]
    congr 1
    · have hbr : (fun s => f s * ∑ e ∈ G.edgeFinset, bond s e)
          = (fun cfg => ∑ e ∈ G.edgeFinset, (fun e s => f s * bond s e) e cfg) := by
        funext s; rw [Finset.mul_sum]
      rw [hbr, expectation_sum]
    · rw [expectation_const_mul]
      congr 1
      have hsp : (fun s => f s * ∑ x, spin s x)
          = (fun cfg => ∑ x, (fun x s => f s * spin s x) x cfg) := by
        funext s; rw [Finset.mul_sum]
      rw [hsp, expectation_sum]
  
  have hZ : isingExpectation G β h (negHam G h)
      = (∑ e ∈ G.edgeFinset, isingExpectation G β h (fun s => bond s e))
        + h * ∑ x, isingExpectation G β h (fun s => spin s x) := by
    have step1 : (negHam G h)
        = (fun s => (fun s => ∑ e ∈ G.edgeFinset, bond s e) s
              + (fun s => h * (∑ x, spin s x)) s) := by
      funext s; unfold negHam; ring
    rw [step1, expectation_add]
    congr 1
    · have hbr : (fun s : ConfigSpace V => ∑ e ∈ G.edgeFinset, bond s e)
          = (fun cfg => ∑ e ∈ G.edgeFinset, (fun e s => bond s e) e cfg) := rfl
      rw [hbr, expectation_sum]
    · rw [expectation_const_mul]
      congr 1
      have hsp : (fun s : ConfigSpace V => ∑ x, spin s x)
          = (fun cfg => ∑ x, (fun x s => spin s x) x cfg) := rfl
      rw [hsp, expectation_sum]
  rw [hnum, hZ]
  
  set X := isingExpectation G β h f with hX
  
  have hbond : (∑ e ∈ G.edgeFinset,
        ((isingExpectation G β h fun s => f s * bond s e)
          - X * isingExpectation G β h fun s => bond s e))
      = (∑ e ∈ G.edgeFinset, isingExpectation G β h fun s => f s * bond s e)
        - X * ∑ e ∈ G.edgeFinset, isingExpectation G β h fun s => bond s e := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  
  have hfield : (∑ x, ((isingExpectation G β h fun s => f s * spin s x)
          - X * isingExpectation G β h fun s => spin s x))
      = (∑ x, isingExpectation G β h fun s => f s * spin s x)
        - X * ∑ x, isingExpectation G β h fun s => spin s x := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hbond, hfield]
  ring









theorem deriv_magnetization_beta_eq (β h : ℝ) (o : V) :
    deriv (fun β => isingExpectation G β h (fun s => spin s o)) β
      = bondEnergySusceptibility G β h o + h * susceptibility G β h o := by
  rw [(hasDerivAt_expectation_beta G β h (fun s => spin s o)).deriv]
  rw [expectation_negHam_cov_expand]
  unfold bondEnergySusceptibility susceptibility cov2
  congr 1
  
  apply Finset.sum_congr rfl
  intro e _
  induction e with
  | h x y =>
    rw [cov3sym_mk]; rfl













def GHSThreePointSym (β h : ℝ) (o : V) : Prop :=
  ∀ e ∈ G.edgeFinset, cov3sym G β h o e ≤ ghsBoundSym G β h o e







theorem bondEnergy_le_ghsSum (β h : ℝ) (o : V) (hghs : GHSThreePointSym G β h o) :
    bondEnergySusceptibility G β h o ≤ ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e := by
  unfold bondEnergySusceptibility
  exact Finset.sum_le_sum hghs




























theorem aizenman_barsky_inequality (β h : ℝ) (o : V) (J : ℝ)
    (hghs : GHSThreePointSym G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
  calc bondEnergySusceptibility G β h o
      ≤ ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e := bondEnergy_le_ghsSum G β h o hghs
    _ = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := hfactor

end Ising

end StatMech
