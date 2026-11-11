/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.MagnetizationFieldDeriv

/-!
# The Aizenman–Barsky–Fernández differential inequality, finite volume

Derivatives of the finite-volume magnetization and a conditional form of the
Aizenman–Barsky–Fernández inequality.

## i. Overview

On a finite graph, `∂_β ⟨σ_o⟩ = ∑_{xy ∈ E} (⟨σ_oσ_xσ_y⟩ - ⟨σ_o⟩⟨σ_xσ_y⟩) + h ∑_x Cov(σ_o, σ_x)`, the
sum of the bond-energy susceptibility and `h` times the susceptibility. This file proves that
identity, defines the two- and three-point covariances used throughout, and the GHS-type bound
`GHSThreePointSym`.

`aizenman_barsky_inequality` is conditional: assuming the GHS bound at `o` and the factorization
`∑_e ghsBoundSym = J ⟨σ_o⟩ χ` (which holds for translation-invariant models), the bond-energy
susceptibility is at most `J ⟨σ_o⟩ χ`. The GHS hypothesis is discharged by
`GHSLebowitz.ghsL_threePoint`.

## ii. Key results

- `StatMech.Ising.cov2` : the spin covariance
- `StatMech.Ising.susceptibility` : the susceptibility `χ = ∑_x Cov(σ_o, σ_x)`
- `StatMech.Ising.deriv_magnetization_beta_eq` : the `β`-derivative of the magnetization
- `StatMech.Ising.GHSThreePointSym` : the GHS inequality at a site, for all edges
- `StatMech.Ising.aizenman_barsky_inequality` : the conditional Aizenman–Barsky–Fernández bound

## iii. Table of contents

- A. Derivatives of the partition function
- B. Covariances
- C. Susceptibilities and the derivative of the magnetization
- D. The GHS-type bound

## iv. References

- M. Aizenman and D. J. Barsky, *Sharpness of the phase transition in percolation models*, Comm.
  Math. Phys. 108 (1987) 489–526
- M. Aizenman, D. J. Barsky and R. Fernández, *The phase transition in a general class of Ising-type
  models is sharp*, J. Stat. Phys. 47 (1987) 343–374
- R. B. Griffiths, C. A. Hurst and S. Sherman, *Concavity of magnetization of an Ising ferromagnet
  in a positive external field*, J. Math. Phys. 11 (1970) 790–795
-/

@[expose] public section

open scoped BigOperators symmDiff
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Derivatives of the partition function -/

/-- The negative Hamiltonian `∑_{xy ∈ E} σ_xσ_y + h ∑_x σ_x`. -/
noncomputable def negHam (h : ℝ) (s : ConfigSpace V) : ℝ :=
  (∑ e ∈ G.edgeFinset, bond s e) + h * ∑ x, spin s x

omit [DecidableEq V] in
lemma hasDerivAt_isingWeight_beta (β h : ℝ) (s : ConfigSpace V) :
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

lemma hasDerivAt_num_beta (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      (∑ s : ConfigSpace V, f s * (isingWeight G β h s * negHam G h s)) β := by
  have hpt : (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      = ∑ s : ConfigSpace V, (fun β => f s * isingWeight G β h s) := by rw [Finset.sum_fn]
  rw [hpt]
  exact HasDerivAt.sum (fun s _ => (hasDerivAt_isingWeight_beta G β h s).const_mul (f s))

lemma hasDerivAt_isingZ_beta (β h : ℝ) :
    HasDerivAt (fun β => isingZ G β h)
      (∑ s : ConfigSpace V, isingWeight G β h s * negHam G h s) β := by
  have h1 := hasDerivAt_num_beta G β h (fun _ => 1)
  simp only [one_mul] at h1
  exact h1

lemma hasDerivAt_expectation_beta (β h : ℝ) (f : ConfigSpace V → ℝ) :
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

lemma expectation_add (β h : ℝ) (f g : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => f s + g s)
      = isingExpectation G β h f + isingExpectation G β h g := by
  unfold isingExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _; ring

lemma expectation_const_mul (β h : ℝ) (c : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => c * f s) = c * isingExpectation G β h f := by
  unfold isingExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _; ring

/-! ## B. Covariances -/

/-- The spin covariance `Cov(σ_x, σ_y) = ⟨σ_xσ_y⟩ - ⟨σ_x⟩⟨σ_y⟩`. -/
noncomputable def cov2 (β h : ℝ) (x y : V) : ℝ :=
  isingExpectation G β h (fun s => spin s x * spin s y)
    - isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y)

/-- The one-point function `⟨σ_x⟩`. -/
noncomputable def onePt (β h : ℝ) (x : V) : ℝ := isingExpectation G β h (fun s => spin s x)

/-- The covariance `⟨σ_o σ_x σ_y⟩ - ⟨σ_o⟩⟨σ_x σ_y⟩` of `σ_o` with the bond variable of `e = {x,
y}`. -/
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

@[simp] lemma cov3sym_mk (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y)
      = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x * spin s y) := rfl

/-- The GHS bound `Cov(σ_o, σ_x)⟨σ_y⟩ + Cov(σ_o, σ_y)⟨σ_x⟩` for the bond `e = {x, y}`. -/
noncomputable def ghsBoundSym (β h : ℝ) (o : V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => cov2 G β h o x * onePt G β h y + cov2 G β h o y * onePt G β h x,
    fun a b => by ring⟩ e

@[simp] lemma ghsBoundSym_mk (β h : ℝ) (o x y : V) :
    ghsBoundSym G β h o s(x, y)
      = cov2 G β h o x * onePt G β h y + cov2 G β h o y * onePt G β h x := rfl

/-! ## C. Susceptibilities and the derivative of the magnetization -/

/-- The bond-energy susceptibility `∑_{e ∈ E} Cov(σ_o, σ_e)`. -/
noncomputable def bondEnergySusceptibility (β h : ℝ) (o : V) : ℝ :=
  ∑ e ∈ G.edgeFinset, cov3sym G β h o e

/-- The susceptibility `χ(o) = ∑_x Cov(σ_o, σ_x)`. -/
noncomputable def susceptibility (β h : ℝ) (o : V) : ℝ :=
  ∑ x, cov2 G β h o x

lemma expectation_negHam_cov_expand (β h : ℝ) (f : ConfigSpace V → ℝ) :
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

lemma deriv_magnetization_beta_eq (β h : ℝ) (o : V) :
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

/-! ## D. The GHS-type bound -/

/-- The GHS inequality at `o` for every edge: `cov3sym ≤ ghsBoundSym`, equivalently `u₃(o, x, y)
≤ 0` for every edge `{x, y}`. -/
def GHSThreePointSym (β h : ℝ) (o : V) : Prop :=
  ∀ e ∈ G.edgeFinset, cov3sym G β h o e ≤ ghsBoundSym G β h o e

lemma bondEnergy_le_ghsSum (β h : ℝ) (o : V) (hghs : GHSThreePointSym G β h o) :
    bondEnergySusceptibility G β h o ≤ ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e := by
  unfold bondEnergySusceptibility
  exact Finset.sum_le_sum hghs

/-- A conditional finite-volume form of the Aizenman–Barsky–Fernández inequality: if the GHS
bound holds at `o` and the GHS bounds sum to `J ⟨σ_o⟩ χ(o)`, then the bond-energy
susceptibility is at most `J ⟨σ_o⟩ χ(o)`. -/
lemma aizenman_barsky_inequality (β h : ℝ) (o : V) (J : ℝ)
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
