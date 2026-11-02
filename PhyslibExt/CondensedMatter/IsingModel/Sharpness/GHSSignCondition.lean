/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.CurrentRep
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.UrsellGap

/-!
# GHS sign condition and the Lebowitz four-point form

The sign condition `GHSSignDominance` on the third Ursell function, its consequences for the GHS
three-point bound and the Aizenman–Barsky inequality, and the random-current form of `u₃` at zero
field.

## i. Overview

`GHSSignDominance G β h o` asserts `u₃(o, x, y) ≤ 0` for all pairwise distinct `o, x, y`. Together
with the degenerate cases (`o = x`, `o = y`, `x = y`), which hold unconditionally for `β, h ≥ 0`, it
gives `u₃ ≤ 0` everywhere and hence the edge-symmetrized GHS bound `GHSThreePointSym` and the
Aizenman–Barsky inequality.

The Ursell function differs from Lebowitz's four-point combination `gc_lebowitzU4` by
`2⟨σ_o⟩⟨σ_x⟩⟨σ_y⟩ ≥ 0`. At zero field `u₃` is a combination of random-current ratios.

## ii. Key results

- `GHSSignDominance` : the GHS sign condition at distinct sites
- `gc_ursell_nonpos_of_signDominance` : the sign condition gives `u₃ ≤ 0` at all sites
- `gc_ghs_concavity_of_signDominance` : the sign condition gives `GHSThreePointSym`
- `gc_aizenman_barsky_of_signDominance` : the sign condition gives the Aizenman–Barsky inequality
- `gc_ursell_currentSum_rep` : random-current form of `u₃` at zero field

## iii. Table of contents

- A. The Lebowitz four-point form
- B. The GHS sign condition
- C. Random-current form at zero field

## iv. References

- R. B. Griffiths, C. A. Hurst, S. Sherman, "Concavity of magnetization of an Ising ferromagnet in a
  positive external field", J. Math. Phys. 11 (1970) 790–795
- J. L. Lebowitz, "GHS and other inequalities", Comm. Math. Phys. 35 (1974) 87–92
- M. Aizenman, D. J. Barsky, R. Fernández, "The phase transition in a general class of Ising-type
  models is sharp", J. Stat. Phys. 47 (1987) 343–374

-/

@[expose] public section

open scoped BigOperators symmDiff
open Finset SimpleGraph Set


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. The Lebowitz four-point form -/

/-- Lebowitz's four-point combination `⟨σ_oσ_xσ_y⟩ - ⟨σ_oσ_x⟩⟨σ_y⟩ - ⟨σ_oσ_y⟩⟨σ_x⟩ - ⟨σ_o⟩⟨σ_xσ_y⟩`,
which differs from the Ursell function `u₃` by `2⟨σ_o⟩⟨σ_x⟩⟨σ_y⟩`. -/
noncomputable def gc_lebowitzU4 (β h : ℝ) (o x y : V) : ℝ :=
  isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
    - isingExpectation G β h (fun s => spin s o * spin s x)
        * isingExpectation G β h (fun s => spin s y)
    - isingExpectation G β h (fun s => spin s o * spin s y)
        * isingExpectation G β h (fun s => spin s x)
    - isingExpectation G β h (fun s => spin s o)
        * isingExpectation G β h (fun s => spin s x * spin s y)

lemma gc_ursell_eq_lebowitz_plus_triple (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y
      = gc_lebowitzU4 G β h o x y
        + 2 * isingExpectation G β h (fun s => spin s o)
            * isingExpectation G β h (fun s => spin s x)
            * isingExpectation G β h (fun s => spin s y) := by
  unfold eg_ursell3 gc_lebowitzU4
  ring

lemma gc_triple_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ 2 * isingExpectation G β h (fun s => spin s o)
          * isingExpectation G β h (fun s => spin s x)
          * isingExpectation G β h (fun s => spin s y) := by
  have ho : 0 ≤ isingExpectation G β h (fun s => spin s o) :=
    expectation_spin_nonneg G β h hβ hh o
  have hx : 0 ≤ isingExpectation G β h (fun s => spin s x) :=
    expectation_spin_nonneg G β h hβ hh x
  have hy : 0 ≤ isingExpectation G β h (fun s => spin s y) :=
    expectation_spin_nonneg G β h hβ hh y
  have h2o : 0 ≤ 2 * isingExpectation G β h (fun s => spin s o) := by linarith
  exact mul_nonneg (mul_nonneg h2o hx) hy

lemma gc_lebowitz_le_ursell (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    gc_lebowitzU4 G β h o x y ≤ eg_ursell3 G β h o x y := by
  rw [gc_ursell_eq_lebowitz_plus_triple]
  have := gc_triple_nonneg G β h hβ hh o x y
  linarith

/-! ## B. The GHS sign condition -/

/-- The GHS sign condition at `(β, h)` and root `o`: the third Ursell function `u₃(o, x, y)` is
nonpositive for all pairwise distinct `o, x, y`. It holds for `β, h ≥ 0` by `ghs_signDominance`. -/
def GHSSignDominance (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → eg_ursell3 G β h o x y ≤ 0

lemma gc_ursell_xeqy_nonpos (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x : V) (hox : o ≠ x) :
    eg_ursell3 G β h o x x ≤ 0 := by
  have hsq : eg_ursell3 G β h o x x
      = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h o x := by
    unfold eg_ursell3 cov2
    have h1 : isingExpectation G β h (fun s => spin s o * (spin s x * spin s x))
        = isingExpectation G β h (fun s => spin s o) := by
      congr 1; funext s; rw [spin_sq, mul_one]
    have h2 : isingExpectation G β h (fun s => spin s x * spin s x) = 1 :=
      expectation_spin_mul_self G β h x
    rw [h1, h2]; ring
  rw [hsq]
  have hspin : 0 ≤ isingExpectation G β h (fun s => spin s x) :=
    expectation_spin_nonneg G β h hβ hh x
  have hcov : 0 ≤ cov2 G β h o x := cov2_nonneg G β h hβ hh o x hox
  nlinarith [mul_nonneg hspin hcov]

lemma gc_ursell_nonpos_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 := by
  by_cases hox : o = x
  · subst hox
    by_cases hoy : o = y
    · subst hoy
      rw [ghc_ursell_degenerate]
      have hspin : 0 ≤ isingExpectation G β h (fun s => spin s o) :=
        expectation_spin_nonneg G β h hβ hh o
      have hsle : isingExpectation G β h (fun s => spin s o) ≤ 1 :=
        expectation_spin_le_one G β h o
      have hcov : 0 ≤ cov2 G β h o o := by
        unfold cov2
        rw [expectation_spin_mul_self]
        nlinarith [hspin, hsle]
      nlinarith [mul_nonneg hspin hcov]
    · exact ghc_ursell_nonpos_degenerate G β h hβ hh o y hoy
  · by_cases hoy : o = y
    · subst hoy
      rw [ghc_ursell_swap]
      exact ghc_ursell_nonpos_degenerate G β h hβ hh o x hox
    · by_cases hxy : x = y
      · subst hxy
        exact gc_ursell_xeqy_nonpos G β h hβ hh o x hox
      · exact hsd x y hox hoy hxy

lemma gc_ghs_concavity_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) :
    GHSThreePointSym G β h o :=
  ghc_ghs_of_ursell_nonpos G β h o
    (fun x y => gc_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y)

lemma gc_aizenman_barsky_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hsd : GHSSignDominance G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J (gc_ghs_concavity_of_signDominance G β h hβ hh o hsd) hfactor

/-! ## C. Random-current form at zero field -/

omit [Fintype V] in
lemma gc_spinProd_triple {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    spinProd ({o, x, y} : Finset V) = (fun s => spin s o * (spin s x * spin s y)) := by
  funext s
  rw [spinProd, Finset.prod_insert (by simp [hox, hoy]),
    Finset.prod_insert (by simp [hxy]), Finset.prod_singleton]

lemma gc_ursell_currentSum_rep (β : ℝ) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β 0 o x y
      = currentSum G β (fun _ => 1) {o, x, y} / currentSum G β (fun _ => 1) ∅
        - currentSum G β (fun _ => 1) {o} / currentSum G β (fun _ => 1) ∅
            * (currentSum G β (fun _ => 1) {x, y} / currentSum G β (fun _ => 1) ∅)
        - currentSum G β (fun _ => 1) {o, x} / currentSum G β (fun _ => 1) ∅
            * (currentSum G β (fun _ => 1) {y} / currentSum G β (fun _ => 1) ∅)
        - currentSum G β (fun _ => 1) {o, y} / currentSum G β (fun _ => 1) ∅
            * (currentSum G β (fun _ => 1) {x} / currentSum G β (fun _ => 1) ∅)
        + 2 * (currentSum G β (fun _ => 1) {o} / currentSum G β (fun _ => 1) ∅)
            * (currentSum G β (fun _ => 1) {x} / currentSum G β (fun _ => 1) ∅)
            * (currentSum G β (fun _ => 1) {y} / currentSum G β (fun _ => 1) ∅) := by
  have hoxy := isingExpectation_eq_currentSum_ratio G β ({o, x, y} : Finset V)
  have ho := isingExpectation_eq_currentSum_ratio G β ({o} : Finset V)
  have hx := isingExpectation_eq_currentSum_ratio G β ({x} : Finset V)
  have hy := isingExpectation_eq_currentSum_ratio G β ({y} : Finset V)
  have hoxe := isingExpectation_eq_currentSum_ratio G β ({o, x} : Finset V)
  have hoye := isingExpectation_eq_currentSum_ratio G β ({o, y} : Finset V)
  have hxye := isingExpectation_eq_currentSum_ratio G β ({x, y} : Finset V)
  rw [gc_spinProd_triple hox hoy hxy] at hoxy
  rw [spinProd_singleton] at ho hx hy
  rw [spinProd_pair o x hox] at hoxe
  rw [spinProd_pair o y hoy] at hoye
  rw [spinProd_pair x y hxy] at hxye
  unfold eg_ursell3
  rw [hoxy, ho, hx, hy, hoxe, hoye, hxye]

end StatMech.Walls
