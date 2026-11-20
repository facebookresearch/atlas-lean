/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Walls.gc5_core
import Code.Walls.gc6_munonneg

open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]













theorem gc6_core_mu_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) :
    0 ≤ isingExpectation G β h (spinProd A) :=
  gc6_mu_nonneg G β h hβ hh A


































def gc6_EqSwiIdentity (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    ∃ (J : Sym2 V → ℝ) (μ : ℝ) (M : Finset (Ising.Current V)) (B : Finset V) (o' x' y' : V),
      (0 ≤ β) ∧ (∀ e, 0 ≤ J e) ∧ (0 ≤ μ)
      ∧ (o' ≠ x') ∧ (o' ≠ y') ∧ (x' ≠ y')
      ∧ (0 < tcp_partitionFunction G β J M B)
      ∧ eg_ursell3 G β h o x y * tcp_partitionFunction G β J M B
          = μ * egh_ensembleUrsell G β J M B o' x' y'












theorem gc6_core_familyRealise_of_eqSwi (β h : ℝ) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) :
    gc5_FamilyRealise G β h o := by
  intro x y hox hoy hxy
  obtain ⟨J, μ, M, B, o', x', y', hβ, hJ, hμ, hox', hoy', hxy', hZpos, hident⟩ :=
    hid x y hox hoy hxy
  refine ⟨J, μ, M, B, o', x', y', hβ, hJ, hμ, ?_⟩
  
  unfold tcp_allConnProb
  rw [egh_ensemble_ursell_eq G β J M B hox' hoy' hxy'] at hident
  have hZne : tcp_partitionFunction G β J M B ≠ 0 := ne_of_gt hZpos
  field_simp
  linarith [hident]











theorem gc6_core_signDominance (β h : ℝ) (o : V) (hid : gc6_EqSwiIdentity G β h o) :
    GHSSignDominance G β h o :=
  gc5_core_signDominance_of_familyRealise G β h o
    (gc6_core_familyRealise_of_eqSwi G β h o hid)





theorem gc6_core_ursell_nonpos (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc5_core_ursell_nonpos_of_familyRealise G β h hβ hh o
    (gc6_core_familyRealise_of_eqSwi G β h o hid) x y




theorem gc6_core_ghs_concavity (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) :
    GHSThreePointSym G β h o :=
  gc5_core_ghs_concavity_of_familyRealise G β h hβ hh o
    (gc6_core_familyRealise_of_eqSwi G β h o hid)












theorem gc6_core_sharpness (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hid : gc6_EqSwiIdentity G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc5_core_sharpness_of_familyRealise G β h hβ hh o J
    (gc6_core_familyRealise_of_eqSwi G β h o hid) hfactor














theorem gc6_core_bracket_surjective {μ t : ℝ} (hμ : 0 ≤ μ) (hlo : -2 * μ ≤ t) (hhi : t ≤ 0) :
    ∃ P : ℝ, 0 ≤ P ∧ P ≤ 1 ∧ -2 * μ * P = t :=
  gc5_familyRealise_bracket_surjective hμ hlo hhi







theorem gc6_core_sharpening (β h : ℝ) (o : V) (hid : gc6_EqSwiIdentity G β h o) :
    gc5_FamilyRealise G β h o :=
  gc6_core_familyRealise_of_eqSwi G β h o hid














theorem gc6_core_eqSwi_degenerate_shape (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x y : V) (hxy : x ≠ y) :
    ∃ μ : ℝ, 0 ≤ μ ∧ eg_ursell3 G β h x x y = -2 * μ * 1 :=
  gc5_familyRealise_degenerate G β h hβ hh x y hxy






theorem gc6_core_mu_clause (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ = isingExpectation G β h (spinProd A) :=
  gc6_familyRealise_mu_clause G β h hβ hh A













theorem gc6_core_ursell_eq_lebowitz_plus_triple (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y
      = gc_lebowitzU4 G β h o x y
        + 2 * isingExpectation G β h (fun s => spin s o)
            * isingExpectation G β h (fun s => spin s x)
            * isingExpectation G β h (fun s => spin s y) :=
  gc5_core_ursell_eq_lebowitz_plus_triple G β h o x y











theorem gc6_core_consistent (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) {μ : ℝ} (hμ : 0 ≤ μ) :
    -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 :=
  gc5_core_u3_nonpos G β J hβ hJ M B o x y hμ

end StatMech.Walls
