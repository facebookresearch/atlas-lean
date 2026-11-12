/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































































import Mathlib
import Code.Walls.gc6_core
import Code.Walls.gc10ghostfourpoint
import Code.Walls.gc10ensembleprob

open scoped BigOperators symmDiff
open Finset SimpleGraph Set
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Walls.GhcEqGap
open StatMech.Walls.Gc5EqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]































def gc10_GhostFourPointSign (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    eg_ursell4_ghostPlus G β h o x y
      ≤ -2 * (onePt G β h o * onePt G β h x * onePt G β h y)












theorem gc10_core_ursell_nonpos_distinct (β h : ℝ) (o : V)
    (hres : gc10_GhostFourPointSign G β h o)
    {x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hsign := hres x y hox hoy hxy
  have hghs : cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) :=
    (gc10_ghs_iff_ghostFourPoint G β h o x y hox hoy hxy).mpr hsign
  exact (ghc_ursell_nonpos_iff_ghs G β h o x y).mpr hghs



theorem gc10_core_signDominance (β h : ℝ) (o : V)
    (hres : gc10_GhostFourPointSign G β h o) :
    GHSSignDominance G β h o :=
  fun x y hox hoy hxy => gc10_core_ursell_nonpos_distinct G β h o hres hox hoy hxy










theorem gc10_core_ghs (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : gc10_GhostFourPointSign G β h o) :
    GHSThreePointSym G β h o :=
  gc_ghs_concavity_of_signDominance G β h hβ hh o
    (gc10_core_signDominance G β h o hres)



theorem gc10_core_ursell_nonpos_all (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : gc10_GhostFourPointSign G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc_ursell_nonpos_of_signDominance G β h hβ hh o
    (gc10_core_signDominance G β h o hres) x y









theorem gc10_core_sharpness (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hres : gc10_GhostFourPointSign G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc_aizenman_barsky_of_signDominance G β h hβ hh o J
    (gc10_core_signDominance G β h o hres) hfactor














theorem gc10_residue_of_familyRealise (β h : ℝ) (o : V)
    (hfr : gc5_FamilyRealise G β h o) :
    gc10_GhostFourPointSign G β h o := by
  intro x y hox hoy hxy
  have hsd : GHSSignDominance G β h o :=
    gc5_core_signDominance_of_familyRealise G β h o hfr
  have hu3 : eg_ursell3 G β h o x y ≤ 0 := hsd x y hox hoy hxy
  have hghs : cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) :=
    (ghc_ursell_nonpos_iff_ghs G β h o x y).mp hu3
  exact (gc10_ghs_iff_ghostFourPoint G β h o x y hox hoy hxy).mp hghs




theorem gc10_residue_of_eqSwi (β h : ℝ) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) :
    gc10_GhostFourPointSign G β h o :=
  gc10_residue_of_familyRealise G β h o (gc6_core_familyRealise_of_eqSwi G β h o hid)















theorem gc10_residue_concreteProb_mem_Icc {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ) (hF : ∀ m, 0 ≤ F m) :
    gc10_allConnProb ends o x y g F ∈ Set.Icc (0 : ℝ) 1 :=
  gc10_allConnProb_mem_Icc ends o x y g F hF








theorem gc10_residue_of_concrete_identity (β h : ℝ) (o : V)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (g : V) (μ : ℝ) (F : Finset ι → ℝ) (hμ : 0 ≤ μ) (hF : ∀ m, 0 ≤ F m)
    (hid : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
        eg_ursell4_ghostPlus G β h o x y
          = -2 * μ * gc10_allConnProb ends o x y g F)
    (htriple : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
        onePt G β h o * onePt G β h x * onePt G β h y
          ≤ μ * gc10_allConnProb ends o x y g F) :
    gc10_GhostFourPointSign G β h o := by
  intro x y hox hoy hxy
  rw [hid x y hox hoy hxy]
  have := htriple x y hox hoy hxy
  nlinarith [this]













theorem gc10_core_ghs_of_concrete_identity (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (g : V) (μ : ℝ) (F : Finset ι → ℝ) (hμ : 0 ≤ μ) (hF : ∀ m, 0 ≤ F m)
    (hid : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
        eg_ursell4_ghostPlus G β h o x y
          = -2 * μ * gc10_allConnProb ends o x y g F)
    (htriple : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
        onePt G β h o * onePt G β h x * onePt G β h y
          ≤ μ * gc10_allConnProb ends o x y g F) :
    GHSThreePointSym G β h o :=
  gc10_core_ghs G β h hβ hh o
    (gc10_residue_of_concrete_identity G β h o ends g μ F hμ hF hid htriple)










theorem gc10_core_ghs_degenerate (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (x y : V) (hxy : x ≠ y) :
    eg_ursell4_ghost G β h x x y ≤ 0 :=
  gc10_ghostFourPoint_nonpos_degenerate G β h hβ hh x y hxy




theorem gc10_core_ursell_nonpos_xeqy (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x : V) (hox : o ≠ x) :
    eg_ursell3 G β h o x x ≤ 0 :=
  gc_ursell_xeqy_nonpos G β h hβ hh o x hox







theorem gc10_residue_nonvacuous :
    eg_ursell3 (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2
      = eg_ursell4_ghostPlus (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2
        + 2 * (onePt (⊤ : SimpleGraph (Fin 3)) 1 1 0
            * onePt (⊤ : SimpleGraph (Fin 3)) 1 1 1
            * onePt (⊤ : SimpleGraph (Fin 3)) 1 1 2) :=
  gc10_ghostFourPoint_nonvacuous

end StatMech.Walls
