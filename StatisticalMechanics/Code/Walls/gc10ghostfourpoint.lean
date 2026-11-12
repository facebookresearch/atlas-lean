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
import Code.Sharpness.CurrentRep
import Code.Sharpness.RandomCurrent
import Code.Sharpness.FieldGhostDict
import Code.Walls.gc6_ghostgraph
import Code.Walls.gc5_urselleqgap

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




























noncomputable def eg_ursell4_ghostPlus (β h : ℝ) (o x y : V) : ℝ :=
  expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
    - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, x} : Finset V).map someEmb)
        * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({y} : Finset V).map someEmb))
    - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, y} : Finset V).map someEmb)
        * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({x} : Finset V).map someEmb))
    - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({o} : Finset V).map someEmb))
        * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({x, y} : Finset V).map someEmb)

















theorem gc10_moment_oxyg (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
      = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) := by
  have hcard : ({o, x, y} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hox, hoy]),
        Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  rw [gc6_expectationJ_ghost_odd G β h ({o, x, y} : Finset V) (by rw [hcard]; exact ⟨1, rfl⟩)]
  congr 1; funext s; unfold spinProd
  rw [Finset.prod_insert (by simp [hox, hoy]), Finset.prod_insert (by simp [hxy]),
      Finset.prod_singleton]




theorem gc10_moment_pair (β h : ℝ) (o x : V) (hox : o ≠ x) :
    expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, x} : Finset V).map someEmb)
      = isingExpectation G β h (fun s => spin s o * spin s x) := by
  rw [fgd_expectationJ_ghost_eq G β h ({o, x} : Finset V)
        (by rw [Finset.card_pair hox]; exact even_two)]
  congr 1; funext s; unfold spinProd; rw [Finset.prod_pair hox]




theorem gc10_moment_ghostSingle (β h : ℝ) (y : V) :
    expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb))
      = isingExpectation G β h (fun s => spin s y) :=
  gc6_ghostGraph_dictionary G β h y
























theorem gc10_ursell4_ghostPlus_eq (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell4_ghostPlus G β h o x y = eg_ursell4_ghost G β h o x y := by
  unfold eg_ursell4_ghostPlus eg_ursell4_ghost
  rw [gc10_moment_oxyg G β h o x y hox hoy hxy,
      gc10_moment_pair G β h o x hox, gc10_moment_ghostSingle G β h y,
      gc10_moment_pair G β h o y hoy, gc10_moment_ghostSingle G β h x,
      gc10_moment_ghostSingle G β h o, gc10_moment_pair G β h x y hxy]

























theorem gc10_ghostFourPoint (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y
      = eg_ursell4_ghostPlus G β h o x y
        + 2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
  rw [gc5_ursellEqGap G β h o x y, gc10_ursell4_ghostPlus_eq G β h o x y hox hoy hxy]
  unfold eg_tripleProduct onePt
  ring




theorem gc10_ursell4_ghostPlus_eq_ursell_sub (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell4_ghostPlus G β h o x y
      = eg_ursell3 G β h o x y - 2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
  rw [gc10_ghostFourPoint G β h o x y hox hoy hxy]; ring














theorem gc10_ghostFourPoint_eq_gap (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell4_ghostPlus G β h o x y
      = (cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y))
          - 2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
  rw [gc10_ursell4_ghostPlus_eq_ursell_sub G β h o x y hox hoy hxy, ghc_ursellEqGap]









theorem gc10_ghs_iff_ghostFourPoint (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y)
      ↔ eg_ursell4_ghostPlus G β h o x y
          ≤ -2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
  rw [gc10_ghostFourPoint_eq_gap G β h o x y hox hoy hxy]
  constructor <;> intro hle <;> linarith


















theorem gc10_ghostFourPoint_nonpos_degenerate (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (x y : V) (hxy : x ≠ y) :
    eg_ursell4_ghost G β h x x y ≤ 0 :=
  gc5_ursell4_ghost_nonpos_degenerate G β h hβ hh x y hxy















theorem gc10_ghostFourPoint_nonvacuous :
    eg_ursell3 (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2
      = eg_ursell4_ghostPlus (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2
        + 2 * (onePt (⊤ : SimpleGraph (Fin 3)) 1 1 0
            * onePt (⊤ : SimpleGraph (Fin 3)) 1 1 1
            * onePt (⊤ : SimpleGraph (Fin 3)) 1 1 2) :=
  gc10_ghostFourPoint (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 (by decide) (by decide) (by decide)



theorem gc10_ursell4_ghostPlus_eq_nonvacuous :
    eg_ursell4_ghostPlus (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2
      = eg_ursell4_ghost (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 :=
  gc10_ursell4_ghostPlus_eq (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 (by decide) (by decide) (by decide)

end StatMech.Walls
