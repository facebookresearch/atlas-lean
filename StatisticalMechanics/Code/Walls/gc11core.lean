/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































































import Mathlib
import Code.Walls.gc10eq15
import Code.Walls.gc10ghostfourpoint
import Code.Walls.gc10core
import Code.Ising.CorrelationRatio

open Finset BigOperators SimpleGraph
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]












noncomputable def gc11_Jghost (β h : ℝ) : Sym2 (Option V) → ℝ := ghostCoupling h β (fun _ => 1)




noncomputable def gc11_Z0 (β h : ℝ) : ℝ :=
  Sharpness.currentSum (withGhost G) β (gc11_Jghost β h) ∅





theorem gc11_Z0_pos (β h : ℝ) : 0 < gc11_Z0 G β h :=
  gc10_eq15_currentMass_pos G β (ghostCoupling h β (fun _ => 1))






























theorem gc11_cleared (β h : ℝ) (o x y : V) :
    eg_ursell4_ghostPlus G β h o x y * (gc11_Z0 G β h) ^ 2
      = gc11_Z0 G β h
          * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h)
              (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h)
            (({o, x} : Finset V).map someEmb)
            (insert (none : Option V) (({y} : Finset V).map someEmb))
        - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h)
            (({o, y} : Finset V).map someEmb)
            (insert (none : Option V) (({x} : Finset V).map someEmb))
        - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h)
            (insert (none : Option V) (({o} : Finset V).map someEmb))
            (({x, y} : Finset V).map someEmb) := by
  unfold eg_ursell4_ghostPlus gc11_Z0 gc11_Jghost
  rw [Sharpness.sourcePairSum_eq_mul, Sharpness.sourcePairSum_eq_mul,
      Sharpness.sourcePairSum_eq_mul]
  rw [gc10_eq15_ghost G β _ (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)),
      gc10_eq15_ghost G β _ (({o, x} : Finset V).map someEmb),
      gc10_eq15_ghost G β _ (insert (none : Option V) (({y} : Finset V).map someEmb)),
      gc10_eq15_ghost G β _ (({o, y} : Finset V).map someEmb),
      gc10_eq15_ghost G β _ (insert (none : Option V) (({x} : Finset V).map someEmb)),
      gc10_eq15_ghost G β _ (insert (none : Option V) (({o} : Finset V).map someEmb)),
      gc10_eq15_ghost G β _ (({x, y} : Finset V).map someEmb)]
  ring





















theorem gc11_triple_Z0cube_eq (β h : ℝ) (o x y : V) :
    (onePt G β h o * onePt G β h x * onePt G β h y) * (gc11_Z0 G β h) ^ 3
      = Sharpness.currentSum (withGhost G) β (gc11_Jghost β h)
            (insert (none : Option V) (({o} : Finset V).map someEmb))
        * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h)
            (insert (none : Option V) (({x} : Finset V).map someEmb))
        * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h)
            (insert (none : Option V) (({y} : Finset V).map someEmb)) := by
  unfold onePt gc11_Z0 gc11_Jghost
  rw [gc10_eq15_magnetization, gc10_eq15_magnetization, gc10_eq15_magnetization]
  ring

























def gc11_ClearedSign (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    gc11_Z0 G β h
        * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h)
            (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
      - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h)
          (({o, x} : Finset V).map someEmb)
          (insert (none : Option V) (({y} : Finset V).map someEmb))
      - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h)
          (({o, y} : Finset V).map someEmb)
          (insert (none : Option V) (({x} : Finset V).map someEmb))
      - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h)
          (insert (none : Option V) (({o} : Finset V).map someEmb))
          (({x, y} : Finset V).map someEmb)
    ≤ -2 * (onePt G β h o * onePt G β h x * onePt G β h y) * (gc11_Z0 G β h) ^ 2








theorem gc11_clearedSign_iff (β h : ℝ) (o : V) :
    gc11_ClearedSign G β h o ↔ gc10_GhostFourPointSign G β h o := by
  constructor
  · intro hres x y hox hoy hxy
    have hZ2 : 0 < (gc11_Z0 G β h) ^ 2 := pow_pos (gc11_Z0_pos G β h) 2
    have hid := gc11_cleared G β h o x y
    have hrr := hres x y hox hoy hxy
    rw [← hid] at hrr
    nlinarith [hrr, hZ2]
  · intro hres x y hox hoy hxy
    have hZ2 : 0 < (gc11_Z0 G β h) ^ 2 := pow_pos (gc11_Z0_pos G β h) 2
    have hid := gc11_cleared G β h o x y
    have hrr := hres x y hox hoy hxy
    rw [← hid]
    nlinarith [hrr, hZ2]



theorem gc11_ghostFourPointSign_of_clearedSign (β h : ℝ) (o : V)
    (hres : gc11_ClearedSign G β h o) :
    gc10_GhostFourPointSign G β h o :=
  (gc11_clearedSign_iff G β h o).mp hres









theorem gc11_core_ursell_nonpos_distinct (β h : ℝ) (o : V)
    (hres : gc11_ClearedSign G β h o)
    {x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc10_core_ursell_nonpos_distinct G β h o (gc11_ghostFourPointSign_of_clearedSign G β h o hres)
    hox hoy hxy


theorem gc11_core_signDominance (β h : ℝ) (o : V)
    (hres : gc11_ClearedSign G β h o) :
    GHSSignDominance G β h o :=
  gc10_core_signDominance G β h o (gc11_ghostFourPointSign_of_clearedSign G β h o hres)





theorem gc11_core_ghs (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : gc11_ClearedSign G β h o) :
    GHSThreePointSym G β h o :=
  gc10_core_ghs G β h hβ hh o (gc11_ghostFourPointSign_of_clearedSign G β h o hres)




theorem gc11_core_sharpness (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hres : gc11_ClearedSign G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc10_core_sharpness G β h hβ hh o J (gc11_ghostFourPointSign_of_clearedSign G β h o hres) hfactor











theorem gc11_clearedSign_of_familyRealise (β h : ℝ) (o : V)
    (hfr : gc5_FamilyRealise G β h o) :
    gc11_ClearedSign G β h o :=
  (gc11_clearedSign_iff G β h o).mpr (gc10_residue_of_familyRealise G β h o hfr)




theorem gc11_clearedSign_of_eqSwi (β h : ℝ) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) :
    gc11_ClearedSign G β h o :=
  (gc11_clearedSign_iff G β h o).mpr (gc10_residue_of_eqSwi G β h o hid)




















theorem gc11_claim1_griffiths_step (eS cS eΛ : ℝ)
    (hSnn : 0 ≤ eS) (hcSnn : 0 ≤ cS) (hgriff : eS ≤ eΛ) :
    eΛ * (eS * cS) ≥ eS ^ 2 * cS :=
  acr_claim1_griffiths_step eS cS eΛ hSnn hcSnn hgriff












theorem gc11_cleared_nonvacuous :
    eg_ursell4_ghostPlus (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2
        * (gc11_Z0 (⊤ : SimpleGraph (Fin 3)) 1 1) ^ 2
      = gc11_Z0 (⊤ : SimpleGraph (Fin 3)) 1 1
          * Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
              (gc11_Jghost 1 1)
              (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb))
        - Sharpness.sourcePairSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (gc11_Jghost 1 1)
            (({0, 1} : Finset (Fin 3)).map someEmb)
            (insert (none : Option (Fin 3)) (({2} : Finset (Fin 3)).map someEmb))
        - Sharpness.sourcePairSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (gc11_Jghost 1 1)
            (({0, 2} : Finset (Fin 3)).map someEmb)
            (insert (none : Option (Fin 3)) (({1} : Finset (Fin 3)).map someEmb))
        - Sharpness.sourcePairSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (gc11_Jghost 1 1)
            (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb))
            (({1, 2} : Finset (Fin 3)).map someEmb) :=
  gc11_cleared (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2




theorem gc11_clearedSign_reduction_nonvacuous :
    0 < gc11_Z0 (⊤ : SimpleGraph (Fin 3)) 1 1
      ∧ (gc11_ClearedSign (⊤ : SimpleGraph (Fin 3)) 1 1 0
          ↔ gc10_GhostFourPointSign (⊤ : SimpleGraph (Fin 3)) 1 1 0) :=
  ⟨gc11_Z0_pos (⊤ : SimpleGraph (Fin 3)) 1 1,
   gc11_clearedSign_iff (⊤ : SimpleGraph (Fin 3)) 1 1 0⟩

end StatMech.Walls
