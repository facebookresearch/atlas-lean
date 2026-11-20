/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Ising.KramersWannierEvenToCut
import Code.Ising.KWClosedWalkParity

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Walls







section Coboundary

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}




def colourDisagrees (c : V → Bool) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => c u ≠ c v, by
    intro a b; exact propext ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩⟩ e

omit [DecidableEq V] in
@[simp] theorem colourDisagrees_mk (c : V → Bool) (u v : V) :
    colourDisagrees c s(u, v) ↔ c u ≠ c v := by
  unfold colourDisagrees; rw [Sym2.lift_mk]

instance (c : V → Bool) (e : Sym2 V) : Decidable (colourDisagrees c e) :=
  Sym2.recOnSubsingleton e (fun a b => by
    change Decidable (Sym2.lift _ s(a, b))
    rw [Sym2.lift_mk]; infer_instance)

variable [Fintype V] [DecidableRel Gp.Adj]




noncomputable def coboundary (Gp : SimpleGraph V) [Fintype V] [DecidableRel Gp.Adj]
    (c : V → Bool) : Finset (Sym2 V) :=
  Gp.edgeFinset.filter (colourDisagrees c)

omit [DecidableEq V] in



theorem mem_coboundary_iff (c : V → Bool) {u v : V} (h : Gp.Adj u v) :
    s(u, v) ∈ coboundary Gp c ↔ c u ≠ c v := by
  unfold coboundary
  rw [Finset.mem_filter, colourDisagrees_mk]
  exact ⟨fun h2 => h2.2, fun h2 => ⟨by rw [SimpleGraph.mem_edgeFinset]; exact h, h2⟩⟩

omit [DecidableEq V] in


theorem coboundary_subset_edgeFinset (c : V → Bool) :
    coboundary Gp c ⊆ Gp.edgeFinset := by
  unfold coboundary; exact Finset.filter_subset _ _

end Coboundary









section TheNode

variable {V : Type*} [Fintype V] [DecidableEq V] {Gp : SimpleGraph V} [DecidableRel Gp.Adj]





theorem walkParity_coboundary_eq_xor (c : V → Bool) {x y : V} (p : Gp.Walk x y) :
    StatMech.Ising.walkParity Gp (coboundary Gp c) p = (c x).xor (c y) :=
  StatMech.Ising.walkParity_eq_xor_of_isCoboundary c (fun h => mem_coboundary_iff c h) p










theorem evenOnCycles_coboundary (c : V → Bool) :
    StatMech.Ising.EvenOnCycles Gp (coboundary Gp c) :=
  StatMech.Ising.evenOnCycles_of_isCoboundary c (fun h => mem_coboundary_iff c h)




theorem walkParity_coboundary_loop (c : V → Bool) {x : V} (p : Gp.Walk x x) :
    StatMech.Ising.walkParity Gp (coboundary Gp c) p = false :=
  evenOnCycles_coboundary c x p

end TheNode







section CutForm

variable {V : Type*} [Fintype V] [DecidableEq V] {Gp : SimpleGraph V} [DecidableRel Gp.Adj]

omit [DecidableEq V] in



theorem coboundary_eq_cutEdges (c : V → Bool) :
    coboundary Gp c = StatMech.Ising.cutEdges Gp c := by
  apply Finset.ext
  intro e
  refine Sym2.recOnSubsingleton e (fun u v => ?_)
  by_cases h : Gp.Adj u v
  · rw [mem_coboundary_iff c h, StatMech.Ising.mem_cutEdges_iff Gp c h]
  · constructor
    · intro hmem
      have hin := coboundary_subset_edgeFinset c hmem
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hin
      exact absurd hin h
    · intro hmem
      have hin : s(u, v) ∈ Gp.edgeFinset := by
        unfold StatMech.Ising.cutEdges at hmem
        exact (Finset.mem_filter.mp hmem).1
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hin
      exact absurd hin h





theorem evenOnCycles_cutEdges' (c : V → Bool) :
    StatMech.Ising.EvenOnCycles Gp (StatMech.Ising.cutEdges Gp c) := by
  rw [← coboundary_eq_cutEdges]
  exact evenOnCycles_coboundary c

end CutForm

end Walls

end StatMech
