/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.WeakHomotopySingleton
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence

/-!
# A connectedness criterion for conull realization

The realization of the terminal simplicial set is a singleton. Its literal
terminal map is a realization weak equivalence when the original realization
is path-connected and all its positive homotopy groups are trivial.

The criterion applies the TopCat singleton comparison to that same realized
map, retaining the original simplicial set and its basepoints.
-/

@[expose] public section

universe u

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology Topology.Homotopy

namespace SSet

section Part1


/-- The actual realization of the chosen terminal simplicial set is a
singleton, by its standard-zero-simplex Iso and genuine affine homeomorphism. -/
theorem realizedTerminal_subsingleton :
    Subsingleton (SSet.toTop.obj (⊤_ SSet.{u})) := by
  let e : (Δ[0] : SSet.{u}) ≅ (⊤_ SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso terminalIsTerminal
  let d := SSet.toTop.mapIso e
  constructor
  intro a b
  apply (ConcreteCategory.bijective_of_isIso d.inv).1
  apply (SimplexCategory.toTopHomeo ⦋0⦌).injective
  exact Subsingleton.elim _ _

/-- The exact terminal map of a simplicial set is a realization weak
equivalence when its actual realization is connected and has trivial positive groups. -/
theorem conull_mem_realizationWeakEquivalences_of_pathConnected_positive
    (K : SSet.{u}) (hConn : PathConnectedSpace (SSet.toTop.obj K))
    (hPositive : ∀ (n : ℕ) (x : SSet.toTop.obj K),
      Subsingleton (HomotopyGroup.Pi (n + 1) (SSet.toTop.obj K) x)) :
    SSet.realizationWeakEquivalences (terminal.from K) := by
  apply (SSet.mem_realizationWeakEquivalences_iff (terminal.from K)).mpr
  apply (TopCat.mem_weakHomotopyEquivalences_iff
    (SSet.toTop.map (terminal.from K))).mp
  exact TopCat.map_mem_weakHomotopyEquivalences_to_singleton
    (SSet.toTop.map (terminal.from K)) realizedTerminal_subsingleton hConn hPositive

end Part1

end SSet

end
