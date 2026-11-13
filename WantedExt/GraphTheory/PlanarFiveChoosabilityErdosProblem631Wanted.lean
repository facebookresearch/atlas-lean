/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# List colouring planar graphs (Erdős Problem 631)

Erdős Problem 631 (Erdős, Rubin and Taylor): does every planar graph `G` have list chromatic number
`χ_L(G) ≤ 5`? Is this best possible?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.ListColoring
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.GraphTheory.PlanarFiveChoosabilityErdosProblem631Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #631, https://www.erdosproblems.com/631 (status
PROVED). UnsolvedMath record UM-30006959 (`EP-631`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite. Planarity is MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free straight-line
drawing), equivalent to planarity for finite simple graphs by Fáry's theorem; `χ_L(G) ≤ q` is
MathlibExt's `SimpleGraph.IsListColorable q` (every assignment of lists of at least `q` colours
admits a proper colouring from the lists). 'Best possible' means that some planar graph has `χ_L(G)
= 5` (MathlibExt's `SimpleGraph.IsChoiceNumber 5`). MathlibExt's `planar_five_choosable_of_step`
proves the first part only conditionally on geometric step data.
-/

/-- Erdős Problem 631, first question (Erdős, Rubin and Taylor): every finite planar graph has list
chromatic number at most `5`. Planarity is `SimpleGraph.IsPlanar` (a crossing-free straight-line
drawing, equivalent to planarity for finite graphs by Fáry's theorem). -/
def planarFiveChoosable : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsPlanar → G.IsListColorable 5

/-- Erdős Problem 631, second question: the bound `5` is best possible, i.e. some finite planar
graph has list chromatic number exactly `5`. -/
def planarListChromaticFiveAttained : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsPlanar ∧ G.IsChoiceNumber 5

/--
Resolved true: Thomassen proved that every planar graph is `5`-choosable; erdosproblems.com/631
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #631,
https://www.erdosproblems.com/631 (status PROVED); resolution: C. Thomassen, Every planar graph is
5-choosable, J. Combin. Theory Ser. B (1994), 180-181; M. Voigt, List colourings of planar graphs,
Discrete Math. (1993), 215-219, erdosproblems.com/631: the answer to both is yes; Thomassen proved
χ_L(G) ≤ 5 for planar G and Voigt constructed a planar graph with χ_L(G) = 5 (a simpler one by
Gutner, 1996), https://www.erdosproblems.com/631.
-/
public theorem_wanted planarFiveChoosable_holds : planarFiveChoosable

/--
Resolved true: Voigt constructed a planar graph with list chromatic number `5`, so the bound is best
possible (a simpler example is due to Gutner); erdosproblems.com/631 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #631, https://www.erdosproblems.com/631 (status
PROVED); resolution: C. Thomassen, Every planar graph is 5-choosable, J. Combin. Theory Ser. B
(1994), 180-181; M. Voigt, List colourings of planar graphs, Discrete Math. (1993), 215-219,
erdosproblems.com/631: the answer to both is yes; Thomassen proved χ_L(G) ≤ 5 for planar G and Voigt
constructed a planar graph with χ_L(G) = 5 (a simpler one by Gutner, 1996),
https://www.erdosproblems.com/631.
-/
public theorem_wanted planarListChromaticFiveAttained_holds : planarListChromaticFiveAttained

end MathlibExt.GraphTheory.PlanarFiveChoosabilityErdosProblem631Wanted
