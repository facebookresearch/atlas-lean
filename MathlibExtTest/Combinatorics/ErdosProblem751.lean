/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ErdosProblem751
import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem751Wanted

example : ¬ conjecture := conjecture_refuted

/-- Already the gap `3` fails: no graph of chromatic number `4` has all of its distinct cycle
lengths at least three apart. -/
example : ¬ ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = 4 ∧
    ∀ m ∈ G.cycleLengths, ∀ m' ∈ G.cycleLengths, m < m' → m + 3 ≤ m' := by
  rintro ⟨V, G, hχ, hgap⟩
  have hcol : ¬ G.Colorable 3 := fun hc => by
    have := hc.chromaticNumber_le
    rw [hχ] at this
    norm_cast at this
  obtain ⟨m, hm, m', hm', hlt, hle⟩ := exists_cycleLengths_lt_le_add_two_of_not_colorable hcol
  have := hgap m hm m' hm' hlt
  omega

/-- The minimum-degree form applies to the complete graph on four vertices, whose minimum degree
is three. -/
example : ∃ m ∈ (⊤ : SimpleGraph (Fin 4)).cycleLengths,
    ∃ m' ∈ (⊤ : SimpleGraph (Fin 4)).cycleLengths, m < m' ∧ m' ≤ m + 2 :=
  exists_cycleLengths_lt_le_add_two_of_three_le_minDegree (by simp [SimpleGraph.minDegree_top])

/-- The colouring form applies on an infinite vertex type: the complete graph on `ℕ` is not
`3`-colourable, since it contains a clique on four vertices. -/
example : ∃ m ∈ (⊤ : SimpleGraph ℕ).cycleLengths,
    ∃ m' ∈ (⊤ : SimpleGraph ℕ).cycleLengths, m < m' ∧ m' ≤ m + 2 := by
  refine exists_cycleLengths_lt_le_add_two_of_not_colorable fun hc => ?_
  have hclique : (⊤ : SimpleGraph ℕ).IsClique ((Finset.range 4 : Finset ℕ) : Set ℕ) :=
    fun _ _ _ _ h => h
  have := hclique.card_le_of_colorable hc
  simp at this

end MathlibExt.Combinatorics.ErdosProblem751Wanted
