/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.AdmissibleGrid

/-!
# Empty admissible grids and Banach-valued integrals

An empty filling at scale one has no reduced boundary and is admissible
for `K = G = ∅`. Its public admissibility predicate then gives zero index
at every complex point. Both the reduced integral and the associated
cycle integral vanish for every function into a complete complex normed
space; no continuity or analyticity of the integrand is required here.
The concrete product-valued case retains its two complex coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set

namespace EmptyAdmissibleGridSmoke

private def emptyGrid : GridFilling := GridFilling.empty 1 zero_lt_one

private theorem empty_admissible :
    emptyGrid.IsAdmissibleFor (∅ : Set ℂ) (∅ : Set ℂ) :=
  GridFilling.empty_isAdmissibleFor_empty 1 zero_lt_one ∅

example :
    emptyGrid.boundaryEdges = ∅ ∧ emptyGrid.reducedTrace = ∅ ∧
      ∀ z : ℂ, emptyGrid.toCycle.index z = 0 := by
  refine ⟨GridFilling.empty_boundaryEdges 1 zero_lt_one,
    GridFilling.empty_reducedTrace 1 zero_lt_one, ?_⟩
  intro z
  exact empty_admissible.2.2 z (by simp only [mem_empty_iff_false, not_false_eq_true])

private theorem empty_integrals {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) :
    emptyGrid.reducedIntegral f = 0 ∧ emptyGrid.toCycle.integral f = 0 := by
  constructor
  · exact GridFilling.empty_reducedIntegral 1 zero_lt_one f
  · change (GridFilling.empty 1 zero_lt_one).toCycle.integral f = 0
    rw [GridFilling.empty_toCycle]
    exact RectilinearCycle.integral_zero f

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : ℂ → E) :
    emptyGrid.reducedIntegral f = 0 ∧ emptyGrid.toCycle.integral f = 0 :=
  empty_integrals f

example :
    emptyGrid.reducedIntegral (fun z : ℂ => (z, star z)) = (0 : ℂ × ℂ) ∧
      emptyGrid.toCycle.integral (fun z : ℂ => (z, star z)) = (0 : ℂ × ℂ) :=
  empty_integrals (fun z : ℂ => (z, star z))

end EmptyAdmissibleGridSmoke
