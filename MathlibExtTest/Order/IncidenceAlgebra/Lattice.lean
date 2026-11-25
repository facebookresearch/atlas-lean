/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.IncidenceAlgebra.Lattice
public import Mathlib.Data.Finset.Interval

@[expose] public section

open Finset IncidenceAlgebra MathlibExt.Order.IncidenceAlgebra.Lattice

namespace MathlibExtTest.Order.IncidenceAlgebra.Lattice

/-- Weisner's theorem in the Boolean lattice of subsets of `Fin 2`, with `a = {0} ≠ 1̂`. -/
example : ∑ t ∈ univ.filter (fun t : Finset (Fin 2) => t ⊓ {0} = ⊥), mu ℤ t ⊤ = 0 :=
  sum_mu_top_of_inf_eq_bot ℤ (by decide)

/-- The crosscut hypotheses are satisfiable: the coatoms `{0}` and `{1}` of the subsets of
`Fin 2`, giving `μ(∅, {0, 1}) = N₀ - N₁ + N₂ = 0 - 0 + 1`. -/
example : mu ℤ (⊥ : Finset (Fin 2)) ⊤ = ∑ k ∈ range (({{0}, {1}} : Finset (Finset (Fin 2))).card + 1),
      (-1 : ℤ) ^ k * (((({{0}, {1}} : Finset (Finset (Fin 2))).powersetCard k).filter
        fun Y => Y.inf id = ⊥).card : ℤ) :=
  mu_bot_top_eq_sum_crosscut ℤ _ (by decide) (by decide)

end MathlibExtTest.Order.IncidenceAlgebra.Lattice
