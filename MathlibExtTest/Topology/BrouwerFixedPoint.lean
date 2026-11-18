/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.BrouwerFixedPoint

@[expose] public section

open Convexity MathlibExt.Topology.BrouwerFixedPoint

namespace MathlibExtTest.Topology.BrouwerFixedPoint

/-- Non-vacuity: the hypotheses hold for a constant map of the 2-simplex, whose fixed point is
the constant value. -/
example : ∃ x : StdSimplex ℝ (Fin 3), (fun _ => StdSimplex.single (0 : Fin 3)) x = x :=
  exists_fixedPoint _ continuous_const

/-- The fixed point of a constant map is forced to be its value. -/
example (x : StdSimplex ℝ (Fin 3))
    (hx : (fun _ : StdSimplex ℝ (Fin 3) => StdSimplex.single (0 : Fin 3)) x = x) :
    x = StdSimplex.single 0 := hx.symm

/-- The covering lemma on a concrete point: the vertex `e₀` and the identity map. -/
example : ∃ i : Fin 3, 0 < (StdSimplex.single (0 : Fin 3) : StdSimplex ℝ (Fin 3)).weights i ∧
    (id (StdSimplex.single (0 : Fin 3)) : StdSimplex ℝ (Fin 3)).weights i ≤
      (StdSimplex.single (0 : Fin 3) : StdSimplex ℝ (Fin 3)).weights i :=
  exists_pos_weights_le id _

/-- Non-vacuity of the product form: the swap of the two factors of `Δ¹ × Δ¹` is continuous and
has a fixed point (any diagonal pair). -/
example : ∃ σ : Fin 2 → StdSimplex ℝ (Fin 2), (fun σ : Fin 2 → StdSimplex ℝ (Fin 2) =>
    fun i => σ (Fin.rev i)) σ = σ :=
  exists_fixedPoint_pi _ (continuous_pi fun _ => continuous_apply _)

/-- The product distribution has the factors as marginals, on a concrete pair. -/
example (σ : Fin 2 → StdSimplex ℝ (Fin 2)) : (prodSimplex σ).map (fun s => s 1) = σ 1 :=
  marginal_prodSimplex σ 1

/-- Brouwer for a simplex indexed by `Bool`. -/
example : ∃ x : StdSimplex ℝ Bool, (fun _ => StdSimplex.single true) x = x :=
  exists_fixedPoint_of_finite _ continuous_const

end MathlibExtTest.Topology.BrouwerFixedPoint
