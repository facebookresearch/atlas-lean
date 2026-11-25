/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ToricMinkowskiWeights

/-!
# Integral fan displacement

Fulton--Sturmfels, *Intersection Theory on Toric Varieties*,
alg-geom/9403002v1, Theorems 2.1 and 3.2. The sum and the balancing
subgroup are already the actual lattice constructions. The requests prove
closure and generic-choice independence; no product or toric Chow
comparison is supplied as the theorem's conclusion in the input data.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ToricMinkowskiWeightsWanted

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.ToricMinkowskiWeights

/-- **Primitive normal vectors of the codimension-one faces of a fan.** For a finite fan $F$ in
$\mathbb{R}^n$ (finitely many rational salient cones, closed under taking faces, the intersection of
any two being a face of each): a choice, for every cone $\sigma$ of $F$ and every face $\tau$ of
$\sigma$ with $\dim \tau + 1 = \dim \sigma$, of a vector
$v \in N_\sigma = \mathbb{Z}^n \cap \operatorname{span} \sigma$ whose class in
$\mathbb{Z}^n / N_\tau$ is nonzero and generates the image of $N_\sigma$, and with
$v \in \sigma + \operatorname{span} \tau$ (Fulton–Sturmfels, *Intersection theory on toric
varieties*, §2). -/
def_wanted normalData (n : ℕ) (F : FiniteFan n) : NormalData F

theorem_wanted product_balanced (n : ℕ) (F : FiniteFan n) (N : NormalData F)
    (_complete : F.IsComplete) (k l : ℕ) (w : weights F N k) (v : weights F N l)
    (a : RealSpace n) (_generic : GenericDisplacement F a) :
    displacementProduct F k l w.val v.val a ∈ weights F N (k + l)

theorem_wanted displacement_independent (n : ℕ) (F : FiniteFan n) (N : NormalData F)
    (_complete : F.IsComplete) (k l : ℕ) (w : weights F N k) (v : weights F N l)
    (a b : RealSpace n) (_generic_a : GenericDisplacement F a)
    (_generic_b : GenericDisplacement F b) :
    displacementProduct F k l w.val v.val a = displacementProduct F k l w.val v.val b

end WantedExt.AlgebraicGeometry.ToricMinkowskiWeightsWanted
