/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.KWSelfDuality

/-!

# High-temperature expansion of the Ising partition function

The zero-field Ising partition function of a finite graph as `2^|V| cosh^|E| β` times the
even-subgraph generating function at `tanh β`.

## i. Overview

For the zero-field Ising model on a finite graph `G = (V, E)` with unit couplings, writing
`e^{β σᵢ σⱼ} = cosh β (1 + σᵢ σⱼ tanh β)` and summing over spins gives
`Z(β) = 2^|V| (cosh β)^|E| X(tanh β)`, where `X(x) = ∑_F x^|F|` runs over the even subgraphs `F` of
`G` (every vertex has even degree in `F`). This is the starting point of the combinatorial solution
of the two-dimensional Ising model.

## ii. Key results

- `ons_Z` : the zero-field partition function
- `ons_X` : the even-subgraph generating function
- `ons_hte` : the high-temperature expansion

## iii. Table of contents

- A. Partition function and even subgraphs

## iv. References

- B. L. van der Waerden, *Die lange Reichweite der regelmässigen Atomanordnung in Mischkristallen*,
  Z. Physik 118 (1941) 473-488
- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337

-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech

namespace Onsager

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Partition function and even subgraphs -/

/-- The zero-field Ising partition function of `G` with unit couplings at inverse temperature `β`.
-/
noncomputable def ons_Z (β : ℝ) : ℝ := isingZ G β 0

/-- The even-subgraph generating function `∑_F x^|F|` of `G`, over edge sets `F` in which every
vertex has even degree. -/
noncomputable def ons_X (x : ℝ) : ℝ :=
  ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, x ^ F.card

/-- **High-temperature expansion** (van der Waerden 1941). `Z(β) = 2^|V| (cosh β)^|E| X(tanh β)` for
the zero-field Ising model on a finite graph (B. L. van der Waerden, *Die lange Reichweite der
regelmässigen Atomanordnung in Mischkristallen*, 1941). -/
theorem ons_hte (β : ℝ) :
    ons_Z G β
      = (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ G.edgeFinset.card
        * ons_X G (Real.tanh β) := by
  unfold ons_Z ons_X
  exact isingZ_high_temp_expansion G β

end Onsager

end StatMech
