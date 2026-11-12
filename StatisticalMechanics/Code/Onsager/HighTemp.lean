/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















import Mathlib
import Code.Ising.KWSelfDuality

open scoped BigOperators
open Finset

namespace StatMech

namespace Onsager

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ons_Z (β : ℝ) : ℝ := isingZ G β 0



noncomputable def ons_X (x : ℝ) : ℝ :=
  ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, x ^ F.card








theorem ons_hte (β : ℝ) :
    ons_Z G β
      = (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ G.edgeFinset.card
        * ons_X G (Real.tanh β) := by
  unfold ons_Z ons_X
  exact isingZ_high_temp_expansion G β

end Onsager

end StatMech
