/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Ising.TwoCurrentProbBound

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Walls

open StatMech.Ising
open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
























theorem ghc_allConnMass_le_partitionFunction (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B :=
  tcp_allConnMass_le_partitionFunction G β J hβ hJ M B o x y







theorem ghc_allConnProb_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    0 ≤ tcp_allConnProb G β J M B o x y :=
  tcp_allConn_prob_nonneg G β J hβ hJ M B o x y






theorem ghc_allConnProb_le_one (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ≤ 1 :=
  tcp_allConn_prob_le_one G β J hβ hJ M B o x y










theorem ghc_allConnProb_mem_unitInterval (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    0 ≤ tcp_allConnProb G β J M B o x y ∧ tcp_allConnProb G β J M B o x y ≤ 1 :=
  ⟨ghc_allConnProb_nonneg G β J hβ hJ M B o x y,
    ghc_allConnProb_le_one G β J hβ hJ M B o x y⟩




theorem ghc_allConnProb_mem_Icc (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ghc_allConnProb_nonneg G β J hβ hJ M B o x y,
    ghc_allConnProb_le_one G β J hβ hJ M B o x y⟩

end Walls

end StatMech
