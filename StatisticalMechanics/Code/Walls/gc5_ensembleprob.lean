/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Ising.TwoCurrentProbBound
import Code.Ising.CrossClassHdom
import Code.Ising.EnsembleGHS

open Finset BigOperators SimpleGraph Set
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]











theorem gc5_partitionFunction_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) :
    0 ≤ tcp_partitionFunction G β J M B :=
  tcp_partitionFunction_nonneg G β J hβ hJ M B




theorem gc5_allConnMass_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    0 ≤ tcp_allConnMass G β J M B o x y :=
  tcp_allConnMass_nonneg G β J hβ hJ M B o x y






















theorem gc5_allConnMass_le_partitionFunction (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B :=
  tcp_allConnMass_le_partitionFunction G β J hβ hJ M B o x y












theorem gc5_ensemble_domination (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    2 * tcp_allConnMass G β J M B o x y
      ≤ tcp_partitionFunction G β J M B + tcp_allConnMass G β J M B o x y :=
  cch_crossClass_full_dom G β J hβ hJ M B o x y











theorem gc5_allConnProb_eq (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Ising.Current V)) (B : Finset V)
    (o x y : V) :
    tcp_allConnProb G β J M B o x y
      = tcp_allConnMass G β J M B o x y / tcp_partitionFunction G β J M B :=
  rfl




theorem gc5_allConnProb_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    0 ≤ tcp_allConnProb G β J M B o x y :=
  tcp_allConn_prob_nonneg G β J hβ hJ M B o x y






theorem gc5_allConnProb_le_one (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ≤ 1 :=
  tcp_allConn_prob_le_one G β J hβ hJ M B o x y











theorem gc5_allConnProb_mem_Icc (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨gc5_allConnProb_nonneg G β J hβ hJ M B o x y,
   gc5_allConnProb_le_one G β J hβ hJ M B o x y⟩
















theorem gc5_lebowitz_closes_U4 (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) (μ : ℝ) (hμ : 0 ≤ μ) :
    -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y
      ∧ -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 :=
  cch_lebowitz_closes_U4 G β J hβ hJ M B o x y μ hμ












theorem gc5_u3_nonpos (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) (μ : ℝ) (hμ : 0 ≤ μ) :
    -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 :=
  egh_u3_nonpos G β J hβ hJ M B o x y μ hμ

end StatMech.Walls
