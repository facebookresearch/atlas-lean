/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Code.Ising.EnsembleGHS
import Code.Ising.TwoCurrentProbBound
import Code.Ising.HdomNativeWeight

open Finset Classical
open scoped symmDiff BigOperators

namespace StatMech.Walls

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]











noncomputable def ghc_ensembleUrsell (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) : ℝ :=
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y



noncomputable def ghc_allConnMass (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) : ℝ :=
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B







theorem ghc_switching (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    {u v : V} (huv : u ≠ v) (hconn : connP (oddEdges G.edgeFinset m) u v) (A : Finset V) :
    hnw_mass G β J m (A ∆ {u, v}) = hnw_mass G β J m A :=
  hnw_switching G β J m huv hconn A








theorem ghc_gap_allConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y) :
    hnw_gap G β J m A o x y = -2 * hnw_mass G β J m A :=
  hnw_gap_allConn G β J m A hox hoy hxy hall













theorem ghc_ensemble_ursell_eq_unfolded (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y
      = -2 * ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hmem => ?_)
  rw [Finset.mem_filter] at hmem
  
  exact ghc_gap_allConn G β J m B hox hoy hxy hmem.2







theorem ghc_ensemble_ursell_eq (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    ghc_ensembleUrsell G β J M B o x y = -2 * ghc_allConnMass G β J M B o x y := by
  unfold ghc_ensembleUrsell ghc_allConnMass
  exact ghc_ensemble_ursell_eq_unfolded G β J M B hox hoy hxy





theorem ghc_ensembleUrsell_eq_egh (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) :
    ghc_ensembleUrsell G β J M B o x y = egh_ensembleUrsell G β J M B o x y :=
  rfl


theorem ghc_allConnMass_eq_tcp (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) :
    ghc_allConnMass G β J M B o x y = tcp_allConnMass G β J M B o x y :=
  rfl

end StatMech.Walls
