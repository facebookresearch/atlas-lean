/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusSparseGreenDecay

open Filter Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Lattice



theorem isingDyadicTorusGreen_cauchySeq
    {d : Nat} (hd : 2 < d) (x : Site d) :
    CauchySeq (fun k => isingDyadicTorusGreen x k) := by
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  obtain ⟨eta, heta, hclose⟩ :=
    isingDyadicTorusGreen_eventually_close_continuum
      hd (epsilon / 2) (half_pos hepsilon)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hclose x)
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [Real.dist_eq]
  calc
    |isingDyadicTorusGreen x m - isingDyadicTorusGreen x n| <=
        |isingDyadicTorusGreen x m -
            isingRegularizedContinuumGreen eta x| +
          |isingDyadicTorusGreen x n -
            isingRegularizedContinuumGreen eta x| := by
      calc
        |isingDyadicTorusGreen x m - isingDyadicTorusGreen x n| <=
            |isingDyadicTorusGreen x m -
                isingRegularizedContinuumGreen eta x| +
              |isingRegularizedContinuumGreen eta x -
                isingDyadicTorusGreen x n| := abs_sub_le _ _ _
        _ = _ := by rw [abs_sub_comm
          (isingRegularizedContinuumGreen eta x)
          (isingDyadicTorusGreen x n)]
    _ < epsilon / 2 + epsilon / 2 := add_lt_add (hN m hm) (hN n hn)
    _ = epsilon := by ring



noncomputable def isingLatticeGreen (d : Nat) (x : Site d) : Real :=
  limUnder atTop (fun k => isingDyadicTorusGreen x k)

theorem isingDyadicTorusGreen_tendsto_latticeGreen
    {d : Nat} (hd : 2 < d) (x : Site d) :
    Tendsto (fun k => isingDyadicTorusGreen x k) atTop
      (nhds (isingLatticeGreen d x)) := by
  exact (isingDyadicTorusGreen_cauchySeq hd x).tendsto_limUnder



noncomputable def isingDyadicGreenAxisBlockAverage
    {d : Nat} (i : Fin d) (r k : Nat) : Real :=
  (1 / ((r + 1 : Nat) : Real) ^ 2) *
    ∑ a ∈ Finset.range (r + 1),
      ∑ b ∈ Finset.range (r + 1),
        isingDyadicTorusGreen
          (Pi.single i ((b : Int) - (a : Int))) k



noncomputable def isingLatticeGreenAxisBlockAverage
    {d : Nat} (i : Fin d) (r : Nat) : Real :=
  (1 / ((r + 1 : Nat) : Real) ^ 2) *
    ∑ a ∈ Finset.range (r + 1),
      ∑ b ∈ Finset.range (r + 1),
        isingLatticeGreen d (Pi.single i ((b : Int) - (a : Int)))



theorem isingDyadicGreenAxisBlockAverage_tendsto_latticeGreen
    {d : Nat} (hd : 2 < d) (i : Fin d) (r : Nat) :
    Tendsto (isingDyadicGreenAxisBlockAverage i r)
      atTop (nhds (isingLatticeGreenAxisBlockAverage i r)) := by
  have hsum : Tendsto
      (fun k => ∑ a ∈ Finset.range (r + 1),
        ∑ b ∈ Finset.range (r + 1),
          isingDyadicTorusGreen
            (Pi.single i ((b : Int) - (a : Int))) k)
      atTop
      (nhds (∑ a ∈ Finset.range (r + 1),
        ∑ b ∈ Finset.range (r + 1),
          isingLatticeGreen d
            (Pi.single i ((b : Int) - (a : Int))))) := by
    exact tendsto_finsetSum (Finset.range (r + 1)) fun a _ =>
      tendsto_finsetSum (Finset.range (r + 1)) fun b _ =>
        isingDyadicTorusGreen_tendsto_latticeGreen hd
          (Pi.single i ((b : Int) - (a : Int)))
  change Tendsto
    (fun k => (1 / ((r + 1 : Nat) : Real) ^ 2) *
      ∑ a ∈ Finset.range (r + 1),
        ∑ b ∈ Finset.range (r + 1),
          isingDyadicTorusGreen
            (Pi.single i ((b : Int) - (a : Int))) k)
    atTop
    (nhds ((1 / ((r + 1 : Nat) : Real) ^ 2) *
      ∑ a ∈ Finset.range (r + 1),
        ∑ b ∈ Finset.range (r + 1),
          isingLatticeGreen d
            (Pi.single i ((b : Int) - (a : Int)))))
  exact hsum.const_mul (1 / ((r + 1 : Nat) : Real) ^ 2)

end StatMech.FrontierA
