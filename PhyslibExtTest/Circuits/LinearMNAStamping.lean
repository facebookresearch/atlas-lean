/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.LinearMNAStamping
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.LinearMNAStamping

namespace PhyslibExtTest.Circuits.LinearMNAStamping

/-- One branch from node `0` to node `1`: the tail-positive
incidence entry is `1` at the tail node and `-1` at the head
node, through the public sign adapter. -/
example :
    physicalIncidence (fun _ : Fin 1 => (0 : Fin 2))
        (fun _ : Fin 1 => (1 : Fin 2)) 0 0 = 1 ∧
      physicalIncidence (fun _ : Fin 1 => (0 : Fin 2))
        (fun _ : Fin 1 => (1 : Fin 2)) 1 0 = -1 := by
  constructor <;>
    simp [physicalIncidence,
      MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix]

/-- The same single branch under `physicalIncidence_mulVec_apply`:
with unit branch current the nodal current is `1` at the tail
node and `-1` at the head node. -/
example :
    Matrix.mulVec (physicalIncidence (fun _ : Fin 1 => (0 : Fin 2))
        (fun _ : Fin 1 => (1 : Fin 2))) (fun _ : Fin 1 => (1 : ℝ)) 0 = 1 ∧
      Matrix.mulVec (physicalIncidence (fun _ : Fin 1 => (0 : Fin 2))
        (fun _ : Fin 1 => (1 : Fin 2))) (fun _ : Fin 1 => (1 : ℝ)) 1 = -1 := by
  constructor <;> rw [physicalIncidence_mulVec_apply] <;> simp

/-- A single capacitor branch on a single node with unit
incidence stamps to nodal capacitance `3` at capacitance value
`3`, through the public computation. -/
example :
    nodalCapacitance (1 : Matrix (Fin 1) (Fin 1) ℝ) {0}
        (fun _ => 3) = !![(3 : ℝ)] :=
  nodalCapacitance_singleCapacitor

/-- The same single-capacitor assembly at value `0` stamps to
`0`: the assembled matrix is not constant in the value. -/
example :
    nodalCapacitance (1 : Matrix (Fin 1) (Fin 1) ℝ) {0}
        (fun _ => 0) = !![(0 : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [nodalCapacitance]

end PhyslibExtTest.Circuits.LinearMNAStamping
