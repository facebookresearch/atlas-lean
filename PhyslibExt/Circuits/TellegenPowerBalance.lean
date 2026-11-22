/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic

/-!
# Tellegen power balance

## i. Overview

For finite sets of nodes and branches and any real node-by-branch
matrix `A`, branch voltages derived from node potentials through the
transpose, `v = Aᵀ *ᵥ phi`, and branch currents satisfying current
balance with independently supplied node injections, `A *ᵥ i = j`,
together give equal total branch power and total node power,
`v ⬝ᵥ i = phi ⬝ᵥ j`. The statement places no sign convention on `A`,
so it applies to the head-positive graph incidence and to its
tail-positive electrical negation alike. The underlying identity is
`Matrix.dotProduct_transpose_mulVec`.

## ii. Key results

- `branchPower_eq_nodePower`: Tellegen's theorem in matrix form.

## iii. Table of contents

- A. Power balance

## iv. References

- B. D. H. Tellegen, *A general network theorem, with applications*,
  Philips Research Reports 7 (1952), 259-269.
- L. O. Chua, C. A. Desoer and E. S. Kuh, *Linear and Nonlinear
  Circuits*, McGraw-Hill, 1987: the incidence matrix and Tellegen's
  theorem.

## A. Power balance
-/

@[expose] public section

namespace PhyslibExt.Circuits.TellegenPowerBalance

open Matrix

/-- Tellegen's theorem in matrix form: for any node-by-branch matrix `A`,
the potential definition of branch voltage `v = Aᵀ *ᵥ phi` and node
current balance `A *ᵥ i = j` give equal total branch power and total
node power, `v ⬝ᵥ i = phi ⬝ᵥ j`. -/
theorem branchPower_eq_nodePower {N B : Type*} [Fintype N] [Fintype B]
    (A : Matrix N B ℝ) (phi j : N → ℝ) (v i : B → ℝ)
    (hKVL : v = A.transpose *ᵥ phi) (hKCL : A *ᵥ i = j) :
    v ⬝ᵥ i = phi ⬝ᵥ j := by
  rw [hKVL, dotProduct_comm, Matrix.dotProduct_transpose_mulVec, hKCL]

end PhyslibExt.Circuits.TellegenPowerBalance
