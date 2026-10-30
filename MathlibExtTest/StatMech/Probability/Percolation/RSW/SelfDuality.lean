/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.SelfDuality
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.SelfDuality`

* `selfDualPoint 1 = 1/2` (Bernoulli percolation) and `selfDualPoint 4 = 2/3` (Ising, `q = 2`
  gives `√2 / (1 + √2)`); membership in `(0, 1)`.
* `dualParam_selfDualPoint` and `dualParam_self_iff` at `q = 1`: `1/2` is self-dual, `1/3` is not.
* `dualBC` on the three boundary conditions and its involutivity.
* `crossingPair_incompatible`, `isOpen_iff_not_dualCross_open` and `dualCross_open_iff_closed`
  for the all-open configuration.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.SelfDuality

example : selfDualPoint 1 = 1 / 2 := by norm_num [selfDualPoint]

example : selfDualPoint 4 = 2 / 3 := by
  rw [selfDualPoint, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

example : selfDualPoint 2 ∈ Set.Ioo (0 : ℝ) 1 := selfDualPoint_mem_Ioo (by norm_num)

example : dualParam (1 / 2) 1 (1 / 2) := by
  have h := dualParam_selfDualPoint (q := 1) one_pos
  rwa [show selfDualPoint 1 = 1 / 2 by norm_num [selfDualPoint]] at h

example : ¬ dualParam (1 / 3) 1 (1 / 3) := by
  rw [dualParam_self_iff one_pos (by norm_num) (by norm_num)]
  norm_num [selfDualPoint]

example : dualBC .free = .wired ∧ dualBC .wired = .free ∧ dualBC .periodic = .periodic :=
  ⟨rfl, rfl, rfl⟩

example (bc : BoundaryCondition) : dualBC (dualBC bc) = bc := dualBC_dualBC bc

example (e : Sym2 (Site 2)) : ¬ ((fun _ => true) e = true ∧
    dualConfig (fun _ => true) (crossEdge e) = true) :=
  crossingPair_incompatible (fun _ => true) e

example (e : Sym2 (Site 2)) : dualConfig (fun _ => true) (crossEdge e) = false := by
  have h := (isOpen_iff_not_dualCross_open (fun _ => true) e).mp rfl
  simpa using h

example (e : Sym2 (Site 2)) : dualConfig (fun _ => false) (crossEdge e) = true :=
  (dualCross_open_iff_closed _ e).mpr rfl

end MathlibExtTest.StatMech.Probability.Percolation.RSW.SelfDuality
