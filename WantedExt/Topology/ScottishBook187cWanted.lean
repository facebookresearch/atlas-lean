/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace MathlibExt.Topology.ScottishBook187cWanted

/-- The `p`-dimensional cube, as the subtype of `Fin p → ℝ` with
coordinates in `[0,1]`. -/
abbrev Cube (p : ℕ) : Type :=
  ↥(Set.pi Set.univ (fun _ : Fin p => Set.Icc (0 : ℝ) 1))

/--
Scottish Book Problem 187, part (3), is false as stated: Keldysh
constructed an open continuous surjection `I^m → I^n` for `m < n`,
refuting the impossibility claim for an open (interior) continuous
transformation of a `p`-dimensional cube into a `q`-dimensional cube
for `p < q`. Status: solved-negative for part (3) (whole Problem 187
is partially_solved, part (1) remaining separate).
Source: P. Alexandroff, Problem 187 part (3) of the Scottish Book,
typescript pp. 82–83; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted scottishBook187c_refuted :
    ∃ p q : ℕ, p < q ∧ ∃ f : Cube p → Cube q, Continuous f ∧ IsOpenMap f ∧
      Function.Surjective f

end MathlibExt.Topology.ScottishBook187cWanted
