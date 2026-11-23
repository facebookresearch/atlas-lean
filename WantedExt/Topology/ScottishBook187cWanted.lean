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

/-- **The p-dimensional cube.** For $p \in \mathbb{N}$, the cube $I^p = [0,1]^p$ is the set of
points of $\mathbb{R}^p$ all of whose coordinates lie in $[0,1]$, with the subspace topology. -/
abbrev Cube (p : ℕ) : Type :=
  ↥(Set.pi Set.univ (fun _ : Fin p => Set.Icc (0 : ℝ) 1))

/--
**Open maps can raise the dimension of a cube.** There are natural numbers $p < q$ and a
continuous, open, surjective map $f \colon I^p \to I^q$, where $I^p = [0,1]^p$ and
$I^q = [0,1]^q$ are the $p$- and $q$-dimensional cubes.

Keldysh constructed such maps, refuting the claim of Scottish Book Problem 187, part (3), that no
open (interior) continuous map of a $p$-dimensional cube onto a $q$-dimensional cube exists for
$p < q$.

Source: P. Alexandroff, Problem 187 part (3) of the Scottish Book,
typescript pp. 82–83; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted scottishBook187c_refuted :
    ∃ p q : ℕ, p < q ∧ ∃ f : Cube p → Cube q, Continuous f ∧ IsOpenMap f ∧
      Function.Surjective f

end MathlibExt.Topology.ScottishBook187cWanted
