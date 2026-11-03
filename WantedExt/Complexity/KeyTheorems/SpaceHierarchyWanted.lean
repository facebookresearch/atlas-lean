/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Deterministic space hierarchy

Source:
R. W. Stearns, J. Hartmanis, and P. M. Lewis II, "Hierarchies of memory limited computations",
Proceedings of the Sixth Annual Symposium on Switching Circuit Theory and Logical Design
(1965), 179-190.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.SpaceHierarchy

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Deterministic space hierarchy

There is a language decidable in deterministic quadratic space that is not decidable in
deterministic linear space, on the CSLib multi-tape model (`DSPACE`).
-/

/-- **Deterministic space hierarchy: quadratic versus linear space.** There is a language $L$
of bitstrings that lies in $\mathrm{DSPACE}(n^2)$ but not in $\mathrm{DSPACE}(n)$, the
deterministic space classes of multi-tape Turing machines for the space bounds $n \mapsto n^2$
and $n \mapsto n$.

Source: R. W. Stearns, J. Hartmanis, and P. M. Lewis
II, "Hierarchies of memory limited computations", Proceedings of the Sixth Annual
Symposium on Switching Circuit Theory and Logical Design (1965), 179-190. -/
public theorem_wanted space_hierarchy :
    ∃ L : Set (List Bool), L ∈ Cslib.Turing.MultiTapeTM.DSPACE (fun n => n ^ 2) ∧
      L ∉ Cslib.Turing.MultiTapeTM.DSPACE (fun n => n)

end MetaMathlibExt.Complexity.KeyTheorems.SpaceHierarchy
