/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Defs

namespace MetaMathlibExt

@[expose] public section

/-- **Groups with finitely many automorphism orbits.** A group $G$ has finitely many automorphism
orbits if the action of its automorphism group $\operatorname{Aut}(G)$ on $G$ has only finitely
many orbits. -/
def HasFinitelyManyAutomorphismOrbits (G : Type*) [Group G] : Prop :=
  Finite (MulAction.orbitRel.Quotient (MulAut G) G)

end

end MetaMathlibExt
