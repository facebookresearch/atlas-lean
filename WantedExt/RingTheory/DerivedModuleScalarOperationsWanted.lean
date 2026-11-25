/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.DerivedModuleScalarOperations
public import Batteries.Util.ProofWanted

/-!
# Derived scalar extension and derived tensor product of modules

Every complex of modules over a commutative ring has a K-flat (indeed K-projective) resolution
(Spaltenstein; Stacks Project, Tag 06Y4), and tensoring with a K-flat complex preserves
quasi-isomorphisms (Tag 06Y0), so the degreewise scalar extension along a ring map and the
total tensor product of complexes have left derived functors. These requests
provide the classes `HasExtension` and `HasTensor` of `DerivedModuleScalarOperations`.
-/

@[expose] public noncomputable section

namespace WantedExt.RingTheory.DerivedModuleScalarOperations

open MathlibExt.RingTheory.DerivedModuleScalarOperations

universe u

/-- Derived scalar extension along every ring map exists. -/
public instance_wanted hasExtension {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    HasExtension f

/-- The derived tensor product of module complexes exists. -/
public instance_wanted hasTensor (A : Type u) [CommRing A] : HasTensor A

end WantedExt.RingTheory.DerivedModuleScalarOperations
