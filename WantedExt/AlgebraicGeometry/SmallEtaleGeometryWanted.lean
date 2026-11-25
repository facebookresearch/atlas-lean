/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
public import Batteries.Util.ProofWanted

/-!
# Inverse images along small étale base change

`HasInverseImage f` records that étale base change along `f : T ⟶ X` is a continuous functor
of the small étale sites and that the induced direct image of sheaves of commutative monoids
has a left adjoint (the inverse image). `InverseImageTheory` asks for this for every scheme map,
also for the larger coefficient universe used by sheafification on the small étale category.
These are the standard functoriality properties of small étale topoi (SGA 4, Exposé VII;
Stacks Project, the chapter on étale cohomology, functoriality of small étale topoi).
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SmallEtaleGeometry

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleGeometry MathlibExt.AlgebraicGeometry.EtaleLogDiagrams

universe u

/-- Continuity and inverse images for étale base change along one scheme map. -/
instance_wanted hasInverseImage {X T : Scheme.{u}} (f : T ⟶ X) : HasInverseImage f

/-- The same properties for every scheme map, in both coefficient universes. -/
instance_wanted inverseImageTheory : InverseImageTheory.{u}

end WantedExt.AlgebraicGeometry.SmallEtaleGeometry
