/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_AlgebraicGeometry_IsPullback_surjective_residueFieldMap_of_isIso_residueFieldMap.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.AlgebraicGeometry.PullbackResidueFieldSurjective

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

private theorem exactSource
    {P X T S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (H : IsPullback fst snd f g) (t : ↥P)
    [IsIso (f.residueFieldMap (fst.base t))] :
    Function.Surjective (snd.residueFieldMap t).hom :=
  AlgebraicGeometry.IsPullback.surjective_residueFieldMap_of_isIso_residueFieldMap H t

/-- Boundary: in the vertical identity pullback square, the theorem
recovers surjectivity of an identity residue field map. -/
example {T S : Scheme.{u}} {g : T ⟶ S} (t : ↥T) :
    Function.Surjective (Scheme.Hom.residueFieldMap (𝟙 T) t).hom :=
  AlgebraicGeometry.IsPullback.surjective_residueFieldMap_of_isIso_residueFieldMap
    (IsPullback.id_vert g) t
