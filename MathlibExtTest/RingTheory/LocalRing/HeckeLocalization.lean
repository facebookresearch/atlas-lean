/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.HeckeLocalization
public import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.FieldSimp

@[expose] public section

-- Consumer with the original binders (`Type`, not `Type*`).
example {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : HeckeData 𝒪 V k) :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) :=
  HeckeData.finite_and_free_localizedModule hk D

-- Higher-universe consumer.
example {𝒪 : Type 1} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type 2} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type 3} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : HeckeData 𝒪 V k) :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) :=
  HeckeData.finite_and_free_localizedModule hk D
