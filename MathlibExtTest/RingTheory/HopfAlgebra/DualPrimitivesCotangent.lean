/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.DualPrimitivesCotangent

@[expose] public section

universe u v

/-- The source statement, with its original binders, restated on the dual
module and the cotangent space at the counit. -/
private theorem exactSource (k : Type u) [Field k] (A : Type v) [CommRing A]
    [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] :
    Module.finrank k ↥(dualPrimitives k A)
      = Module.finrank k (cotangentSpaceAtCounit k A) :=
  finrank_dualPrimitives_eq_finrank_cotangentSpaceAtCounit k A

/-- A higher-universe consumer of the source statement. -/
private theorem exactSourceUniverse (k : Type u) [Field k] (A : Type (v + 1)) [CommRing A]
    [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] :
    Module.finrank k ↥(dualPrimitives k A)
      = Module.finrank k (cotangentSpaceAtCounit k A) :=
  finrank_dualPrimitives_eq_finrank_cotangentSpaceAtCounit k A

example (k : Type u) [Field k] :
    Module.finrank k ↥(dualPrimitives k k) = Module.finrank k (cotangentSpaceAtCounit k k) :=
  finrank_dualPrimitives_eq_finrank_cotangentSpaceAtCounit k k

example {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]
    {φ : Module.Dual k A} (hφ : φ ∈ dualPrimitives k A) (a : A) :
    φ (a * 1) = φ a * Coalgebra.counit (R := k) (1 : A)
      + Coalgebra.counit (R := k) a * φ 1 :=
  (mem_dualPrimitives_iff).1 hφ a 1
