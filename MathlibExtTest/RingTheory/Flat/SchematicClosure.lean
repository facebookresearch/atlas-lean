/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Flat.SchematicClosure

@[expose] public section

open scoped TensorProduct

-- Characterization consumer with the original binders: membership unfolds
-- to the defining tensor condition.
example {R F G : Type*} [CommRing R] [Field F] [Algebra R F] [CommRing G]
    [Algebra R G] (B : Subalgebra F (F ⊗[R] G)) (g : G) :
    g ∈ flatClosure B ↔ (1 : F) ⊗ₜ[R] g ∈ B :=
  mem_flatClosure_iff

-- Nontrivial instance: over a field, the closure of the whole algebra is
-- the whole algebra, and the finite/free/flat conclusions apply.
example (B : Subalgebra ℚ (ℚ ⊗[ℚ] ℚ)) : flatClosure B ≤ ⊤ :=
  le_top

example (B : Subalgebra ℚ (ℚ ⊗[ℚ] ℚ)) : Module.Finite ℚ (flatClosure B) :=
  flatClosure_finite B

example (B : Subalgebra ℚ (ℚ ⊗[ℚ] ℚ)) : Module.Free ℚ (flatClosure B) :=
  flatClosure_free B

example (B : Subalgebra ℚ (ℚ ⊗[ℚ] ℚ)) : Module.Flat ℚ (flatClosure B) :=
  flatClosure_flat B

-- Monotonicity consumer.
example {R F G : Type*} [CommRing R] [Field F] [Algebra R F] [CommRing G]
    [Algebra R G] {B B' : Subalgebra F (F ⊗[R] G)} (h : B ≤ B') :
    flatClosure B ≤ flatClosure B' :=
  flatClosure_mono h
