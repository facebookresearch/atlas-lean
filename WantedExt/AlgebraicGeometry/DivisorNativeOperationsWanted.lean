/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DivisorNativeOperations

/-!
# Actual divisor tensor and inverse-image realization

The objects, tensor/sections, scheme pullback, all module arrows,
unitors, associator, symmetry and inverse-image unit/tensor maps are
fixed native operations in MathlibExt. Only their line/section landing
proofs and the native symmetric monoidal coherence realization remain.
This request has no parabolic or infinite-root equivalence as an input.

Source: Borne–Vistoli arXiv:1001.0466v2, Definition3.1.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DivisorNativeOperations

open MathlibExt.AlgebraicGeometry.DivisorNativeOperations

/-- Realize the actual generic invertible-module tensor and scheme
inverse image, with every categorical structure map fixed to its
native section-preserving recipe. -/
public def_wanted nativeDivisors : NativeDivisors

end WantedExt.AlgebraicGeometry.DivisorNativeOperations
