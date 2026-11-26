/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.PlaceCongr

/-! # Tests for the transport of places along field isomorphisms -/

@[expose] public section

namespace AlgebraicCurve.Place

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)

-- A `K`-isomorphism of fields transports places, preserving orders and degrees.
example (v : Place K F) (f : F) : (congrRingEquiv e he v).ord (e f) = v.ord f :=
  ord_congrRingEquiv e he v f

example (v : Place K F) : (congrRingEquiv e he v).deg = v.deg := deg_congrRingEquiv e he v

example (v : Place K F) : (congrEquiv e he).symm (congrEquiv e he v) = v :=
  (congrEquiv e he).symm_apply_apply v

-- Boundary: the identity isomorphism fixes every place.
example (v : Place K F) : congrRingEquiv (RingEquiv.refl F) (fun _ => rfl) v = v :=
  Place.ext rfl

end AlgebraicCurve.Place
