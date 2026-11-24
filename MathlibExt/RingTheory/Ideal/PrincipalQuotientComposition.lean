/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Kernels of composite principal quotient maps

These facts retain the actual scheme maps, unreduced intersections and original coefficients.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace RingHom

universe u

/-- Two actual surjective principal quotients have the span of both original equations as composite kernel. -/
theorem ker_comp_eq_span_pair {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : Function.Surjective f)
    (a b : A) (ha : RingHom.ker f = Ideal.span {a}) (hb : RingHom.ker g = Ideal.span {f b}) :
    RingHom.ker (g.comp f) = Ideal.span {a, b} := by
  rw [← RingHom.comap_ker, hb]
  have hmap : Ideal.span {f b} = (Ideal.span {b}).map f := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hmap, Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot, ha]
  rw [← Ideal.span_union]
  congr 1
  exact Set.pair_comm b a

end RingHom
