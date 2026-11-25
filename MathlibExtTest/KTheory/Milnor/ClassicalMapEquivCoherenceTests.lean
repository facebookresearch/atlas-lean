/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.ClassicalMap

/-!
# Tests for classical Milnor map-equivalence coherence
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v w

namespace MilnorK

variable {F : Type u} {K : Type v} {L : Type w}
variable [Field F] [Field K] [Field L]

example (e : F ≃+* K) (n : ℕ) :
    (mapEquiv e n).toLinearMap = map e.toRingHom n :=
  mapEquiv_toLinearMap e n

example (F : Type u) [Field F] (n : ℕ) :
    mapEquiv (RingEquiv.refl F) n = LinearEquiv.refl ℤ (MilnorK F n) := by
  simp

example (e : F ≃+* K) (e' : K ≃+* L) (n : ℕ) :
    mapEquiv (e.trans e') n = (mapEquiv e n).trans (mapEquiv e' n) :=
  mapEquiv_comp e e' n

example (e : F ≃+* K) (n : ℕ) :
    (mapEquiv e n).symm = mapEquiv e.symm n := by
  simp

example (e : F ≃+* K) (n : ℕ) (x : TensorRing.degree F n) :
    mapEquiv e n (mk F n x) =
      mk K n (MilnorKRing.tensorMapDegree e.toRingHom n x) := by
  simp

end MilnorK
