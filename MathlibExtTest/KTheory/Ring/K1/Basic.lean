/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.KTheory.Ring.K1.Basic

/-! Public use of the canonical K1 coefficient map in independent ring universes. -/

open AlgebraicKTheory

universe u v w

noncomputable section

section

variable {R : Type u} {S : Type v} {T : Type w}
variable [Ring R] [Ring S] [Ring T]

example (f : R →+* S) : K1 R →+ K1 S := K1.mapRingHom f

example (f : R →+* S) (g : StableGL R) :
    K1.mapRingHom f (K1.proj g) = K1.proj (StableGL.scalarMap f g) := by
  simp

example (f : R →+* S) {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) R) :
    K1.mapRingHom f (K1.mk A) = K1.mk (Matrix.GeneralLinearGroup.mapRingHom f A) := by
  simp

example (f : R →+* S) (g : S →+* T) (x : K1 R) :
    K1.mapRingHom (g.comp f) x = K1.mapRingHom g (K1.mapRingHom f x) :=
  congrArg (fun h : K1 R →+ K1 T => h x) (K1.mapRingHom_comp f g)

end

example (R : Type u) [Ring R] (x : K1 R) : K1.mapRingHom (RingHom.id R) x = x := by
  simp

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    K1.mapRingHom f = (K1.functor.map (RingCat.ofHom f)).hom :=
  K1.mapRingHom_eq_functor f

example (f : ℤ →+* ℚ) (A : Matrix.GeneralLinearGroup (Fin 0) ℤ) :
    K1.mapRingHom f (K1.mk A) = K1.mk (Matrix.GeneralLinearGroup.mapRingHom f A) := by
  simp

end
