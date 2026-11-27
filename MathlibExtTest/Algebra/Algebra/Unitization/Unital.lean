/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Algebra.Algebra.Unitization.Unital
import Mathlib.Data.ZMod.Basic

/-! Public-API consumers for the algebraic unitization product shear. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExtTest.Unitization.AlgebraicUnital

noncomputable section

universe u v

variable (R : Type u) (A : Type v)
variable [CommRing R] [Ring A] [Algebra R A]

example (x : Unitization R A) :
    Unitization.unitalProdAlgHom R A x =
      (x.fst, x.fst • (1 : A) + x.snd) :=
  Unitization.unitalProdAlgHom_apply R A x

example (x : Unitization R A) :
    Unitization.unitalProdAlgEquiv R A x =
      (x.fst, x.fst • (1 : A) + x.snd) :=
  Unitization.unitalProdAlgEquiv_apply R A x

example (x : Unitization R A) :
    (Unitization.unitalProdAlgEquiv R A x).1 = x.fst :=
  Unitization.unitalProdAlgEquiv_apply_fst R A x

example (x : Unitization R A) :
    (Unitization.unitalProdAlgEquiv R A x).2 =
      x.fst • (1 : A) + x.snd :=
  Unitization.unitalProdAlgEquiv_apply_snd R A x

example (x : R × A) :
    (Unitization.unitalProdAlgEquiv R A).symm x =
      Unitization.inl x.1 +
        Unitization.inr (R := R) (A := A) (x.2 - x.1 • (1 : A)) :=
  Unitization.unitalProdAlgEquiv_symm_apply R A x

example (r : R) :
    Unitization.unitalProdAlgEquiv R A (Unitization.inl r) =
      (r, r • (1 : A)) :=
  Unitization.unitalProdAlgEquiv_inl R A r

example (a : A) :
    Unitization.unitalProdAlgEquiv R A (Unitization.inr a) = (0, a) :=
  Unitization.unitalProdAlgEquiv_inr R A a

example (x y : Unitization R A) :
    Unitization.unitalProdAlgEquiv R A (x * y) =
      Unitization.unitalProdAlgEquiv R A x *
        Unitization.unitalProdAlgEquiv R A y :=
  map_mul (Unitization.unitalProdAlgEquiv R A) x y

example (r : R) :
    Unitization.unitalProdAlgEquiv R A
        (algebraMap R (Unitization R A) r) =
      algebraMap R (R × A) r :=
  (Unitization.unitalProdAlgEquiv R A).commutes r

example (x : Unitization R A) :
    (Unitization.unitalProdAlgEquiv R A).symm
        (Unitization.unitalProdAlgEquiv R A x) = x :=
  (Unitization.unitalProdAlgEquiv R A).symm_apply_apply x

example (x : R × A) :
    Unitization.unitalProdAlgEquiv R A
        ((Unitization.unitalProdAlgEquiv R A).symm x) = x :=
  (Unitization.unitalProdAlgEquiv R A).apply_symm_apply x

example :
    Unitization.unitalProdAlgEquiv (ZMod 1) (ZMod 1)
        (0 : Unitization (ZMod 1) (ZMod 1)) = (0, 0) := by
  rw [Unitization.unitalProdAlgEquiv_apply]
  rfl

#print axioms Unitization.unitalProdAlgHom
#print axioms Unitization.unitalProdAlgHom_apply
#print axioms Unitization.unitalProdAlgEquiv
#print axioms Unitization.unitalProdAlgEquiv_apply
#print axioms Unitization.unitalProdAlgEquiv_apply_fst
#print axioms Unitization.unitalProdAlgEquiv_apply_snd
#print axioms Unitization.unitalProdAlgEquiv_symm_apply
#print axioms Unitization.unitalProdAlgEquiv_inl
#print axioms Unitization.unitalProdAlgEquiv_inr

end

end MathlibExtTest.Unitization.AlgebraicUnital
