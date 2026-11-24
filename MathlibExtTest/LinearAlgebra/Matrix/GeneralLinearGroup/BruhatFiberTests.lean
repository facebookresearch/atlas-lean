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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatFiber

@[expose] public section

noncomputable section

set_option autoImplicit false

open Matrix

universe u v

namespace Matrix.GeneralLinearGroup.BruhatFiberTests

open Matrix.GeneralLinearGroup

variable {F : Type u} [Field F] {n : ℕ}
variable {W : Type v} [Group W]
variable (p : W →* MonomialSL F (Fin n))

example : Type (max u v) := BruhatFiber F n p

example (x : BruhatFiber F n p) :
    bruhatMiddle (BruhatFiber.fst x) = p (BruhatFiber.snd x) :=
  BruhatFiber.prop_eq x

example (x : BruhatFiber F n p)
    (a : upperElementarySubgroup (Fin n) F) :
    BruhatFiber.leftUpper a (BruhatFiber.rightUpper a x) =
      BruhatFiber.rightUpper a (BruhatFiber.leftUpper a x) :=
  BruhatFiber.left_right_commute a a x

example (x : BruhatFiber F n p) :
    BruhatFiber.map (BruhatFiber.MapData.id F n p) x = x := by
  simp

example (x : BruhatFiber F n p)
    (a : upperElementarySubgroup (Fin n) F) :
    BruhatFiber.map (BruhatFiber.MapData.id F n p)
        (BruhatFiber.leftUpper a x) =
      BruhatFiber.leftUpper a
        (BruhatFiber.map (BruhatFiber.MapData.id F n p) x) :=
  BruhatFiber.map_leftUpper (BruhatFiber.MapData.id F n p) a a rfl x

example (x : BruhatFiber F n p) :
    BruhatFiber.map
        (BruhatFiber.MapData.comp (BruhatFiber.MapData.id F n p)
          (BruhatFiber.MapData.id F n p)) x =
      BruhatFiber.map (BruhatFiber.MapData.id F n p)
        (BruhatFiber.map (BruhatFiber.MapData.id F n p) x) :=
  BruhatFiber.map_comp _ _ x

example (hp : Function.Surjective p)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    p (BruhatFiber.snd (BruhatFiber.mk hp s)) = bruhatMiddle s :=
  BruhatFiber.mk_point_snd_proj hp s

section IdentityProjection

abbrev IdentityFiber (F : Type u) [Field F] (n : ℕ) :=
  BruhatFiber F n (MonoidHom.id (MonomialSL F (Fin n)))

example (F : Type u) [Field F] (n : ℕ) : IdentityFiber F n :=
  BruhatFiber.basepoint F n (MonoidHom.id _)

example (F : Type u) [Field F] (n : ℕ)
    (m : MonomialSL F (Fin n)) :
    (MonoidHom.id _)
        (BruhatFiber.chooseLift (p := MonoidHom.id _) Function.surjective_id m) = m :=
  BruhatFiber.chooseLift_spec Function.surjective_id m

end IdentityProjection

end Matrix.GeneralLinearGroup.BruhatFiberTests
