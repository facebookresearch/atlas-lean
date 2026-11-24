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

public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatFiber
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatFiber

@[expose] public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup MatsumotoMonomialExtension

universe u v

namespace MatsumotoBruhatFiber

variable {F : Type u} [Field F] {K : Type v} [Field K] {n : ℕ}

example : X F n =
    Matrix.GeneralLinearGroup.BruhatFiber F n (projHom F n) := rfl

example (x : X F n) (u : upperElementarySubgroup (Fin n) F) :
    leftUpper u (rightUpper u x) = rightUpper u (leftUpper u x) :=
  left_right_commute u u x

example (f : F →+* K) (x : X F n) :
    XMap f (central (1 : Multiplicative (MilnorK F 2)) x) =
      central (MilnorK.mapMultiplicative f 2 1) (XMap f x) :=
  XMap_central_naturality f 1 x

example (x : X F n) : XMap (RingHom.id F) x = x :=
  XMap_id x

example (s : Matrix.SpecialLinearGroup (Fin n) F) :
    projHom F n (X.snd (mkX s)) = bruhatMiddle s :=
  mkX_snd_proj s

end MatsumotoBruhatFiber
