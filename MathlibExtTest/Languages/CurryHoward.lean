/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Languages.CurryHoward

@[expose] public section

/-- The identity term at type `A` yields the identity proof. -/
example (A : Ty) : ND [A] A :=
  curry_howard (HasType.var 0 (by simp))

/-- A hypothesis used under an implication introduction. -/
example (A B : Ty) : ND [] (Ty.imp A A) :=
  curry_howard (HasType.lam (HasType.var 0 (by simp)))

end
