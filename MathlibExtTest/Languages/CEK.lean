/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Languages.CEK

@[expose] public section

/-- Evaluating an application enters the function part. -/
example (t u : Tm) (e : List Clos) (k : Kont) :
    Step (State.eval (Tm.app t u) e k) (State.eval t e (Kont.arg u e k)) :=
  Step.app

/-- A lambda evaluates to its closure. -/
example (t : Tm) (e : List Clos) (k : Kont) :
    Step (State.eval (Tm.lam t) e k) (State.ret (Clos.clos t e) k) :=
  Step.lam

end
