/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.BitBlast

@[expose] public section

/-- AND at a concrete bit reads the two input bits. -/
example (a b : BV 4) (i : Fin 4) : bvAnd a b i = (a i && b i) :=
  bvAnd_apply a b i

/-- De Morgan at width 2. -/
example (a b : BV 2) : bvNot (bvAnd a b) = bvOr (bvNot a) (bvNot b) :=
  bvNot_and a b

end
