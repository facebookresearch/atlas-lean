/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Languages.SignDomain

@[expose] public section

/-- `3 + 4` has sign `pos`, as the abstract table allows. -/
example : signOf (3 + 4) ∈ addSigns (signOf 3) (signOf 4) :=
  signOf_add_mem 3 4

/-- `(-2) * 5` has sign `neg`, as the abstract table allows. -/
example : signOf (-2 * 5) ∈ mulSigns (signOf (-2)) (signOf 5) :=
  signOf_mul_mem (-2) 5

end
