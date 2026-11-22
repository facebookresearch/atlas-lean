/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.ElevenPid

@[expose] public section

open scoped NumberField

-- `exactSource` consumer with the original binders.
example (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K] :
    IsPrincipalIdealRing (𝓞 K) :=
  IsCyclotomicExtension.Rat.eleven_pid K

-- Higher-universe consumer.
example (K : Type 1) [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K] :
    IsPrincipalIdealRing (𝓞 K) :=
  IsCyclotomicExtension.Rat.eleven_pid K

-- Boundary: the analogous statement for 3 is already available, and the
-- eleventh case is a distinct instance of the same PID conclusion.
example (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    IsPrincipalIdealRing (𝓞 K) :=
  IsCyclotomicExtension.Rat.three_pid K
