/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.RingClassField

#check @PeriodPair.jInvariant
#check @ringClassField
#check @jInvariant_mem_ringClassField

/-- The ring class field contains its base field. -/
example (K : Subfield ℂ) (𝒪 : Subring ℂ) (x : K) : (x : ℂ) ∈ ringClassField K 𝒪 :=
  (ringClassField K 𝒪).algebraMap_mem x
