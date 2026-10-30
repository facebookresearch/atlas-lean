/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.CharP

@[expose] public section

example (A : Type*) [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    CharP (IsLocalRing.ResidueField A) p :=
  IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal A p hAp
