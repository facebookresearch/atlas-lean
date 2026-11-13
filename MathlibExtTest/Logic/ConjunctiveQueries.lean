/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.ConjunctiveQueries

@[expose] public section

/-- Boundary check: the identity is a homomorphism from any
query to itself, hence every query contains itself. -/
example (Q : CQ) : Contained Q Q :=
  (contained_iff_hom Q Q).mpr ⟨id, by
    constructor
    · simp
    · intro a ha
      simpa using ha⟩
