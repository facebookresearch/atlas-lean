/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.DataProcessing

@[expose] public section

/-- Boundary check: the Helstrom identity instantiates for a
fair coin against itself: both sides are `1`. -/
example (p : PMF Bool) :
    (∑ a, max (p a).toReal (p a).toReal) =
      (2 + ∑ a, |(p a).toReal - (p a).toReal|) / 2 := by
  have h := helstrom_max_sum p p
  simpa using h
