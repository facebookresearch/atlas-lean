/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Basic

/-!
# Upstream Physlib smoke tests

Checks that the new libraries expose the pinned upstream `Space` API.

## i. Overview

The examples use the upstream representation, its zero-dimensional boundary,
and its affine and metric instances. No replacement physics API is defined.

## ii. Key results

These are import and elaboration checks, not new mathematical results.

## iii. Table of contents

- A. Upstream API checks

## iv. References

- `Physlib.SpaceAndTime.Space.Basic`

## A. Upstream API checks
-/

example : (⟨fun _ => 7⟩ : Space 3) 0 = 7 := rfl

example (p q : Space 0) : p = q := Subsingleton.elim p q

example (p : Space 3) : (0 : EuclideanSpace ℝ (Fin 3)) +ᵥ p = p :=
  zero_vadd _ _

example (p : Space 3) : dist p p = 0 := dist_self p
