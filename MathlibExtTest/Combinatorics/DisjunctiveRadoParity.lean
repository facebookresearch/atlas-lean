/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DisjunctiveRadoParity

set_option autoImplicit false

open MathlibExt.Combinatorics.DisjunctiveRadoWanted

example (R : ℕ) : ¬ radoGood 4 5 {3} R :=
  not_radoGood_of_odd 5 4 3 (by decide) (by decide) ⟨4, rfl⟩ ⟨1, rfl⟩ R

example (R : ℕ) : ¬ radoGood 4 5 {-3} R :=
  not_radoGood_of_odd 5 4 (-3) (by decide) (by decide) ⟨4, rfl⟩ ⟨-2, rfl⟩ R
