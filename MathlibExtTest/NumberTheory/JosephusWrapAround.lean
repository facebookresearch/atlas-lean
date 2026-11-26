/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusWrapAround

open MetaMathlibExt MathlibExt.NumberTheory.JosephusWanted

-- No wrap: the upper endpoint still gives the last position, not zero.
example : josephus 2 3 = 3 :=
  (josephus_succ_eq_sub 2 2 0 (by decide) (by decide) (by decide)).trans (by decide)

-- One wrap: the lower endpoint gives the first position.
example : josephus 2 2 = 1 :=
  (josephus_succ_eq_sub 2 1 1 (by decide) (by decide) (by decide)).trans (by decide)

-- Three wraps: a strict interior value gives the second position.
example : josephus 9 3 = 2 :=
  (josephus_succ_eq_sub 9 2 3 (by decide) (by decide) (by decide)).trans (by decide)
