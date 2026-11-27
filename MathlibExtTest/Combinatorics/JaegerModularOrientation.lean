/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.Combinatorics.JaegerModularOrientation

/-! Regression for the exact statement and the concrete `k = 3` counterexample. -/

open MathlibExt.Combinatorics.JaegerModularOrientationWanted
open HanLiWuZhang

example : ¬ conjecture := conjecture_refuted

example : Fintype.card Vertex = 170 := by decide +kernel

example : IsFourKEdgeConnected 3 endA endB := twelve_connected

example (r : Edge → Bool) : ¬ IsModularOrientation 3 endA endB r := no_modular_orientation r
