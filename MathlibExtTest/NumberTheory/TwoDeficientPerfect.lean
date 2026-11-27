/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OddPrimeDeficientPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

example : IsKLDeficientPerfect 0 1 2 := isKLDeficientPerfect_two (k := 0)

example : IsKLDeficientPerfect 1 1 2 := isKLDeficientPerfect_two (k := 1)

example : IsKLDeficientPerfect 2 1 2 := isKLDeficientPerfect_two (k := 2)
