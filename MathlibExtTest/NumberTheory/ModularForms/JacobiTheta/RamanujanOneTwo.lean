/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanOneTwo
import Mathlib.Tactic.NormNum

open MetaMathlibExt MetaMathlibExt.QPochhammer

-- The origin is included in the open disk.
example : ramanujanThetaRaw (0 : ℂ) 0 * qPochhammerInfRaw 0 0 = ramanujanThetaRaw 0 0 := by
  simpa using ramanujanTheta_one_two (q := 0) (hq := by simp)

-- A nonreal point in the domain, using the named norm hypothesis.
example :
    ramanujanThetaRaw (Complex.I / 2) ((Complex.I / 2) ^ 2) *
        qPochhammerInfRaw (Complex.I / 2) ((Complex.I / 2) ^ 2) =
      ramanujanThetaRaw (-(Complex.I / 2) ^ 3) (-(Complex.I / 2) ^ 3) :=
  ramanujanTheta_one_two (hq := by norm_num [norm_div])

#print axioms MetaMathlibExt.ramanujanTheta_one_two
