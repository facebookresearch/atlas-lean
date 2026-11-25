/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Adaptive.ScalarEnergy

open ControlTheory

-- Concrete instance at `t = 0`: plant `x = 1 + 2s`, reference
-- `xm = 3 - s`, estimate `ahat = 4 - 5s`, with `a = 5`, `b = 1`,
-- `lam = 1`, `gamma = 5 / 2`, `r = 2`. The energy derivative is
-- `-lam * (x 0 - xm 0) ^ 2 = -4`.
example :
    HasDerivAt
      (fun s : ℝ => (((1 + 2 * s) - (3 - s)) ^ 2
        + ((5 : ℝ) - (4 - 5 * s)) ^ 2 / (5 / 2)) / 2) (-4) 0 := by
  have dx : HasDerivAt (fun s : ℝ => 1 + 2 * s) 2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).const_add (1 : ℝ)
  have dxm : HasDerivAt (fun s : ℝ => 3 - s) (-1) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_sub (3 : ℝ)
  have dahat : HasDerivAt (fun s : ℝ => 4 - 5 * s) (-5) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul (5 : ℝ)).const_sub (4 : ℝ)
  have hx : HasDerivAt (fun s : ℝ => 1 + 2 * s)
      ((5 : ℝ) * (1 + 2 * 0)
        + (1 : ℝ) * ((- (4 - 5 * 0) * (1 + 2 * 0) - (1 : ℝ) * (1 + 2 * 0) + 2) / 1)) 0 := by
    convert dx using 1
    norm_num
  have hxm : HasDerivAt (fun s : ℝ => 3 - s) (-(1 : ℝ) * (3 - 0) + 2) 0 := by
    convert dxm using 1
    norm_num
  have hahat : HasDerivAt (fun s : ℝ => 4 - 5 * s)
      ((5 / 2 : ℝ) * ((1 + 2 * 0) - (3 - 0)) * (1 + 2 * 0)) 0 := by
    convert dahat using 1
    norm_num
  have h := scalarMRACEnergy_hasDerivAt
    (a := 5) (b := 1) (lam := 1) (gamma := 5 / 2) (r := 2)
    (x := fun s => 1 + 2 * s) (xm := fun s => 3 - s) (ahat := fun s => 4 - 5 * s)
    (t := 0) one_ne_zero (by norm_num) hx hxm hahat
  convert h using 1
  norm_num

-- Wrong-sign adaptation (`ahat = 4 + 5s`): the adaptation law
-- fails at `t = 0`, the actual energy derivative is `-8`, and
-- the identity's conclusion `-4` does not hold.
example :
    ¬ HasDerivAt (fun s : ℝ => 4 + 5 * s)
      ((5 / 2 : ℝ) * ((1 + 2 * 0) - (3 - 0)) * (1 + 2 * 0)) 0 := by
  have dahat : HasDerivAt (fun s : ℝ => 4 + 5 * s) 5 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul (5 : ℝ)).const_add (4 : ℝ)
  intro h
  have huniq := h.unique dahat
  norm_num at huniq

example :
    ¬ HasDerivAt
      (fun s : ℝ => (((1 + 2 * s) - (3 - s)) ^ 2
        + ((5 : ℝ) - (4 + 5 * s)) ^ 2 / (5 / 2)) / 2)
      (-(1 : ℝ) * ((1 + 2 * 0) - (3 - 0)) ^ 2) 0 := by
  have dx : HasDerivAt (fun s : ℝ => 1 + 2 * s) 2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).const_add (1 : ℝ)
  have dxm : HasDerivAt (fun s : ℝ => 3 - s) (-1) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_sub (3 : ℝ)
  have dahat : HasDerivAt (fun s : ℝ => 4 + 5 * s) 5 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul (5 : ℝ)).const_add (4 : ℝ)
  have h1 : HasDerivAt (fun s : ℝ => (1 + 2 * s) - (3 - s)) 3 0 := by
    convert dx.fun_sub dxm using 1
    norm_num
  have h2 : HasDerivAt (fun s : ℝ => (5 : ℝ) - (4 + 5 * s)) (-5) 0 := by
    convert dahat.const_sub (5 : ℝ) using 1
  have hdirect : HasDerivAt
      (fun s : ℝ => (((1 + 2 * s) - (3 - s)) ^ 2
        + ((5 : ℝ) - (4 + 5 * s)) ^ 2 / (5 / 2)) / 2) (-8) 0 := by
    have h := ((h1.fun_pow 2).fun_add ((h2.fun_pow 2).div_const (5 / 2 : ℝ))).div_const 2
    convert h using 1
    norm_num
  intro h
  have huniq := h.unique hdirect
  norm_num at huniq

#print axioms scalarMRACEnergy_hasDerivAt
