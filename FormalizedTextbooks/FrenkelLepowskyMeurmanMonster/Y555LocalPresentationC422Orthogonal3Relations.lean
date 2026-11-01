/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal bounded matrix certificates for original spider10 and the scalar Q cubic. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3Data

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The exact original source letters of this finite product. -/
def y422Orthogonal3SpiderLetters : Fin 9 → Fin 9 :=
  ![0, 1, 2, 0, 5, 6, 0, 7, 8]

/-- Exact successive prefix products, with all literal matrix entries. -/
def y422Orthogonal3SpiderPrefixes : Fin 10 → Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![
    ![
        ![1, 0, 0, 0, 0, 0, 0, 0],
        ![0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![2, 1, 0, 0, 0, 1, 0, 1],
        ![0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![0, 2, 1, 0, 0, 1, 0, 1],
        ![1, 2, 1, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![0, 0, 2, 1, 0, 1, 0, 1],
        ![1, 0, 2, 1, 0, 0, 0, 0],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![0, 0, 2, 1, 0, 1, 0, 1],
        ![2, 1, 2, 1, 0, 1, 0, 1],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![1, 0, 2, 1, 0, 2, 1, 1],
        ![0, 1, 2, 1, 0, 2, 1, 1],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 0, 0, 0, 0, 2, 1, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![1, 0, 2, 1, 0, 0, 2, 1],
        ![0, 1, 2, 1, 0, 0, 2, 1],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 0, 0, 0, 0, 0, 2, 0],
        ![0, 0, 0, 0, 0, 1, 2, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![2, 1, 2, 1, 0, 1, 2, 2],
        ![0, 1, 2, 1, 0, 0, 2, 1],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![2, 1, 0, 0, 0, 1, 2, 1],
        ![0, 0, 0, 0, 0, 1, 2, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![1, 1, 2, 1, 0, 1, 2, 1],
        ![1, 1, 2, 1, 0, 0, 2, 2],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 1, 0, 0, 0, 1, 2, 2],
        ![0, 0, 0, 0, 0, 1, 2, 0],
        ![1, 0, 0, 0, 0, 0, 0, 2]],
    ![
        ![1, 1, 2, 1, 0, 1, 2, 0],
        ![1, 1, 2, 1, 0, 0, 2, 0],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 1, 0, 0, 0, 1, 2, 2],
        ![0, 0, 0, 0, 0, 1, 2, 1],
        ![1, 0, 0, 0, 0, 0, 0, 1]]]

/-- Exact successive powers of the already certified original source prefix. -/
def y422Orthogonal3SpiderPowers : Fin 11 → Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![
    ![
        ![1, 0, 0, 0, 0, 0, 0, 0],
        ![0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![1, 1, 2, 1, 0, 1, 2, 0],
        ![1, 1, 2, 1, 0, 0, 2, 0],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 1, 0, 0, 0, 1, 2, 2],
        ![0, 0, 0, 0, 0, 1, 2, 1],
        ![1, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![2, 2, 2, 2, 0, 1, 1, 1],
        ![2, 1, 2, 2, 0, 0, 2, 2],
        ![1, 0, 0, 1, 0, 0, 2, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 2, 2, 1, 0, 0, 2, 0],
        ![1, 1, 0, 0, 0, 0, 0, 2],
        ![2, 1, 2, 1, 0, 1, 2, 1]],
    ![
        ![2, 1, 0, 2, 0, 1, 0, 1],
        ![2, 2, 1, 1, 0, 1, 1, 1],
        ![1, 1, 2, 2, 0, 0, 0, 2],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![2, 1, 2, 2, 0, 2, 2, 2],
        ![1, 2, 1, 2, 0, 1, 1, 2],
        ![1, 0, 1, 0, 0, 2, 0, 2]],
    ![
        ![1, 1, 0, 2, 0, 0, 2, 0],
        ![2, 0, 1, 0, 0, 1, 0, 1],
        ![1, 1, 2, 0, 0, 1, 1, 2],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![2, 1, 1, 1, 0, 0, 2, 2],
        ![2, 2, 2, 0, 0, 0, 1, 2],
        ![0, 1, 1, 2, 0, 0, 0, 0]],
    ![
        ![2, 2, 1, 1, 0, 0, 2, 2],
        ![0, 1, 0, 0, 0, 0, 0, 0],
        ![1, 2, 2, 1, 0, 0, 2, 2],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![2, 1, 2, 2, 0, 1, 1, 1],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![1, 2, 1, 1, 0, 0, 2, 0]],
    ![
        ![0, 2, 1, 0, 0, 1, 0, 1],
        ![1, 1, 2, 1, 0, 0, 2, 0],
        ![2, 2, 1, 0, 0, 0, 1, 1],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 0, 1, 1, 0, 1, 1, 1],
        ![0, 0, 0, 0, 0, 1, 2, 1],
        ![0, 1, 2, 2, 0, 0, 1, 2]],
    ![
        ![0, 1, 0, 0, 0, 1, 0, 0],
        ![2, 1, 2, 2, 0, 0, 2, 2],
        ![2, 2, 1, 2, 0, 0, 1, 2],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![2, 0, 1, 0, 0, 0, 0, 1],
        ![1, 1, 0, 0, 0, 0, 0, 2],
        ![0, 0, 0, 2, 0, 1, 1, 0]],
    ![
        ![1, 2, 2, 1, 0, 1, 1, 2],
        ![2, 2, 1, 1, 0, 1, 1, 1],
        ![0, 2, 1, 1, 0, 0, 1, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 2, 1, 1],
        ![1, 2, 1, 2, 0, 1, 1, 2],
        ![0, 1, 0, 2, 0, 2, 1, 0]],
    ![
        ![2, 0, 1, 0, 0, 0, 1, 2],
        ![2, 0, 1, 0, 0, 1, 0, 1],
        ![2, 0, 0, 1, 0, 1, 0, 1],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 2, 0, 0, 0, 0, 0, 0],
        ![2, 2, 2, 0, 0, 0, 1, 2],
        ![1, 0, 2, 0, 0, 0, 2, 2]],
    ![
        ![1, 0, 0, 0, 0, 0, 0, 0],
        ![0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]]]

/-- The prefix chain starts at the actual identity. -/
theorem y422Orthogonal3Spider_prefix_start :
    y422Orthogonal3SpiderPrefixes 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Bounded finite matrix products are reduced in the kernel, using their exact source entries.
/-- Each bounded prefix step is its actual predecessor times its exact source reflection. -/
theorem y422Orthogonal3Spider_prefix_step (i : Fin 9) :
    y422Orthogonal3SpiderPrefixes i.succ = y422Orthogonal3SpiderPrefixes i.castSucc *
      y422Orthogonal3Reflection (y422Orthogonal3SpiderLetters i) := by
  revert i
  decide +kernel

/-- The final prefix is the exact original source product. -/
theorem y422Orthogonal3Spider_prefix_value : y422Orthogonal3SpiderPrefixes 9 =
    y422Orthogonal3Reflection 0 * y422Orthogonal3Reflection 1 *
      y422Orthogonal3Reflection 2 * y422Orthogonal3Reflection 0 *
      y422Orthogonal3Reflection 5 * y422Orthogonal3Reflection 6 *
      y422Orthogonal3Reflection 0 * y422Orthogonal3Reflection 7 *
      y422Orthogonal3Reflection 8 := by
  have h0 : y422Orthogonal3SpiderPrefixes 1 = y422Orthogonal3SpiderPrefixes 0 *
      y422Orthogonal3Reflection 0 := by
    convert (y422Orthogonal3Spider_prefix_step ⟨0, by decide⟩) using 1 <;> rfl
  have h1 : y422Orthogonal3SpiderPrefixes 2 = y422Orthogonal3SpiderPrefixes 1 *
      y422Orthogonal3Reflection 1 := by
    convert (y422Orthogonal3Spider_prefix_step ⟨1, by decide⟩) using 1 <;> rfl
  have h2 : y422Orthogonal3SpiderPrefixes 3 = y422Orthogonal3SpiderPrefixes 2 *
      y422Orthogonal3Reflection 2 := by
    convert (y422Orthogonal3Spider_prefix_step ⟨2, by decide⟩) using 1 <;> rfl
  have h3 : y422Orthogonal3SpiderPrefixes 4 = y422Orthogonal3SpiderPrefixes 3 *
      y422Orthogonal3Reflection 0 := by
    convert (y422Orthogonal3Spider_prefix_step ⟨3, by decide⟩) using 1 <;> rfl
  have h4 : y422Orthogonal3SpiderPrefixes 5 = y422Orthogonal3SpiderPrefixes 4 *
      y422Orthogonal3Reflection 5 := by
    convert (y422Orthogonal3Spider_prefix_step ⟨4, by decide⟩) using 1 <;> rfl
  have h5 : y422Orthogonal3SpiderPrefixes 6 = y422Orthogonal3SpiderPrefixes 5 *
      y422Orthogonal3Reflection 6 := by
    convert (y422Orthogonal3Spider_prefix_step ⟨5, by decide⟩) using 1 <;> rfl
  have h6 : y422Orthogonal3SpiderPrefixes 7 = y422Orthogonal3SpiderPrefixes 6 *
      y422Orthogonal3Reflection 0 := by
    convert (y422Orthogonal3Spider_prefix_step ⟨6, by decide⟩) using 1 <;> rfl
  have h7 : y422Orthogonal3SpiderPrefixes 8 = y422Orthogonal3SpiderPrefixes 7 *
      y422Orthogonal3Reflection 7 := by
    convert (y422Orthogonal3Spider_prefix_step ⟨7, by decide⟩) using 1 <;> rfl
  have h8 : y422Orthogonal3SpiderPrefixes 9 = y422Orthogonal3SpiderPrefixes 8 *
      y422Orthogonal3Reflection 8 := by
    convert (y422Orthogonal3Spider_prefix_step ⟨8, by decide⟩) using 1 <;> rfl
  rw [h8, h7, h6, h5, h4, h3, h2, h1, h0, y422Orthogonal3Spider_prefix_start]
  simp only [one_mul]

/-- The power chain starts at the actual identity. -/
theorem y422Orthogonal3Spider_power_start : y422Orthogonal3SpiderPowers 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Bounded finite matrix products are reduced in the kernel, using their exact source entries.
/-- Each bounded power step multiplies by the already certified prefix. -/
theorem y422Orthogonal3Spider_power_step (i : Fin 10) :
    y422Orthogonal3SpiderPowers i.succ = y422Orthogonal3SpiderPowers i.castSucc *
      y422Orthogonal3SpiderPrefixes 9 := by
  revert i
  decide +kernel

/-- The checked finite power chain is the actual monoid power. -/
theorem y422Orthogonal3Spider_power_value (i : Fin 11) :
    (y422Orthogonal3SpiderPrefixes 9) ^ i.val = y422Orthogonal3SpiderPowers i := by
  induction i using Fin.induction with
  | zero => exact y422Orthogonal3Spider_power_start.symm
  | succ i ih =>
    simp only [Fin.val_castSucc] at ih
    rw [Fin.val_succ, pow_succ, ih, ← y422Orthogonal3Spider_power_step i]

/-- The final original spider power is the identity. -/
theorem y422Orthogonal3Spider_power_end : y422Orthogonal3SpiderPowers 10 = 1 := by decide +kernel

/-- The original spider10 relation holds literally in the concrete matrices. -/
theorem y422Orthogonal3Spider_tenth : y422Orthogonal3Spider ^ 10 = 1 := by
  change (y422Orthogonal3Reflection 0 * y422Orthogonal3Reflection 1 *
      y422Orthogonal3Reflection 2 * y422Orthogonal3Reflection 0 *
      y422Orthogonal3Reflection 5 * y422Orthogonal3Reflection 6 *
      y422Orthogonal3Reflection 0 * y422Orthogonal3Reflection 7 *
      y422Orthogonal3Reflection 8) ^ 10 = 1
  rw [← y422Orthogonal3Spider_prefix_value]
  exact (y422Orthogonal3Spider_power_value 10).trans y422Orthogonal3Spider_power_end

/-- The exact original source letters of this finite product. -/
def y422Orthogonal3LongestLetters : Fin 7 → Fin 9 :=
  ![0, 1, 5, 7, 2, 6, 3]

/-- Exact successive prefix products, with all literal matrix entries. -/
def y422Orthogonal3LongestPrefixes : Fin 8 → Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![
    ![
        ![1, 0, 0, 0, 0, 0, 0, 0],
        ![0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![2, 1, 0, 0, 0, 1, 0, 1],
        ![0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![0, 2, 1, 0, 0, 1, 0, 1],
        ![1, 2, 1, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![1, 2, 1, 0, 0, 2, 1, 1],
        ![1, 2, 1, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 0, 0, 0, 0, 2, 1, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![2, 2, 1, 0, 0, 2, 1, 2],
        ![1, 2, 1, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 0, 0, 0, 0, 2, 1, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![1, 0, 0, 0, 0, 0, 0, 2]],
    ![
        ![2, 0, 2, 1, 0, 2, 1, 2],
        ![1, 0, 2, 1, 0, 0, 0, 0],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 0, 0, 0, 0, 2, 1, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![1, 0, 0, 0, 0, 0, 0, 2]],
    ![
        ![2, 0, 2, 1, 0, 0, 2, 2],
        ![1, 0, 2, 1, 0, 0, 0, 0],
        ![0, 1, 2, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 0, 0, 0, 0, 0, 2, 0],
        ![0, 0, 0, 0, 0, 1, 2, 0],
        ![1, 0, 0, 0, 0, 0, 0, 2]],
    ![
        ![2, 0, 0, 2, 1, 0, 2, 2],
        ![1, 0, 0, 2, 1, 0, 0, 0],
        ![0, 1, 0, 2, 1, 0, 0, 0],
        ![0, 0, 1, 2, 1, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 0, 0, 0, 0, 0, 2, 0],
        ![0, 0, 0, 0, 0, 1, 2, 0],
        ![1, 0, 0, 0, 0, 0, 0, 2]]]

/-- Exact successive powers of the already certified original source prefix. -/
def y422Orthogonal3LongestPowers : Fin 10 → Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![
    ![
        ![1, 0, 0, 0, 0, 0, 0, 0],
        ![0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![2, 0, 0, 2, 1, 0, 2, 2],
        ![1, 0, 0, 2, 1, 0, 0, 0],
        ![0, 1, 0, 2, 1, 0, 0, 0],
        ![0, 0, 1, 2, 1, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 0, 0, 0, 0, 0, 2, 0],
        ![0, 0, 0, 0, 0, 1, 2, 0],
        ![1, 0, 0, 0, 0, 0, 0, 2]],
    ![
        ![0, 0, 2, 2, 2, 2, 2, 2],
        ![2, 0, 2, 0, 1, 0, 2, 2],
        ![1, 0, 2, 0, 1, 0, 0, 0],
        ![0, 1, 2, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![2, 0, 0, 2, 1, 2, 0, 2],
        ![1, 0, 0, 0, 0, 2, 0, 0],
        ![1, 0, 0, 2, 1, 0, 2, 0]],
    ![
        ![1, 2, 2, 2, 0, 2, 2, 1],
        ![0, 2, 0, 2, 2, 2, 2, 2],
        ![2, 2, 0, 0, 1, 0, 2, 2],
        ![1, 2, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![2, 0, 2, 2, 2, 0, 2, 2],
        ![1, 0, 0, 2, 1, 0, 0, 2],
        ![2, 0, 2, 0, 1, 2, 0, 2]],
    ![
        ![1, 2, 2, 2, 1, 2, 1, 1],
        ![0, 0, 2, 2, 0, 2, 2, 1],
        ![2, 0, 0, 2, 2, 2, 2, 2],
        ![1, 0, 0, 0, 1, 0, 2, 2],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 2, 2, 0, 2, 2, 2, 2],
        ![1, 0, 2, 0, 1, 0, 2, 0],
        ![2, 2, 0, 2, 2, 0, 2, 2]],
    ![
        ![1, 2, 2, 2, 2, 1, 2, 1],
        ![0, 2, 2, 2, 1, 2, 2, 2],
        ![2, 0, 2, 2, 0, 2, 0, 2],
        ![1, 0, 0, 2, 2, 2, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 2, 0, 2, 0, 2, 2, 1],
        ![2, 2, 0, 0, 1, 2, 0, 2],
        ![2, 0, 2, 0, 2, 2, 2, 2]],
    ![
        ![0, 2, 2, 2, 0, 2, 2, 1],
        ![0, 2, 2, 0, 1, 2, 2, 1],
        ![2, 2, 2, 0, 0, 0, 2, 2],
        ![1, 0, 2, 0, 2, 0, 0, 2],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![2, 0, 2, 2, 1, 2, 2, 2],
        ![1, 0, 0, 2, 2, 0, 2, 2],
        ![2, 2, 0, 2, 0, 2, 0, 2]],
    ![
        ![2, 2, 2, 0, 0, 2, 2, 2],
        ![2, 2, 0, 2, 2, 2, 2, 2],
        ![2, 2, 0, 0, 0, 2, 2, 2],
        ![1, 2, 0, 0, 2, 0, 2, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![2, 2, 2, 0, 1, 2, 0, 2],
        ![1, 0, 2, 0, 2, 2, 0, 0],
        ![1, 0, 2, 0, 0, 0, 2, 2]],
    ![
        ![1, 2, 0, 0, 0, 2, 0, 2],
        ![1, 0, 2, 0, 2, 2, 0, 2],
        ![1, 0, 0, 2, 1, 2, 0, 2],
        ![1, 0, 0, 0, 2, 2, 0, 2],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![1, 2, 0, 0, 1, 0, 2, 2],
        ![1, 2, 0, 0, 2, 0, 0, 2],
        ![1, 2, 0, 0, 0, 2, 0, 0]],
    ![
        ![2, 0, 0, 0, 0, 0, 0, 0],
        ![0, 2, 0, 0, 2, 0, 0, 0],
        ![0, 0, 2, 0, 1, 0, 0, 0],
        ![0, 0, 0, 2, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 1, 2, 0, 0],
        ![0, 0, 0, 0, 2, 0, 2, 0],
        ![0, 0, 0, 0, 0, 0, 0, 2]]]

/-- The prefix chain starts at the actual identity. -/
theorem y422Orthogonal3Longest_prefix_start :
    y422Orthogonal3LongestPrefixes 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Bounded finite matrix products are reduced in the kernel, using their exact source entries.
/-- Each bounded prefix step is its actual predecessor times its exact source reflection. -/
theorem y422Orthogonal3Longest_prefix_step (i : Fin 7) :
    y422Orthogonal3LongestPrefixes i.succ = y422Orthogonal3LongestPrefixes i.castSucc *
      y422Orthogonal3Reflection (y422Orthogonal3LongestLetters i) := by
  revert i
  decide +kernel

/-- The final prefix is the exact original source product. -/
theorem y422Orthogonal3Longest_prefix_value : y422Orthogonal3LongestPrefixes 7 =
    y422Orthogonal3Reflection 0 * y422Orthogonal3Reflection 1 *
      y422Orthogonal3Reflection 5 * y422Orthogonal3Reflection 7 *
      y422Orthogonal3Reflection 2 * y422Orthogonal3Reflection 6 *
      y422Orthogonal3Reflection 3 := by
  have h0 : y422Orthogonal3LongestPrefixes 1 = y422Orthogonal3LongestPrefixes 0 *
      y422Orthogonal3Reflection 0 := by
    convert (y422Orthogonal3Longest_prefix_step ⟨0, by decide⟩) using 1 <;> rfl
  have h1 : y422Orthogonal3LongestPrefixes 2 = y422Orthogonal3LongestPrefixes 1 *
      y422Orthogonal3Reflection 1 := by
    convert (y422Orthogonal3Longest_prefix_step ⟨1, by decide⟩) using 1 <;> rfl
  have h2 : y422Orthogonal3LongestPrefixes 3 = y422Orthogonal3LongestPrefixes 2 *
      y422Orthogonal3Reflection 5 := by
    convert (y422Orthogonal3Longest_prefix_step ⟨2, by decide⟩) using 1 <;> rfl
  have h3 : y422Orthogonal3LongestPrefixes 4 = y422Orthogonal3LongestPrefixes 3 *
      y422Orthogonal3Reflection 7 := by
    convert (y422Orthogonal3Longest_prefix_step ⟨3, by decide⟩) using 1 <;> rfl
  have h4 : y422Orthogonal3LongestPrefixes 5 = y422Orthogonal3LongestPrefixes 4 *
      y422Orthogonal3Reflection 2 := by
    convert (y422Orthogonal3Longest_prefix_step ⟨4, by decide⟩) using 1 <;> rfl
  have h5 : y422Orthogonal3LongestPrefixes 6 = y422Orthogonal3LongestPrefixes 5 *
      y422Orthogonal3Reflection 6 := by
    convert (y422Orthogonal3Longest_prefix_step ⟨5, by decide⟩) using 1 <;> rfl
  have h6 : y422Orthogonal3LongestPrefixes 7 = y422Orthogonal3LongestPrefixes 6 *
      y422Orthogonal3Reflection 3 := by
    convert (y422Orthogonal3Longest_prefix_step ⟨6, by decide⟩) using 1 <;> rfl
  rw [h6, h5, h4, h3, h2, h1, h0, y422Orthogonal3Longest_prefix_start]
  simp only [one_mul]

/-- The power chain starts at the actual identity. -/
theorem y422Orthogonal3Longest_power_start : y422Orthogonal3LongestPowers 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Bounded finite matrix products are reduced in the kernel, using their exact source entries.
/-- Each bounded power step multiplies by the already certified prefix. -/
theorem y422Orthogonal3Longest_power_step (i : Fin 9) :
    y422Orthogonal3LongestPowers i.succ = y422Orthogonal3LongestPowers i.castSucc *
      y422Orthogonal3LongestPrefixes 7 := by
  revert i
  decide +kernel

/-- The checked finite power chain is the actual monoid power. -/
theorem y422Orthogonal3Longest_power_value (i : Fin 10) :
    (y422Orthogonal3LongestPrefixes 7) ^ i.val = y422Orthogonal3LongestPowers i := by
  induction i using Fin.induction with
  | zero => exact y422Orthogonal3Longest_power_start.symm
  | succ i ih =>
    simp only [Fin.val_castSucc] at ih
    rw [Fin.val_succ, pow_succ, ih, ← y422Orthogonal3Longest_power_step i]

/-- Exact powers of the printed Q base, after its checked longest prefix. -/
def y422Orthogonal3QPower : Fin 4 → Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![
    ![
        ![1, 0, 0, 0, 0, 0, 0, 0],
        ![0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 1, 0, 0, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0, 0],
        ![0, 0, 0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![2, 0, 0, 0, 0, 0, 0, 0],
        ![0, 2, 0, 2, 1, 0, 0, 0],
        ![0, 0, 2, 1, 2, 0, 0, 0],
        ![0, 0, 0, 2, 0, 0, 0, 0],
        ![0, 0, 0, 1, 2, 0, 0, 0],
        ![0, 0, 0, 1, 2, 2, 0, 0],
        ![0, 0, 0, 2, 1, 0, 2, 0],
        ![0, 0, 0, 0, 0, 0, 0, 2]],
    ![
        ![1, 0, 0, 0, 0, 0, 0, 0],
        ![0, 1, 0, 0, 1, 0, 0, 0],
        ![0, 0, 1, 0, 2, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 1, 1, 0, 0, 0],
        ![0, 0, 0, 0, 2, 1, 0, 0],
        ![0, 0, 0, 0, 1, 0, 1, 0],
        ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![
        ![2, 0, 0, 0, 0, 0, 0, 0],
        ![0, 2, 0, 0, 0, 0, 0, 0],
        ![0, 0, 2, 0, 0, 0, 0, 0],
        ![0, 0, 0, 2, 0, 0, 0, 0],
        ![0, 0, 0, 0, 2, 0, 0, 0],
        ![0, 0, 0, 0, 0, 2, 0, 0],
        ![0, 0, 0, 0, 0, 0, 2, 0],
        ![0, 0, 0, 0, 0, 0, 0, 2]]]

/-- The printed Q power chain starts at the actual identity. -/
theorem y422Orthogonal3QPower_start : y422Orthogonal3QPower 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Bounded finite matrix products are reduced in the kernel, using their exact source entries.
/-- Each Q power step uses the actual checked ninth longest power and source e1. -/
theorem y422Orthogonal3QPower_step (i : Fin 3) :
    y422Orthogonal3QPower i.succ = y422Orthogonal3QPower i.castSucc *
      (y422Orthogonal3LongestPowers 9 * y422Orthogonal3Reflection 4) := by
  revert i
  decide +kernel

/-- The checked Q powers equal the actual printed source-word powers. -/
theorem y422Orthogonal3QPower_value (i : Fin 4) :
    (y422Orthogonal3LongestPowers 9 * y422Orthogonal3Reflection 4) ^ i.val =
      y422Orthogonal3QPower i := by
  induction i using Fin.induction with
  | zero => exact y422Orthogonal3QPower_start.symm
  | succ i ih =>
    simp only [Fin.val_castSucc] at ih
    rw [Fin.val_succ, pow_succ, ih, ← y422Orthogonal3QPower_step i]

/-- The original Q cubic is the scalar minus identity before projectivizing. -/
theorem y422Orthogonal3QPower_end : y422Orthogonal3QPower 3 = -1 := by decide +kernel

/-- The exact printed source Q cubic is the central minus-identity scalar. -/
theorem y422Orthogonal3Q_scalar :
    (y422Orthogonal3Longest * y422Orthogonal3Reflection 4) ^ 3 = -1 := by
  have hl : y422Orthogonal3Longest = y422Orthogonal3LongestPowers 9 := by
    unfold y422Orthogonal3Longest
    rw [← y422Orthogonal3Longest_prefix_value]
    exact y422Orthogonal3Longest_power_value 9
  rw [hl]
  exact (y422Orthogonal3QPower_value 3).trans y422Orthogonal3QPower_end

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
