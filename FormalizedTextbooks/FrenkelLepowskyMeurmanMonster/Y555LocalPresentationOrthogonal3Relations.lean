/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal finite product certificates for the original C322 spider and longest word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Data

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact source letter order. -/
def y322Orthogonal3SpiderLetters : Fin 9 → Fin 8 :=
  ![0, 1, 2, 0, 4, 5, 0, 6, 7]

/-- Literal successive prefix products of the exact source word. -/
def y322Orthogonal3SpiderPrefixes : Fin 10 → Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![
    ![
      ![1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![2, 1, 0, 0, 1, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![0, 2, 1, 0, 1, 0, 1],
      ![1, 2, 1, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![0, 0, 2, 1, 1, 0, 1],
      ![1, 0, 2, 1, 0, 0, 0],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![0, 0, 2, 1, 1, 0, 1],
      ![2, 1, 2, 1, 1, 0, 1],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![1, 0, 2, 1, 2, 1, 1],
      ![0, 1, 2, 1, 2, 1, 1],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 2, 1, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![1, 0, 2, 1, 0, 2, 1],
      ![0, 1, 2, 1, 0, 2, 1],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0, 2, 0],
      ![0, 0, 0, 0, 1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![2, 1, 2, 1, 1, 2, 2],
      ![0, 1, 2, 1, 0, 2, 1],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![2, 1, 0, 0, 1, 2, 1],
      ![0, 0, 0, 0, 1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![1, 1, 2, 1, 1, 2, 1],
      ![1, 1, 2, 1, 0, 2, 2],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 1, 2, 2],
      ![0, 0, 0, 0, 1, 2, 0],
      ![1, 0, 0, 0, 0, 0, 2]],
    ![
      ![1, 1, 2, 1, 1, 2, 0],
      ![1, 1, 2, 1, 0, 2, 0],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 1, 2, 2],
      ![0, 0, 0, 0, 1, 2, 1],
      ![1, 0, 0, 0, 0, 0, 1]]]

/-- Literal successive power products of the exact source word. -/
def y322Orthogonal3SpiderPowers : Fin 11 → Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![
    ![
      ![1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![1, 1, 2, 1, 1, 2, 0],
      ![1, 1, 2, 1, 0, 2, 0],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 1, 2, 2],
      ![0, 0, 0, 0, 1, 2, 1],
      ![1, 0, 0, 0, 0, 0, 1]],
    ![
      ![2, 2, 2, 2, 1, 1, 1],
      ![2, 1, 2, 2, 0, 2, 2],
      ![1, 0, 0, 1, 0, 2, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 2, 2, 1, 0, 2, 0],
      ![1, 1, 0, 0, 0, 0, 2],
      ![2, 1, 2, 1, 1, 2, 1]],
    ![
      ![2, 1, 0, 2, 1, 0, 1],
      ![2, 2, 1, 1, 1, 1, 1],
      ![1, 1, 2, 2, 0, 0, 2],
      ![0, 0, 0, 1, 0, 0, 0],
      ![2, 1, 2, 2, 2, 2, 2],
      ![1, 2, 1, 2, 1, 1, 2],
      ![1, 0, 1, 0, 2, 0, 2]],
    ![
      ![1, 1, 0, 2, 0, 2, 0],
      ![2, 0, 1, 0, 1, 0, 1],
      ![1, 1, 2, 0, 1, 1, 2],
      ![0, 0, 0, 1, 0, 0, 0],
      ![2, 1, 1, 1, 0, 2, 2],
      ![2, 2, 2, 0, 0, 1, 2],
      ![0, 1, 1, 2, 0, 0, 0]],
    ![
      ![2, 2, 1, 1, 0, 2, 2],
      ![0, 1, 0, 0, 0, 0, 0],
      ![1, 2, 2, 1, 0, 2, 2],
      ![0, 0, 0, 1, 0, 0, 0],
      ![2, 1, 2, 2, 1, 1, 1],
      ![0, 0, 0, 0, 0, 1, 0],
      ![1, 2, 1, 1, 0, 2, 0]],
    ![
      ![0, 2, 1, 0, 1, 0, 1],
      ![1, 1, 2, 1, 0, 2, 0],
      ![2, 2, 1, 0, 0, 1, 1],
      ![0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 1, 1, 1, 1, 1],
      ![0, 0, 0, 0, 1, 2, 1],
      ![0, 1, 2, 2, 0, 1, 2]],
    ![
      ![0, 1, 0, 0, 1, 0, 0],
      ![2, 1, 2, 2, 0, 2, 2],
      ![2, 2, 1, 2, 0, 1, 2],
      ![0, 0, 0, 1, 0, 0, 0],
      ![2, 0, 1, 0, 0, 0, 1],
      ![1, 1, 0, 0, 0, 0, 2],
      ![0, 0, 0, 2, 1, 1, 0]],
    ![
      ![1, 2, 2, 1, 1, 1, 2],
      ![2, 2, 1, 1, 1, 1, 1],
      ![0, 2, 1, 1, 0, 1, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 2, 1, 1],
      ![1, 2, 1, 2, 1, 1, 2],
      ![0, 1, 0, 2, 2, 1, 0]],
    ![
      ![2, 0, 1, 0, 0, 1, 2],
      ![2, 0, 1, 0, 1, 0, 1],
      ![2, 0, 0, 1, 1, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0],
      ![1, 2, 0, 0, 0, 0, 0],
      ![2, 2, 2, 0, 0, 1, 2],
      ![1, 0, 2, 0, 0, 2, 2]],
    ![
      ![1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]]]

/-- The literal prefix starts at the identity. -/
theorem y322Orthogonal3Spider_prefix_start :
    y322Orthogonal3SpiderPrefixes 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks single products of small literal matrices at each finite step.
/-- Each literal prefix multiplies its predecessor by its actual source reflection. -/
theorem y322Orthogonal3Spider_prefix_step (i : Fin 9) :
    y322Orthogonal3SpiderPrefixes i.succ = y322Orthogonal3SpiderPrefixes i.castSucc *
      y322Orthogonal3Reflection (y322Orthogonal3SpiderLetters i) := by
  revert i
  decide +kernel

/-- The final literal prefix equals the exact source product. -/
theorem y322Orthogonal3Spider_prefix_value :
    y322Orthogonal3SpiderPrefixes 9 =
      y322Orthogonal3Spider := by
  have h0 : y322Orthogonal3SpiderPrefixes 1 = y322Orthogonal3SpiderPrefixes 0 *
      y322Orthogonal3Reflection 0 := by
    convert (y322Orthogonal3Spider_prefix_step ⟨0, by decide⟩) using 1 <;> rfl
  have h1 : y322Orthogonal3SpiderPrefixes 2 = y322Orthogonal3SpiderPrefixes 1 *
      y322Orthogonal3Reflection 1 := by
    convert (y322Orthogonal3Spider_prefix_step ⟨1, by decide⟩) using 1 <;> rfl
  have h2 : y322Orthogonal3SpiderPrefixes 3 = y322Orthogonal3SpiderPrefixes 2 *
      y322Orthogonal3Reflection 2 := by
    convert (y322Orthogonal3Spider_prefix_step ⟨2, by decide⟩) using 1 <;> rfl
  have h3 : y322Orthogonal3SpiderPrefixes 4 = y322Orthogonal3SpiderPrefixes 3 *
      y322Orthogonal3Reflection 0 := by
    convert (y322Orthogonal3Spider_prefix_step ⟨3, by decide⟩) using 1 <;> rfl
  have h4 : y322Orthogonal3SpiderPrefixes 5 = y322Orthogonal3SpiderPrefixes 4 *
      y322Orthogonal3Reflection 4 := by
    convert (y322Orthogonal3Spider_prefix_step ⟨4, by decide⟩) using 1 <;> rfl
  have h5 : y322Orthogonal3SpiderPrefixes 6 = y322Orthogonal3SpiderPrefixes 5 *
      y322Orthogonal3Reflection 5 := by
    convert (y322Orthogonal3Spider_prefix_step ⟨5, by decide⟩) using 1 <;> rfl
  have h6 : y322Orthogonal3SpiderPrefixes 7 = y322Orthogonal3SpiderPrefixes 6 *
      y322Orthogonal3Reflection 0 := by
    convert (y322Orthogonal3Spider_prefix_step ⟨6, by decide⟩) using 1 <;> rfl
  have h7 : y322Orthogonal3SpiderPrefixes 8 = y322Orthogonal3SpiderPrefixes 7 *
      y322Orthogonal3Reflection 6 := by
    convert (y322Orthogonal3Spider_prefix_step ⟨7, by decide⟩) using 1 <;> rfl
  have h8 : y322Orthogonal3SpiderPrefixes 9 = y322Orthogonal3SpiderPrefixes 8 *
      y322Orthogonal3Reflection 7 := by
    convert (y322Orthogonal3Spider_prefix_step ⟨8, by decide⟩) using 1 <;> rfl
  rw [h8, h7, h6, h5, h4, h3, h2, h1, h0, y322Orthogonal3Spider_prefix_start]
  simp only [one_mul, y322Orthogonal3Spider]

/-- The literal power starts at the identity. -/
theorem y322Orthogonal3Spider_power_start : y322Orthogonal3SpiderPowers 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks single products of small literal matrices at each finite step.
/-- Each power is its predecessor times the already checked source product. -/
theorem y322Orthogonal3Spider_power_step (i : Fin 10) :
    y322Orthogonal3SpiderPowers i.succ = y322Orthogonal3SpiderPowers i.castSucc *
      y322Orthogonal3SpiderPrefixes 9 := by
  revert i
  decide +kernel

/-- The checked finite power chain is the actual monoid power. -/
theorem y322Orthogonal3Spider_power_value (i : Fin 11) :
    (y322Orthogonal3SpiderPrefixes 9) ^ i.val = y322Orthogonal3SpiderPowers i := by
  induction i using Fin.induction with
  | zero => exact y322Orthogonal3Spider_power_start.symm
  | succ i ih =>
    simp only [Fin.val_castSucc] at ih
    rw [Fin.val_succ, pow_succ, ih, ← y322Orthogonal3Spider_power_step i]

/-- The last literal power has the asserted finite matrix value. -/
theorem y322Orthogonal3Spider_power_end : y322Orthogonal3SpiderPowers 10 = 1 := by decide +kernel

/-- The exact original source word has its certified actual matrix power. -/
theorem y322Orthogonal3Spider_tenth :
    y322Orthogonal3Spider ^ 10 = 1 := by
  rw [← y322Orthogonal3Spider_prefix_value]
  exact (y322Orthogonal3Spider_power_value 10).trans y322Orthogonal3Spider_power_end

/-- The exact source letter order. -/
def y322Orthogonal3LongestLetters : Fin 7 → Fin 8 :=
  ![0, 1, 4, 6, 2, 5, 3]

/-- Literal successive prefix products of the exact source word. -/
def y322Orthogonal3LongestPrefixes : Fin 8 → Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![
    ![
      ![1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![2, 1, 0, 0, 1, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![0, 2, 1, 0, 1, 0, 1],
      ![1, 2, 1, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![1, 2, 1, 0, 2, 1, 1],
      ![1, 2, 1, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 2, 1, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![2, 2, 1, 0, 2, 1, 2],
      ![1, 2, 1, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 2, 1, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 0, 2]],
    ![
      ![2, 0, 2, 1, 2, 1, 2],
      ![1, 0, 2, 1, 0, 0, 0],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 2, 1, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 0, 2]],
    ![
      ![2, 0, 2, 1, 0, 2, 2],
      ![1, 0, 2, 1, 0, 0, 0],
      ![0, 1, 2, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0, 2, 0],
      ![0, 0, 0, 0, 1, 2, 0],
      ![1, 0, 0, 0, 0, 0, 2]],
    ![
      ![2, 0, 0, 2, 0, 2, 2],
      ![1, 0, 0, 2, 0, 0, 0],
      ![0, 1, 0, 2, 0, 0, 0],
      ![0, 0, 1, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0, 2, 0],
      ![0, 0, 0, 0, 1, 2, 0],
      ![1, 0, 0, 0, 0, 0, 2]]]

/-- Literal successive power products of the exact source word. -/
def y322Orthogonal3LongestPowers : Fin 10 → Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![
    ![
      ![1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1]],
    ![
      ![2, 0, 0, 2, 0, 2, 2],
      ![1, 0, 0, 2, 0, 0, 0],
      ![0, 1, 0, 2, 0, 0, 0],
      ![0, 0, 1, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0, 2, 0],
      ![0, 0, 0, 0, 1, 2, 0],
      ![1, 0, 0, 0, 0, 0, 2]],
    ![
      ![0, 0, 2, 2, 2, 2, 2],
      ![2, 0, 2, 0, 0, 2, 2],
      ![1, 0, 2, 0, 0, 0, 0],
      ![0, 1, 2, 0, 0, 0, 0],
      ![2, 0, 0, 2, 2, 0, 2],
      ![1, 0, 0, 0, 2, 0, 0],
      ![1, 0, 0, 2, 0, 2, 0]],
    ![
      ![1, 2, 2, 2, 2, 2, 1],
      ![0, 2, 0, 2, 2, 2, 2],
      ![2, 2, 0, 0, 0, 2, 2],
      ![1, 2, 0, 0, 0, 0, 0],
      ![2, 0, 2, 2, 0, 2, 2],
      ![1, 0, 0, 2, 0, 0, 2],
      ![2, 0, 2, 0, 2, 0, 2]],
    ![
      ![1, 2, 2, 2, 2, 1, 1],
      ![0, 0, 2, 2, 2, 2, 1],
      ![2, 0, 0, 2, 2, 2, 2],
      ![1, 0, 0, 0, 0, 2, 2],
      ![0, 2, 2, 0, 2, 2, 2],
      ![1, 0, 2, 0, 0, 2, 0],
      ![2, 2, 0, 2, 0, 2, 2]],
    ![
      ![1, 2, 2, 2, 1, 2, 1],
      ![0, 2, 2, 2, 2, 2, 2],
      ![2, 0, 2, 2, 2, 0, 2],
      ![1, 0, 0, 2, 2, 0, 0],
      ![0, 2, 0, 2, 2, 2, 1],
      ![2, 2, 0, 0, 2, 0, 2],
      ![2, 0, 2, 0, 2, 2, 2]],
    ![
      ![0, 2, 2, 2, 2, 2, 1],
      ![0, 2, 2, 0, 2, 2, 1],
      ![2, 2, 2, 0, 0, 2, 2],
      ![1, 0, 2, 0, 0, 0, 2],
      ![2, 0, 2, 2, 2, 2, 2],
      ![1, 0, 0, 2, 0, 2, 2],
      ![2, 2, 0, 2, 2, 0, 2]],
    ![
      ![2, 2, 2, 0, 2, 2, 2],
      ![2, 2, 0, 2, 2, 2, 2],
      ![2, 2, 0, 0, 2, 2, 2],
      ![1, 2, 0, 0, 0, 2, 0],
      ![2, 2, 2, 0, 2, 0, 2],
      ![1, 0, 2, 0, 2, 0, 0],
      ![1, 0, 2, 0, 0, 2, 2]],
    ![
      ![1, 2, 0, 0, 2, 0, 2],
      ![1, 0, 2, 0, 2, 0, 2],
      ![1, 0, 0, 2, 2, 0, 2],
      ![1, 0, 0, 0, 2, 0, 2],
      ![1, 2, 0, 0, 0, 2, 2],
      ![1, 2, 0, 0, 0, 0, 2],
      ![1, 2, 0, 0, 2, 0, 0]],
    ![
      ![2, 0, 0, 0, 0, 0, 0],
      ![0, 2, 0, 0, 0, 0, 0],
      ![0, 0, 2, 0, 0, 0, 0],
      ![0, 0, 0, 2, 0, 0, 0],
      ![0, 0, 0, 0, 2, 0, 0],
      ![0, 0, 0, 0, 0, 2, 0],
      ![0, 0, 0, 0, 0, 0, 2]]]

/-- The literal prefix starts at the identity. -/
theorem y322Orthogonal3Longest_prefix_start :
    y322Orthogonal3LongestPrefixes 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks single products of small literal matrices at each finite step.
/-- Each literal prefix multiplies its predecessor by its actual source reflection. -/
theorem y322Orthogonal3Longest_prefix_step (i : Fin 7) :
    y322Orthogonal3LongestPrefixes i.succ = y322Orthogonal3LongestPrefixes i.castSucc *
      y322Orthogonal3Reflection (y322Orthogonal3LongestLetters i) := by
  revert i
  decide +kernel

/-- The final literal prefix equals the exact source product. -/
theorem y322Orthogonal3Longest_prefix_value :
    y322Orthogonal3LongestPrefixes 7 =
      (y322Orthogonal3Reflection 0 * y322Orthogonal3Reflection 1 *
      y322Orthogonal3Reflection 4 * y322Orthogonal3Reflection 6 *
      y322Orthogonal3Reflection 2 * y322Orthogonal3Reflection 5 * y322Orthogonal3Reflection 3) := by
  have h0 : y322Orthogonal3LongestPrefixes 1 = y322Orthogonal3LongestPrefixes 0 *
      y322Orthogonal3Reflection 0 := by
    convert (y322Orthogonal3Longest_prefix_step ⟨0, by decide⟩) using 1 <;> rfl
  have h1 : y322Orthogonal3LongestPrefixes 2 = y322Orthogonal3LongestPrefixes 1 *
      y322Orthogonal3Reflection 1 := by
    convert (y322Orthogonal3Longest_prefix_step ⟨1, by decide⟩) using 1 <;> rfl
  have h2 : y322Orthogonal3LongestPrefixes 3 = y322Orthogonal3LongestPrefixes 2 *
      y322Orthogonal3Reflection 4 := by
    convert (y322Orthogonal3Longest_prefix_step ⟨2, by decide⟩) using 1 <;> rfl
  have h3 : y322Orthogonal3LongestPrefixes 4 = y322Orthogonal3LongestPrefixes 3 *
      y322Orthogonal3Reflection 6 := by
    convert (y322Orthogonal3Longest_prefix_step ⟨3, by decide⟩) using 1 <;> rfl
  have h4 : y322Orthogonal3LongestPrefixes 5 = y322Orthogonal3LongestPrefixes 4 *
      y322Orthogonal3Reflection 2 := by
    convert (y322Orthogonal3Longest_prefix_step ⟨4, by decide⟩) using 1 <;> rfl
  have h5 : y322Orthogonal3LongestPrefixes 6 = y322Orthogonal3LongestPrefixes 5 *
      y322Orthogonal3Reflection 5 := by
    convert (y322Orthogonal3Longest_prefix_step ⟨5, by decide⟩) using 1 <;> rfl
  have h6 : y322Orthogonal3LongestPrefixes 7 = y322Orthogonal3LongestPrefixes 6 *
      y322Orthogonal3Reflection 3 := by
    convert (y322Orthogonal3Longest_prefix_step ⟨6, by decide⟩) using 1 <;> rfl
  rw [h6, h5, h4, h3, h2, h1, h0, y322Orthogonal3Longest_prefix_start]
  simp only [one_mul]

/-- The literal power starts at the identity. -/
theorem y322Orthogonal3Longest_power_start : y322Orthogonal3LongestPowers 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks single products of small literal matrices at each finite step.
/-- Each power is its predecessor times the already checked source product. -/
theorem y322Orthogonal3Longest_power_step (i : Fin 9) :
    y322Orthogonal3LongestPowers i.succ = y322Orthogonal3LongestPowers i.castSucc *
      y322Orthogonal3LongestPrefixes 7 := by
  revert i
  decide +kernel

/-- The checked finite power chain is the actual monoid power. -/
theorem y322Orthogonal3Longest_power_value (i : Fin 10) :
    (y322Orthogonal3LongestPrefixes 7) ^ i.val = y322Orthogonal3LongestPowers i := by
  induction i using Fin.induction with
  | zero => exact y322Orthogonal3Longest_power_start.symm
  | succ i ih =>
    simp only [Fin.val_castSucc] at ih
    rw [Fin.val_succ, pow_succ, ih, ← y322Orthogonal3Longest_power_step i]

/-- The last literal power has the asserted finite matrix value. -/
theorem y322Orthogonal3Longest_power_end : y322Orthogonal3LongestPowers 9 = -1 := by decide +kernel

/-- The exact original source word has its certified actual matrix power. -/
theorem y322Orthogonal3Reflection_longest :
    (y322Orthogonal3Reflection 0 * y322Orthogonal3Reflection 1 *
      y322Orthogonal3Reflection 4 * y322Orthogonal3Reflection 6 *
      y322Orthogonal3Reflection 2 * y322Orthogonal3Reflection 5 *
      y322Orthogonal3Reflection 3) ^ 9 = -1 := by
  rw [← y322Orthogonal3Longest_prefix_value]
  exact (y322Orthogonal3Longest_power_value 9).trans y322Orthogonal3Longest_power_end

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
