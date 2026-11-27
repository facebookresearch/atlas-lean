/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
import MathlibExt.GroupTheory.Kourovka21Problem134b

open MathlibExt.GroupTheory.Kourovka21Problem134bWanted

example : ¬ conjecture.{1, 2} := conjecture_refuted

example : ¬ SamePowerEquationType (Multiplicative (ZMod 4))
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  intro h
  have h₂ := h 2 (by decide)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h₂
  exact (by decide +kernel : ¬ _) h₂
