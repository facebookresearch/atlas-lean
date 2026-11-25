/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PadicFormalSchemes
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! The second 2-adic thickening retains a nonzero square-zero element,
which disappears in the first level. These are actual quotient rings.
-/

open MathlibExt.AlgebraicGeometry.PadicFormalSchemes

private lemma secondIdeal :
    levelIdeal 2 (ZMod 4) ⊥ 1 = ⊥ := by
  simp [levelIdeal, Ideal.span_singleton_pow,
    show (2 : ZMod 4) ^ 2 = 0 by decide]

private def secondToZMod : LevelRing 2 (ZMod 4) ⊥ 1 →+* ZMod 4 :=
  Ideal.Quotient.lift _ (RingHom.id _) (by
    intro a ha
    rw [secondIdeal] at ha
    exact ha)

example : (2 : LevelRing 2 (ZMod 4) ⊥ 1) ≠ 0 := by
  intro h
  have hh := congrArg secondToZMod h
  rw [map_ofNat, map_zero] at hh
  exact (by decide : (2 : ZMod 4) ≠ 0) hh

example : (2 : LevelRing 2 (ZMod 4) ⊥ 1) ^ 2 = 0 := by
  change Ideal.Quotient.mk _ ((2 : ZMod 4) ^ 2) = 0
  rw [show (2 : ZMod 4) ^ 2 = 0 by decide, map_zero]

example : (2 : LevelRing 2 (ZMod 4) ⊥ 0) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h : Ideal.span {(2 : ZMod 4)} ≤ levelIdeal 2 (ZMod 4) ⊥ 0 := by
    simp [levelIdeal]
  exact h (Ideal.subset_span (by simp))

example : reduction 2 (ZMod 4) ⊥ (show 0 ≤ 1 by decide)
    (2 : LevelRing 2 (ZMod 4) ⊥ 1) = 0 := by
  change (2 : LevelRing 2 (ZMod 4) ⊥ 0) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h : Ideal.span {(2 : ZMod 4)} ≤ levelIdeal 2 (ZMod 4) ⊥ 0 := by
    simp [levelIdeal]
  exact h (Ideal.subset_span (by simp))
