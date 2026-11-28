/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Knot.NonIsotopicTwoLinks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for the two-component unlink and Hopf link -/

open MathlibExt.Topology.ConwayKnotShared.KnotTheory
open MathlibExt.Topology.LinkingWanted.KnotTheory
open Set

private def equatorialDisk : Set R3 := {p | p 2 = 0 ∧ p 0 ^ 2 + p 1 ^ 2 ≤ 1}

-- Both first components trace the same disk boundary with the same parametrization.
example (t : ℝ) : unlink.K.curve t = hopfLink.K.curve t ∧
    (unlink.K.curve t) 2 = 0 ∧ (unlink.K.curve t) 0 ^ 2 + (unlink.K.curve t) 1 ^ 2 = 1 := by
  have hu : unlink.K.curve t = !₂[Real.cos t, Real.sin t, 0] :=
    congrArg Prod.fst (unlink_curves t)
  have hh : hopfLink.K.curve t = !₂[Real.cos t, Real.sin t, 0] :=
    congrArg Prod.fst (hopfLink_curves t)
  refine ⟨hu.trans hh.symm, ?_⟩
  rw [hu]
  change 0 = 0 ∧ Real.cos t ^ 2 + Real.sin t ^ 2 = 1
  exact ⟨rfl, Real.cos_sq_add_sin_sq t⟩

-- The second component of the unlink misses the entire disk, not just its boundary.
example : Disjoint (range unlink.L.curve) equatorialDisk := by
  apply disjoint_left.2
  rintro _ ⟨t, rfl⟩ h
  have ht : unlink.L.curve t = !₂[3 + Real.cos t / 2, 0, Real.sin t / 2] :=
    congrArg Prod.snd (unlink_curves t)
  rw [ht] at h
  change Real.sin t / 2 = 0 ∧ (3 + Real.cos t / 2) ^ 2 + 0 ^ 2 ≤ 1 at h
  have hx : (1 : ℝ) < 3 + Real.cos t / 2 := by linarith [Real.neg_one_le_cos t]
  nlinarith [h.2, mul_pos (sub_pos.mpr hx) (show 0 < 3 + Real.cos t / 2 + 1 by linarith)]

-- The second component of the Hopf link pierces the disk at exactly one point (at angle π).
example : range hopfLink.L.curve ∩ equatorialDisk = {(!₂[1 / 2, 0, 0] : R3)} := by
  have hcurve (t : ℝ) : hopfLink.L.curve t = !₂[1 + Real.cos t / 2, 0, Real.sin t / 2] :=
    congrArg Prod.snd (hopfLink_curves t)
  ext p
  constructor
  · rintro ⟨⟨t, rfl⟩, hp⟩
    rw [hcurve] at hp ⊢
    change Real.sin t / 2 = 0 ∧ (1 + Real.cos t / 2) ^ 2 + 0 ^ 2 ≤ 1 at hp
    have hz : Real.sin t = 0 := by linarith [hp.1]
    rcases Real.sin_eq_zero_iff_cos_eq.mp hz with hc | hc
    · norm_num [hc] at hp
    · norm_num [hc, hz]
  · rintro rfl
    refine ⟨⟨Real.pi, ?_⟩, ?_⟩
    · rw [hcurve]
      norm_num [Real.cos_pi, Real.sin_pi]
    · change 0 = 0 ∧ (1 / 2 : ℝ) ^ 2 + 0 ^ 2 ≤ 1
      norm_num

example : ∃ L₁ L₂ : TwoLink, ¬ L₁.Isotopic L₂ := exists_nonisotopic_link
