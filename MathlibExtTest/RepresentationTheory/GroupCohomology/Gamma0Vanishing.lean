/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_TW12CD1Dock_subsingleton_H2_gamma0.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RepresentationTheory.GroupCohomology.Gamma0Vanishing
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

@[expose] public section

open CongruenceSubgroup groupCohomology

open scoped MatrixGroups

/-- Consumer with the original binders (`Type 0`). -/
private theorem exactSource {k : Type} [CommRing k] (M : ℕ) (h6 : IsUnit (6 : k))
    (A : Rep k ↥(Gamma0 M)) : Subsingleton (groupCohomology A 2) :=
  CongruenceSubgroup.subsingleton_H2_Gamma0 M h6 A

/-- A concrete instance: rational coefficients at level `11`. -/
example (A : Rep ℚ ↥(Gamma0 11)) : Subsingleton (groupCohomology A 2) :=
  CongruenceSubgroup.subsingleton_H2_Gamma0 11 (isUnit_iff_ne_zero.mpr (by norm_num)) A

/-- Level `0` (the upper triangular subgroup) with trivial coefficients in `ZMod 5`, where `6`
is the unit `1`. -/
example : Subsingleton (groupCohomology (Rep.trivial (ZMod 5) ↥(Gamma0 0) (ZMod 5)) 2) :=
  CongruenceSubgroup.subsingleton_H2_Gamma0 0 (IsUnit.of_mul_eq_one 1 (by decide)) _

/-! ### The unit hypothesis cannot be dropped

At level `0` with trivial coefficients in `ZMod 2`, where `6 = 0`, the upper-left entry `±1` of
an element of `Γ₀(0)` is a homomorphism onto `{±1}`, split by `{±I}`. The cup square of the
corresponding sign is a 2-cocycle whose class is nonzero: every coboundary `d ψ` takes the same
value `ψ(I)` at `(I, I)` and at `(-I, -I)`, namely `ψ(I) - ψ(I) + ψ(I)` and
`ψ(-I) - ψ(I) + ψ(-I)` in `ZMod 2`, whereas the cup square takes the values `0` and `1` there. -/

/-- The sign of the upper-left entry of an element of `Γ₀(0)`, written additively in `ZMod 2`:
`0` when the entry is `1`, and `1` otherwise. -/
private def sgn (g : ↥(Gamma0 0)) : ZMod 2 := if (g : SL(2, ℤ)).1 0 0 = 1 then 0 else 1

private theorem lowerLeft_eq_zero (g : ↥(Gamma0 0)) : (g : SL(2, ℤ)).1 1 0 = 0 := by
  have h := g.2
  rw [Gamma0_mem] at h
  exact h

private theorem upperLeft_mul (g h : ↥(Gamma0 0)) :
    ((g * h : ↥(Gamma0 0)) : SL(2, ℤ)).1 0 0 = (g : SL(2, ℤ)).1 0 0 * (h : SL(2, ℤ)).1 0 0 := by
  rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    lowerLeft_eq_zero h, mul_zero, add_zero]

private theorem upperLeft_eq_one_or_neg_one (g : ↥(Gamma0 0)) :
    (g : SL(2, ℤ)).1 0 0 = 1 ∨ (g : SL(2, ℤ)).1 0 0 = -1 := by
  have hdet : (g : SL(2, ℤ)).1.det = 1 := (g : SL(2, ℤ)).2
  rw [Matrix.det_fin_two, lowerLeft_eq_zero g, mul_zero, sub_zero] at hdet
  exact Int.eq_one_or_neg_one_of_mul_eq_one hdet

private theorem sgn_mul (g h : ↥(Gamma0 0)) : sgn (g * h) = sgn g + sgn h := by
  unfold sgn
  rw [upperLeft_mul]
  rcases upperLeft_eq_one_or_neg_one g with hg | hg <;>
    rcases upperLeft_eq_one_or_neg_one h with hh | hh <;>
    rw [hg, hh] <;> decide

/-- The cup square of `sgn`. -/
private def sgnSq : ↥(Gamma0 0) × ↥(Gamma0 0) → ZMod 2 := fun gh => sgn gh.1 * sgn gh.2

private theorem sgnSq_mem_cocycles₂ :
    sgnSq ∈ cocycles₂ (Rep.trivial (ZMod 2) ↥(Gamma0 0) (ZMod 2)) := by
  rw [mem_cocycles₂_iff]
  intro g h j
  simp only [sgnSq, Representation.trivial_apply, sgn_mul]
  ring

/-- `H²(Γ₀(0), ZMod 2) ≠ 0` for trivial coefficients. -/
private theorem not_subsingleton_H2_Gamma0_zero :
    ¬ Subsingleton (groupCohomology (Rep.trivial (ZMod 2) ↥(Gamma0 0) (ZMod 2)) 2) := by
  intro hsub
  let x : cocycles₂ (Rep.trivial (ZMod 2) ↥(Gamma0 0) (ZMod 2)) := ⟨sgnSq, sgnSq_mem_cocycles₂⟩
  have h0 : H2π (Rep.trivial (ZMod 2) ↥(Gamma0 0) (ZMod 2)) x = 0 := Subsingleton.elim _ _
  rw [H2π_eq_zero_iff] at h0
  obtain ⟨ψ, hψ⟩ := h0
  let s : ↥(Gamma0 0) := ⟨-1, by rw [Gamma0_mem]; simp⟩
  have hss : s * s = 1 := Subtype.ext (by simp [s])
  have hs : sgn s = 1 := by simp [sgn, s]
  have h1 : sgn 1 = 0 := by simp [sgn]
  have e₁ : ψ 1 - ψ (1 * 1) + ψ 1 = sgn 1 * sgn 1 := congrFun hψ (1, 1)
  have e₂ : ψ s - ψ (s * s) + ψ s = sgn s * sgn s := congrFun hψ (s, s)
  rw [mul_one, h1] at e₁
  rw [hss, hs] at e₂
  revert e₁ e₂
  generalize ψ s = a
  generalize ψ 1 = b
  revert a b
  decide

/-- The theorem fails without its unit hypothesis: at level `0` with trivial coefficients in
`ZMod 2`, where `6 = 0`, the second cohomology is not zero. -/
example : ¬ ∀ (M : ℕ) (A : Rep (ZMod 2) ↥(Gamma0 M)), Subsingleton (groupCohomology A 2) :=
  fun h => not_subsingleton_H2_Gamma0_zero (h 0 _)

/-- The same boundary read through the theorem: it forces `6` to be a nonunit in `ZMod 2`. -/
example : ¬ IsUnit (6 : ZMod 2) := fun h6 =>
  not_subsingleton_H2_Gamma0_zero (CongruenceSubgroup.subsingleton_H2_Gamma0 0 h6 _)
