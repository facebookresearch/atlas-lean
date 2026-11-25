/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RelativeRootEquivalenceGroups
import MathlibExt.AlgebraicGeometry.ExpansionScalingModels
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Equal contact orders alone do not make a root swap eligible: the vertex
genus and incidence must also be preserved. Scaling coordinates are the
adjacent ratios (2,6) maps to (2,3), not the independent units (2,6).
-/

noncomputable section

open MathlibExt.AlgebraicGeometry.RelativeMapTypeModels
open MathlibExt.AlgebraicGeometry.RelativeRootEquivalenceGroups
open MathlibExt.AlgebraicGeometry.ExpansionScalingModels

private def roots : Fin 2 ≃ (Σ _v : Fin 2, Fin 1) where
  toFun i := ⟨i, 0⟩
  invFun i := i.1
  left_inv _ := rfl
  right_inv i := by
    rcases i with ⟨v, i⟩
    have h : i = 0 := Fin.eq_zero i
    subst i
    rfl

private def legs : Fin 0 ≃ (Σ _v : Fin 2, Fin 0) where
  toFun := Fin.elim0
  invFun i := Fin.elim0 i.2
  left_inv i := Fin.elim0 i
  right_inv i := Fin.elim0 i.2

private abbrev differentGenera : RelativeType 0 2 where
  vertices := 2
  nonempty := by decide
  legs _ := 0
  roots _ := 1
  genus i := i.val
  legLabels := legs
  rootLabels := roots
  order _ := 1
  positive _ := by decide
  relativelyConnected := Or.inr (fun v => ⟨v, rfl⟩)

example : ¬ eligible differentGenera (fun _ => ()) (Equiv.swap (0 : Fin 2) 1) := by
  rintro ⟨v, hg, hb, hl, hr, ho⟩
  have h := hr 0
  have h01 : v 0 = 1 := by simpa [differentGenera, roots] using h.symm
  have hgen := hg 0
  rw [h01] at hgen
  norm_num [differentGenera] at hgen

private def scales (i : Fin 2) : ℚˣ :=
  if i = 0 then Units.mk0 2 (by norm_num) else Units.mk0 6 (by norm_num)

example : (adjacentUnit scales (0 : Fin 2) : ℚ) = 2 := by simp [adjacentUnit, scales]

example : (adjacentUnit scales (1 : Fin 2) : ℚ) = 3 := by
  norm_num [adjacentUnit, scales]
