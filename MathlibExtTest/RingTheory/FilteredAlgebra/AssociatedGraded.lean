/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.RingTheory.FilteredAlgebra.AssociatedGraded
public import Mathlib.Tactic.NormNum

/-!
# A concrete associated-graded algebra and a nonunital additive client

Filter the product ring Z × Z by the diagonal copy of Z in degree zero and the whole ring
in positive degrees. The nonzero diagonal representative (2,2) survives in degree zero but
vanishes in degree one. The degree-one class of (1,0) is nonzero, and its square vanishes in
degree two. Symbol products and scalar multiplication use the inferred associated-graded
algebra structure.

The constant family 2Z has no unit. Its positive quotient layers vanish, and agreement on
degree-zero symbols determines linear maps without any multiplicative filtration hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace FilteredAlgebra.AssociatedGradedClient

private abbrev A := ℤ × ℤ

private def diagonal : Submodule ℤ A := (Algebra.linearMap ℤ A).range

private def filtration (n : ℕ) : Submodule ℤ A :=
  if n = 0 then diagonal else ⊤

private theorem filtration_mono : Monotone filtration := by
  intro i j hij
  cases i with
  | zero =>
      cases j with
      | zero => exact le_rfl
      | succ j => simp [filtration]
  | succ i =>
      have hj : j ≠ 0 := by omega
      simp [filtration, hj]

private instance : IsRingFiltration filtration (lower filtration) where
  __ := isFiltration_lower filtration filtration_mono
  one_mem := by
    change (1 : A) ∈ diagonal
    exact ⟨1, by simp [Algebra.linearMap_apply]⟩
  mul_mem := by
    intro i j x y hx hy
    cases i with
    | zero =>
        cases j with
        | zero =>
            change x ∈ diagonal at hx
            change y ∈ diagonal at hy
            rcases hx with ⟨a, rfl⟩
            rcases hy with ⟨b, rfl⟩
            exact ⟨a * b, by simp [Algebra.linearMap_apply, map_mul]⟩
        | succ j => simp [filtration]
    | succ i => simp [filtration, Nat.succ_add]

private def diagonalRepresentative (z : ℤ) : filtration 0 :=
  ⟨(z, z), ⟨z, by ext <;> simp [Algebra.linearMap_apply]⟩⟩

private def positiveRepresentative (n : ℕ) (hn : n ≠ 0) (x : A) : filtration n :=
  ⟨x, by simp [filtration, hn]⟩

private abbrev degreeOneRepresentative : filtration 1 :=
  positiveRepresentative 1 (by decide) (1, 0)

private theorem symbol_zero_of_lower (n : ℕ) (x : filtration n)
    (hx : x ∈ lowerInStage filtration n) : symbol filtration n x = 0 := by
  have hq : (lowerInStage filtration n).mkQ x = 0 :=
    (Submodule.Quotient.mk_eq_zero (lowerInStage filtration n)).mpr hx
  simp only [symbol_mk, hq, map_zero]

example :
    symbol filtration 1 (positiveRepresentative 1 (by decide) (2, 2)) = 0 := by
  apply symbol_zero_of_lower
  apply (mem_lowerInStage_iff filtration 1 _).mpr
  change (2, 2) ∈ diagonal
  exact ⟨2, by ext <;> simp [Algebra.linearMap_apply]⟩

example : symbol filtration 0 (diagonalRepresentative 2) ≠ 0 := by
  intro h
  have hq : (lowerInStage filtration 0).mkQ (diagonalRepresentative 2) = 0 := by
    have hc := congrArg (DirectSum.component ℤ ℕ (Grade filtration) 0) h
    simpa only [symbol_mk, DirectSum.component.lof_self, map_zero] using hc
  have hx := (Submodule.Quotient.mk_eq_zero (lowerInStage filtration 0)).mp hq
  have hz : diagonalRepresentative 2 = 0 := by simpa [lowerInStage] using hx
  have hf := congrArg (fun x : filtration 0 => x.val.1) hz
  norm_num [diagonalRepresentative] at hf

example : symbol filtration 1 degreeOneRepresentative ≠ 0 := by
  intro h
  have hq : (lowerInStage filtration 1).mkQ degreeOneRepresentative = 0 := by
    have hc := congrArg (DirectSum.component ℤ ℕ (Grade filtration) 1) h
    simpa only [symbol_mk, DirectSum.component.lof_self, map_zero] using hc
  have hx := (Submodule.Quotient.mk_eq_zero (lowerInStage filtration 1)).mp hq
  have hd := (mem_lowerInStage_iff filtration 1 degreeOneRepresentative).mp hx
  change (1, 0) ∈ diagonal at hd
  rcases hd with ⟨z, hz⟩
  have hf : z = 1 := by
    simpa [Algebra.linearMap_apply] using congrArg Prod.fst hz
  have hs : z = 0 := by
    simpa [Algebra.linearMap_apply] using congrArg Prod.snd hz
  have hbad : (1 : ℤ) = 0 := hf.symm.trans hs
  norm_num at hbad

example :
    symbol filtration 1 degreeOneRepresentative *
      symbol filtration 1 degreeOneRepresentative = 0 := by
  rw [symbol_mul]
  apply symbol_zero_of_lower
  apply (mem_lowerInStage_iff filtration (1 + 1) _).mpr
  simp [lower, filtration]

example :
    symbol filtration 0 (diagonalRepresentative 2) *
      symbol filtration 0 (diagonalRepresentative 3) =
      symbol filtration 0 (diagonalRepresentative 6) := by
  rw [symbol_mul]
  exact symbol_congr filtration rfl _ _ (by norm_num [diagonalRepresentative])

example :
    symbol filtration 0 (diagonalRepresentative 2) *
      symbol filtration 1 degreeOneRepresentative =
      symbol filtration 1 (positiveRepresentative 1 (by decide) (2, 0)) := by
  rw [symbol_mul]
  exact symbol_congr filtration rfl _ _
    (by norm_num [diagonalRepresentative, degreeOneRepresentative, positiveRepresentative])

example : Algebra ℤ (AssociatedGraded filtration) := inferInstance

private theorem algebraMap_two :
    algebraMap ℤ (AssociatedGraded filtration) 2 =
      symbol filtration 0 (diagonalRepresentative 2) := by
  rw [← symbol_algebraMap filtration 2]
  apply congrArg (symbol filtration 0)
  apply Subtype.ext
  change algebraMap ℤ A 2 = ((2 : ℤ), (2 : ℤ))
  ext <;> norm_num

example :
    (2 : ℤ) • symbol filtration 1 degreeOneRepresentative =
      symbol filtration 1 (positiveRepresentative 1 (by decide) (2, 0)) := by
  rw [Algebra.smul_def, algebraMap_two, symbol_mul]
  exact symbol_congr filtration rfl _ _
    (by norm_num [diagonalRepresentative, degreeOneRepresentative, positiveRepresentative])

private def evenFamily (_n : ℕ) : Submodule ℤ ℤ :=
  Submodule.span ℤ {(2 : ℤ)}

example : (1 : ℤ) ∉ evenFamily 0 := by
  intro h
  change (1 : ℤ) ∈ Submodule.span ℤ {(2 : ℤ)} at h
  rcases Submodule.mem_span_singleton.mp h with ⟨r, hr⟩
  have hr' : r * 2 = (1 : ℤ) := by simpa [smul_eq_mul] using hr
  omega

example (f g : AssociatedGraded evenFamily →ₗ[ℤ] ℤ)
    (h : ∀ x : evenFamily 0, f (symbol evenFamily 0 x) = g (symbol evenFamily 0 x)) :
    f = g := by
  apply linearMap_ext_symbol evenFamily
  intro n x
  cases n with
  | zero => exact h x
  | succ n =>
      have hx : x ∈ lowerInStage evenFamily (n + 1) := x.property
      have hq : (lowerInStage evenFamily (n + 1)).mkQ x = 0 :=
        (Submodule.Quotient.mk_eq_zero (lowerInStage evenFamily (n + 1))).mpr hx
      simp only [symbol_mk, hq, map_zero]

end FilteredAlgebra.AssociatedGradedClient
