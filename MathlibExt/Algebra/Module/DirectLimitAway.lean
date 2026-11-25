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

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Tactic

/-!
# Localization away from an element as a sequential direct limit

For an `R`-module `M` and `r : R`, consider the constant sequential system

```text
M --r•--> M --r•--> M --r•--> ⋯.
```

This file proves that its module direct limit is the localization of `M`
away from `r`. The proof constructs the inverse shift to scalar
multiplication by `r` and verifies the specialized
`IsLocalizedModule.Away` universal property.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module

variable {R : Type u} [CommSemiring R]
  (M : Type v) [AddCommMonoid M] [Module R M]

/-- Transition from stage `i` to stage `j`: multiply by `r^(j-i)`. -/
def awayTransition (r : R) (i j : ℕ) (_ : i ≤ j) : M →ₗ[R] M :=
  LinearMap.lsmul R M (r ^ (j - i))

instance awayTransition_directedSystem (r : R) :
    DirectedSystem (fun _ : ℕ ↦ M) (awayTransition M r · · ·) where
  map_self i x := by
    simp [awayTransition]
  map_map {k j i} hij hjk x := by
    change r ^ (k - j) • (r ^ (j - i) • x) = r ^ (k - i) • x
    rw [← mul_smul, ← pow_add]
    congr 2
    omega

/-- The sequential direct limit under repeated multiplication by `r`. -/
abbrev AwayDirectLimit (r : R) :=
  Module.DirectLimit (fun _ : ℕ ↦ M) (awayTransition M r)

/-- The canonical stage-zero map into the sequential direct limit. -/
def awayDirectLimitMap (r : R) : M →ₗ[R] AwayDirectLimit M r :=
  Module.DirectLimit.of R ℕ (fun _ : ℕ ↦ M)
    (awayTransition M r) 0

/-- Increasing the stage by one defines the inverse shift on the direct
limit. -/
def awayShift (r : R) : AwayDirectLimit M r →ₗ[R] AwayDirectLimit M r :=
  Module.DirectLimit.lift R ℕ (fun _ : ℕ ↦ M)
    (awayTransition M r)
    (fun n ↦ Module.DirectLimit.of R ℕ (fun _ : ℕ ↦ M)
      (awayTransition M r) (n + 1))
    (by
      intro i j hij x
      have hsucc : i + 1 ≤ j + 1 := Nat.add_le_add_right hij 1
      have h := Module.DirectLimit.of_f
        (R := R) (G := fun _ : ℕ ↦ M)
        (f := awayTransition M r) (i := i + 1) (j := j + 1)
        (hij := hsucc) (x := x)
      simpa [awayTransition, Nat.succ_sub_succ_eq_sub] using h)

@[simp]
theorem awayShift_of (r : R) (n : ℕ) (x : M) :
    awayShift M r
        (Module.DirectLimit.of R ℕ (fun _ : ℕ ↦ M)
          (awayTransition M r) n x) =
      Module.DirectLimit.of R ℕ (fun _ : ℕ ↦ M)
        (awayTransition M r) (n + 1) x :=
  by simp [awayShift]

/-- Multiplication by `r` after shifting is the identity. -/
theorem r_smul_awayShift (r : R) (z : AwayDirectLimit M r) :
    r • awayShift M r z = z := by
  induction z using Module.DirectLimit.induction_on with
  | _ n x =>
      rw [awayShift_of, ← map_smul]
      simpa [awayTransition, pow_one] using Module.DirectLimit.of_f
        (R := R) (G := fun _ : ℕ ↦ M)
        (f := awayTransition M r) (i := n) (j := n + 1)
        (hij := Nat.le_succ n) (x := x)

/-- Shifting after multiplication by `r` is the identity. -/
theorem awayShift_r_smul (r : R) (z : AwayDirectLimit M r) :
    awayShift M r (r • z) = z := by
  induction z using Module.DirectLimit.induction_on with
  | _ n x =>
      rw [← map_smul, awayShift_of]
      simpa [awayTransition, pow_one] using Module.DirectLimit.of_f
        (R := R) (G := fun _ : ℕ ↦ M)
        (f := awayTransition M r) (i := n) (j := n + 1)
        (hij := Nat.le_succ n) (x := x)

/-- The element `r` acts invertibly on the sequential direct limit. -/
theorem awayDirectLimit_isUnit_algebraMap (r : R) :
    IsUnit
      (algebraMap R (Module.End R (AwayDirectLimit M r)) r) := by
  rw [Module.End.isUnit_iff]
  change Function.Bijective (fun z : AwayDirectLimit M r ↦ r • z)
  constructor
  · intro x y h
    have h' := congrArg (awayShift M r) h
    simpa only [awayShift_r_smul] using h'
  · intro z
    exact ⟨awayShift M r z, r_smul_awayShift M r z⟩

/-- A stage-`n` class becomes a stage-zero class after multiplication by
`r^n`. -/
theorem pow_smul_of_eq_awayDirectLimitMap (r : R) (n : ℕ) (x : M) :
    r ^ n •
        Module.DirectLimit.of R ℕ (fun _ : ℕ ↦ M)
          (awayTransition M r) n x =
      awayDirectLimitMap M r x := by
  rw [← map_smul]
  exact Module.DirectLimit.of_f
    (R := R) (G := fun _ : ℕ ↦ M)
    (f := awayTransition M r) (i := 0) (j := n)
    (hij := Nat.zero_le n) (x := x)

/-- The stage-zero map exhibits the sequential direct limit as localization
away from `r`. -/
theorem awayDirectLimit_isLocalizedModule (r : R) :
    IsLocalizedModule.Away r (awayDirectLimitMap M r) := by
  apply IsLocalizedModule.Away.mk
  · exact awayDirectLimit_isUnit_algebraMap M r
  · intro z
    induction z using Module.DirectLimit.induction_on with
    | _ n x =>
        exact ⟨n, x, pow_smul_of_eq_awayDirectLimitMap M r n x⟩
  · intro x y hxy
    obtain ⟨n, _, hn⟩ := Module.DirectLimit.exists_eq_of_of_eq
      (R := R) (G := fun _ : ℕ ↦ M)
      (f := awayTransition M r) hxy
    exact ⟨n, by simpa [awayTransition] using hn⟩

/-- The sequential direct limit is canonically linearly equivalent to the
localized module away from `r`. -/
noncomputable def awayDirectLimitLinearEquiv (r : R) :
    AwayDirectLimit M r ≃ₗ[R] LocalizedModule.Away r M := by
  let _ : IsLocalizedModule.Away r (awayDirectLimitMap M r) :=
    awayDirectLimit_isLocalizedModule M r
  exact (IsLocalizedModule.iso (Submonoid.powers r)
    (awayDirectLimitMap M r)).symm

/-- Under the canonical equivalence, a stage-`n` class is the fraction with
denominator `r^n`. -/
theorem awayDirectLimitLinearEquiv_of (r : R) (n : ℕ) (x : M) :
    awayDirectLimitLinearEquiv M r
        (Module.DirectLimit.of R ℕ (fun _ : ℕ ↦ M)
          (awayTransition M r) n x) =
      LocalizedModule.mk x
        ⟨r ^ n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩ := by
  let _ : IsLocalizedModule.Away r (awayDirectLimitMap M r) :=
    awayDirectLimit_isLocalizedModule M r
  apply IsLocalizedModule.iso_symm_apply'
  exact pow_smul_of_eq_awayDirectLimitMap M r n x

end Module

end
