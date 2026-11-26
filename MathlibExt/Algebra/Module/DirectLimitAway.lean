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

For a module over a commutative semiring, form the sequential system whose successor map is
multiplication by r. The transition from stage i to j is multiplication by r^{j−i}.

In its direct limit, moving a representative from stage n to n+1 is inverse to multiplication
by r. The stage-zero map therefore exhibits localization away from r, and the canonical linear
equivalence sends a stage-n class of x to x/r^n. The semiring and module carrier universes are
independent.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module

variable {R : Type u} [CommSemiring R]
  (M : Type v) [AddCommMonoid M] [Module R M]

/-- The power transition in an away-localization system.

For i≤j, map x to r^{j−i}·x. -/
def awayTransition (r : R) (i j : ℕ) (_ : i ≤ j) : M →ₗ[R] M :=
  LinearMap.lsmul R M (r ^ (j - i))

/-- The directed-system laws of power transitions.

The identity power and additive exponent law give the transition identities and composition. -/
instance awayTransition_directedSystem (r : R) :
    DirectedSystem (fun _ : ℕ ↦ M) (awayTransition M r · · ·) where
  map_self i x := by
    simp [awayTransition]
  map_map {k j i} hij hjk x := by
    change r ^ (k - j) • (r ^ (j - i) • x) = r ^ (k - i) • x
    rw [← mul_smul, ← pow_add]
    congr 2
    omega

/-- The direct limit of repeated scalar multiplication.

Take the module direct limit of the constant sequence with successor map r·−. -/
abbrev AwayDirectLimit (r : R) :=
  Module.DirectLimit (fun _ : ℕ ↦ M) (awayTransition M r)

/-- The stage-zero map to the away direct limit.

Send x∈M to its direct-limit class at stage zero. -/
def awayDirectLimitMap (r : R) : M →ₗ[R] AwayDirectLimit M r :=
  Module.DirectLimit.of R ℕ (fun _ : ℕ ↦ M)
    (awayTransition M r) 0

/-- The stage-increase operator on the away direct limit.

Send the class of x at stage n to its class at stage n+1. -/
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

/-- The shift formula on a direct-limit representative.

The stage-n representative is sent to the same x at stage n+1. -/
@[simp]
theorem awayShift_of (r : R) (n : ℕ) (x : M) :
    awayShift M r
        (Module.DirectLimit.of R ℕ (fun _ : ℕ ↦ M)
          (awayTransition M r) n x) =
      Module.DirectLimit.of R ℕ (fun _ : ℕ ↦ M)
        (awayTransition M r) (n + 1) x :=
  by simp [awayShift]

/-- Multiplication after stage increase is the identity.

For every direct-limit element z, r·awayShift(z)=z. -/
theorem r_smul_awayShift (r : R) (z : AwayDirectLimit M r) :
    r • awayShift M r z = z := by
  induction z using Module.DirectLimit.induction_on with
  | _ n x =>
      rw [awayShift_of, ← map_smul]
      simpa [awayTransition, pow_one] using Module.DirectLimit.of_f
        (R := R) (G := fun _ : ℕ ↦ M)
        (f := awayTransition M r) (i := n) (j := n + 1)
        (hij := Nat.le_succ n) (x := x)

/-- Stage increase after multiplication is the identity.

For every z, awayShift(r·z)=z. -/
theorem awayShift_r_smul (r : R) (z : AwayDirectLimit M r) :
    awayShift M r (r • z) = z := by
  induction z using Module.DirectLimit.induction_on with
  | _ n x =>
      rw [← map_smul, awayShift_of]
      simpa [awayTransition, pow_one] using Module.DirectLimit.of_f
        (R := R) (G := fun _ : ℕ ↦ M)
        (f := awayTransition M r) (i := n) (j := n + 1)
        (hij := Nat.le_succ n) (x := x)

/-- The scalar r acts invertibly on the direct limit.

Its module endomorphism is a unit, with inverse awayShift. -/
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

/-- A power clears the stage of a direct-limit representative.

Multiplying the stage-n class of x by r^n gives its stage-zero class. -/
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

/-- The stage-zero map has the away-localization universal property.

The sequential direct limit is a localized module at the powers of r. -/
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

/-- The linear equivalence between the direct limit and away localization.

Identify the two localized-module models through their universal properties. -/
noncomputable def awayDirectLimitLinearEquiv (r : R) :
    AwayDirectLimit M r ≃ₗ[R] LocalizedModule.Away r M := by
  let _ : IsLocalizedModule.Away r (awayDirectLimitMap M r) :=
    awayDirectLimit_isLocalizedModule M r
  exact (IsLocalizedModule.iso (Submonoid.powers r)
    (awayDirectLimitMap M r)).symm

/-- The direct-limit equivalence on a stage representative.

The class of x at stage n maps to the fraction x/r^n. -/
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
