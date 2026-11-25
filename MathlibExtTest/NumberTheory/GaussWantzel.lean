/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussWantzel
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for the Gauss–Wantzel theorem -/

open MathlibExt.NumberTheory.GaussWantzelWanted.NumberTheory.GaussWantzel

-- The smallest admissible polygon.
example : IsConstructible (Real.cos (2 * Real.pi / 3)) := by
  apply (gauss_wantzel_constructible_polygon 3 (hn := by decide)).mpr
  refine ⟨by decide, fun p hp hdiv ↦ ?_⟩
  have hp3 := (Nat.prime_three.dvd_iff_eq hp.ne_one).mp hdiv
  subst p
  exact ⟨Or.inr ⟨Nat.prime_three, 0, rfl⟩, by decide⟩

-- The prime 2 may occur with multiplicity.
example : IsConstructible (Real.cos (2 * Real.pi / 8)) := by
  apply (gauss_wantzel_constructible_polygon 8 (by decide)).mpr
  refine ⟨by decide, fun p hp hdiv ↦ ?_⟩
  change p ∣ 2 ^ 3 at hdiv
  have hp2 := ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp (hp.dvd_of_dvd_pow hdiv)).symm
  subst p
  exact ⟨Or.inl rfl, by decide⟩

-- A product of two distinct Fermat primes.
example : IsConstructible (Real.cos (2 * Real.pi / 15)) := by
  apply (gauss_wantzel_constructible_polygon 15 (by decide)).mpr
  refine ⟨by decide, fun p hp hdiv ↦ ?_⟩
  change p ∣ 3 * 5 at hdiv
  rcases hp.dvd_mul.mp hdiv with h3 | h5
  · have hp3 := (Nat.prime_three.dvd_iff_eq hp.ne_one).mp h3
    subst p
    exact ⟨Or.inr ⟨Nat.prime_three, 0, rfl⟩, by decide⟩
  · have hp5 := (Nat.prime_five.dvd_iff_eq hp.ne_one).mp h5
    subst p
    exact ⟨Or.inr ⟨Nat.prime_five, 1, rfl⟩, by decide⟩

-- An odd Fermat prime may only occur once.
example : ¬ IsConstructible (Real.cos (2 * Real.pi / 9)) := by
  intro h
  have h9 := (gauss_wantzel_constructible_polygon 9 (by decide)).mp h
  exact (h9.2 3 Nat.prime_three (by decide)).2 (by decide) (by decide)

-- The heptagon has a prime side count that is not a Fermat number.
example : ¬ IsConstructible (Real.cos (2 * Real.pi / 7)) := by
  intro h
  have h7 := (gauss_wantzel_constructible_polygon 7 (by decide)).mp h
  obtain ⟨-, k, hk⟩ := (h7.2 7 (by norm_num) (by decide)).1.resolve_left (by decide)
  rcases k with _ | _ | k
  · norm_num at hk
  · norm_num at hk
  · have hle := Nat.fermatNumber_mono (show 2 ≤ k + 2 by omega)
    rw [Nat.fermatNumber_two, ← hk] at hle
    omega

-- The square-root constructor also respects the real square root of negative inputs.
example : IsConstructible (Real.sqrt (-1)) := by
  simpa using (IsConstructible.base (-1)).sqrt
