/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_
of_finrank_prime.lean`
and
`P2M/Sol/S_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_
of_finrank_prime.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Inertia

@[expose] public section

open NumberField

namespace Ideal

/-- In a Galois extension of number fields of prime degree, a nonzero maximal
ideal is split, inert, or totally ramified.

This follows from `g * (e * f) = [L : K]` together with primality of the
degree: one of `g`, `e`, `f` equals the degree and the other two equal `1`. -/
public theorem ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (hℓ : (Module.finrank K L).Prime)
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver p] :
    ((p.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = Module.finrank K L ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = Module.finrank K L) := by
  classical
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 L) Gal(L/K)
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p) (q := P) hp,
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := p) (P := P),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L] at hmain
  set g := (p.primesOver (𝓞 L)).ncard with hg
  set e := p.ramificationIdx' P with he
  set f := p.inertiaDeg' P with hf
  set ℓ := Module.finrank K L with hℓdef
  have hprime : ℓ.Prime := hℓ
  have hprod : g * (e * f) = ℓ := hmain
  have hdvd_g : g ∣ ℓ := ⟨e * f, hprod.symm⟩
  rcases (Nat.dvd_prime hprime).mp hdvd_g with hg1 | hgl
  · have hef : e * f = ℓ := by simpa [hg1] using hprod
    have hdvd_e : e ∣ ℓ := ⟨f, hef.symm⟩
    rcases (Nat.dvd_prime hprime).mp hdvd_e with he1 | hel
    · have hfl : f = ℓ := by simpa [he1] using hef
      exact Or.inr (Or.inr ⟨hg1, he1, hfl⟩)
    · have hf1 : f = 1 := by
        have h : ℓ * f = ℓ * 1 := by rw [mul_one, ← hel]; exact hel ▸ hef
        exact Nat.eq_of_mul_eq_mul_left hprime.pos h
      exact Or.inr (Or.inl ⟨hg1, hel, hf1⟩)
  · have hef : e * f = 1 := by
      have h : ℓ * (e * f) = ℓ * 1 := by rw [mul_one]; exact hgl ▸ hprod
      exact Nat.eq_of_mul_eq_mul_left hprime.pos h
    exact Or.inl ⟨hgl, Nat.eq_one_of_mul_eq_one_right hef, Nat.eq_one_of_mul_eq_one_left hef⟩

end Ideal
