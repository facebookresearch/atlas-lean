/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Perfectoid.SemistableFrobenius

/-! Tests for the Frobenius of Fontaine's rings `B_cris^+`, `B_cris` and `B_st` and the monodromy
operator of `B_st`: each Frobenius is a `ℚ_[p]`-algebra map extending the previous one and
commuting with the Galois action, `φ(t) = p t` in `B_cris`, `φ(X) = p X` in `B_st`, and
`N = -d/dX` is the `B_cris`-derivation with `N(X) = -1`, satisfies `N φ = p φ N` and commutes with
the Galois action. -/

open Polynomial PadicComplexInt

variable (p : ℕ) [Fact p.Prime]

local notation "𝔸cris" => CrystallineCompletion p (xi p)

-- `B_cris^+`: the Frobenius extends that of `A_cris`, fixes `ℚ_[p]` and commutes with Galois.
example (x : 𝔸cris) :
    BCrisPlus.frobenius p (algebraMap 𝔸cris (BCrisPlus p) x) =
      algebraMap 𝔸cris (BCrisPlus p) (frobeniusCrystallineCompletion p (xi p) x) :=
  BCrisPlus.frobenius_algebraMap p x

example (r : ℚ_[p]) :
    BCrisPlus.frobenius p (algebraMap ℚ_[p] (BCrisPlus p) r) = algebraMap ℚ_[p] (BCrisPlus p) r :=
  (BCrisPlus.frobenius p).commutes r

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : BCrisPlus p) :
    BCrisPlus.frobenius p (BCrisPlus.galois p σ x) =
      BCrisPlus.galois p σ (BCrisPlus.frobenius p x) :=
  BCrisPlus.frobenius_galois p σ x

-- On `W(𝓞_ℂ_[p]♭)`, the Frobenius of `A_cris` is the Witt vector Frobenius.
example (a : WittVector p (PreTilt 𝓞_ℂ_[p] p)) :
    frobeniusCrystallineCompletion p (xi p) (BCrisPlus.ofWittVector p a) =
      BCrisPlus.ofWittVector p (WittVector.frobenius a) :=
  BCrisPlus.frobeniusCrystallineCompletion_ofWittVector p a

-- `B_cris`: `φ(t) = p t`, the Frobenius extends that of `B_cris^+` and commutes with Galois.
example :
    BCris.frobenius p
        (algebraMap 𝔸cris (BCris p) (logTeichmullerCrystalline p (untilt_epsilon p))) =
      (p : BCris p) * algebraMap 𝔸cris (BCris p) (logTeichmullerCrystalline p (untilt_epsilon p)) :=
  BCris.frobenius_algebraMap_logTeichmullerCrystalline p

example (x : BCrisPlus p) :
    BCris.frobenius p (algebraMap (BCrisPlus p) (BCris p) x) =
      algebraMap (BCrisPlus p) (BCris p) (BCrisPlus.frobenius p x) :=
  BCris.frobenius_algebraMap p x

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : BCris p) :
    BCris.frobenius p (BCris.galois p σ x) = BCris.galois p σ (BCris.frobenius p x) :=
  BCris.frobenius_galois p σ x

-- `φ(1/t) = 1/(p t)`: the Frobenius of `t⁻¹ ∈ B_cris` is inverse to `p t`.
example :
    BCris.frobenius p (IsLocalization.Away.invSelf (S := BCris p)
        (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p)))) *
      ((p : BCris p) *
        algebraMap 𝔸cris (BCris p) (logTeichmullerCrystalline p (untilt_epsilon p))) = 1 := by
  rw [← BCris.frobenius_algebraMap_logTeichmullerCrystalline, ← map_mul,
    IsScalarTower.algebraMap_apply 𝔸cris (BCrisPlus p) (BCris p), mul_comm,
    IsLocalization.Away.mul_invSelf, map_one]

-- `B_st`: `φ(X) = p X`, `φ` is the Frobenius of `B_cris` on coefficients, and commutes with Galois.
example : BSt.frobenius p X = (p : BSt p) * X :=
  BSt.frobenius_X p

example (b : BCris p) : BSt.frobenius p (C b) = C (BCris.frobenius p b) :=
  BSt.frobenius_C p b

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : BSt p) :
    BSt.frobenius p (BSt.galois p σ x) = BSt.galois p σ (BSt.frobenius p x) :=
  BSt.frobenius_galois p σ x

-- `φ(X^2) = p^2 X^2`.
example : BSt.frobenius p (X ^ 2) = (p : BSt p) ^ 2 * X ^ 2 := by
  rw [map_pow, BSt.frobenius_X, mul_pow]

-- The monodromy operator: `N(X) = -1`, `N(X^2) = -2 X`, `N` kills `B_cris`, and it is the
-- unique `B_cris`-derivation with `N(X) = -1`.
example : BSt.monodromy p X = -1 :=
  BSt.monodromy_X p

example : BSt.monodromy p (X ^ 2) = -(2 * X) := by
  rw [BSt.monodromy_apply, derivative_X_pow]
  norm_num
  rw [map_ofNat]

example (b : BCris p) : BSt.monodromy p (C b) = 0 :=
  BSt.monodromy_C p b

example (D : Derivation (BCris p) (BSt p) (BSt p)) (h : D X = -1) : D = BSt.monodromy p :=
  BSt.eq_monodromy p h

-- `N φ = p φ N`, checked on `X` directly, and `N` commutes with the Galois action.
example (P : BSt p) :
    BSt.monodromy p (BSt.frobenius p P) = (p : BSt p) * BSt.frobenius p (BSt.monodromy p P) :=
  BSt.monodromy_frobenius p P

example :
    BSt.monodromy p (BSt.frobenius p X) = (p : BSt p) * BSt.frobenius p (BSt.monodromy p X) := by
  rw [BSt.frobenius_X, BSt.monodromy_X, map_neg, map_one, Derivation.leibniz, BSt.monodromy_X,
    ← map_natCast C p, BSt.monodromy_C, smul_eq_mul, smul_zero, add_zero]

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (P : BSt p) :
    BSt.monodromy p (BSt.galois p σ P) = BSt.galois p σ (BSt.monodromy p P) :=
  BSt.monodromy_galois p σ P
