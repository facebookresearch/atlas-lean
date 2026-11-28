/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Perfectoid.SemistablePeriodRingAbstract

/-! Tests for Fontaine's abstract rings `B_cris^+ = A_cris[1/p]`, `B_cris = B_cris^+[1/t]` and
`B_st = B_cris[X]`: their embeddings into `B_dR` are injective and Galois equivariant, with images
`bCrisPlus`, `bCris` and `bSt`; `σ(X) = X + log [u_σ]` in `B_st`, mapping to
`σ(log [p̃]) = log [p̃] + log [u_σ]`; and the isomorphism `B_st ≃ bSt` sends `X` to `log [p̃]`. -/

open Polynomial PadicComplexInt

variable (p : ℕ) [Fact p.Prime]

local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p
local notation "𝔸cris" => CrystallineCompletion p (xi p)

-- The three embeddings into `B_dR` are injective.
example : Function.Injective (BCrisPlus.toBDeRham p) := BCrisPlus.toBDeRham_injective p

example : Function.Injective (BCris.toBDeRham p) := BCris.toBDeRham_injective p

example : Function.Injective (BSt.toBDeRham p) := BSt.toBDeRham_injective p

-- A polynomial over `B_cris` whose value at `log [p̃]` vanishes is zero.
example (P : BSt p) (hP : BSt.toBDeRham p P = 0) : P = 0 :=
  (injective_iff_map_eq_zero _).mp (BSt.toBDeRham_injective p) P hP

-- The embedding of `B_st` is the evaluation at `log [p̃]`.
example (P : BSt p) : BSt.toBDeRham p P =
    eval₂ (BCris.toBDeRham p : BCris p →+* 𝔹) (algebraMap 𝔹⁺ 𝔹 (logPTilde p)) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, hP, hQ, eval₂_add]
  | monomial n b =>
    rw [eval₂_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, BSt.toBDeRham_C,
      BSt.toBDeRham_X, RingHom.coe_coe]

-- The three embeddings are Galois equivariant.
example (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BCrisPlus p) :
    BCrisPlus.toBDeRham p (BCrisPlus.galois p σ x) =
      galoisBDeRham p σ (BCrisPlus.toBDeRham p x) :=
  BCrisPlus.toBDeRham_galois p σ x

example (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BCris p) :
    BCris.toBDeRham p (BCris.galois p σ x) = galoisBDeRham p σ (BCris.toBDeRham p x) :=
  BCris.toBDeRham_galois p σ x

example (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BSt p) :
    BSt.toBDeRham p (BSt.galois p σ x) = galoisBDeRham p σ (BSt.toBDeRham p x) :=
  BSt.toBDeRham_galois p σ x

-- On `A_cris`, the action and the embedding are those of `A_cris`.
example (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : 𝔸cris) :
    BCrisPlus.galois p σ (algebraMap 𝔸cris (BCrisPlus p) x) =
      algebraMap 𝔸cris (BCrisPlus p)
        (galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ x) :=
  BCrisPlus.galois_algebraMap p σ x

example (x : 𝔸cris) :
    BCris.toBDeRham p (algebraMap (BCrisPlus p) (BCris p) (algebraMap 𝔸cris (BCrisPlus p) x)) =
      algebraMap 𝔹⁺ 𝔹 (toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p) x) := by
  rw [BCris.toBDeRham_algebraMap, BCrisPlus.toBDeRham_algebraMap]

-- `t = log [ε]` maps to `log [ε]`, a nonzero element of `B_dR`.
example : BCris.toBDeRham p (algebraMap (BCrisPlus p) (BCris p)
    (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p)))) ≠ 0 := by
  rw [BCris.toBDeRham_algebraMap, BCrisPlus.toBDeRham_algebraMap,
    toBDeRhamPlus_logTeichmullerCrystalline]
  exact (map_ne_zero_iff _ (algebraMap_bDeRham_injective p)).mpr
    (logTeichmuller_ne_zero p _ (epsilon_ne_one p))

-- `σ(X) = X + log [u_σ]` in `B_st`, and its image is `σ(log [p̃]) = log [p̃] + log [u_σ]`.
example (σ : Gal(PadicAlgCl p/ℚ_[p])) :
    BSt.galois p σ X = X + C (algebraMap 𝔸cris (BCris p)
      (logTeichmullerCrystalline p (untilt_kummerUnit p σ))) :=
  BSt.galois_X p σ

example (σ : Gal(PadicAlgCl p/ℚ_[p])) (b : BCris p) :
    BSt.galois p σ (C b) = C (BCris.galois p σ b) :=
  BSt.galois_C p σ b

example (σ : Gal(PadicAlgCl p/ℚ_[p])) :
    BSt.toBDeRham p (BSt.galois p σ X) =
      algebraMap 𝔹⁺ 𝔹 (logPTilde p) +
        algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_kummerUnit p σ)) := by
  rw [BSt.toBDeRham_galois, BSt.toBDeRham_X, galoisBDeRham_algebraMap_logPTilde]

-- The isomorphism `B_st ≃ bSt` sends `X` to `log [p̃]` and is the embedding on `B_cris`.
example : (BSt.equivBSt p X : 𝔹) = algebraMap 𝔹⁺ 𝔹 (logPTilde p) := BSt.coe_equivBSt_X p

example (b : BCris p) : (BSt.equivBSt p (C b) : 𝔹) = BCris.equivBCris p b := by
  rw [BSt.coe_equivBSt, BSt.toBDeRham_C, BCris.coe_equivBCris]

-- The images are `bCrisPlus`, `bCris` and `bSt`.
example : (BCrisPlus.toBDeRham p).range = bCrisPlus p := BCrisPlus.range_toBDeRham p

example : (BCris.toBDeRham p).range = bCris p := BCris.range_toBDeRham p

example : (BSt.toBDeRham p).range = bSt p := BSt.range_toBDeRham p

-- Hence `bSt` is Galois stable.
example (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BSt p) :
    galoisBDeRham p σ (BSt.toBDeRham p x) ∈ bSt p := by
  rw [← BSt.toBDeRham_galois, ← BSt.range_toBDeRham]
  exact AlgHom.mem_range_self _ _
