/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Perfectoid.SemistablePeriodRing

/-! Tests for Fontaine's rings `B_cris^+ ⊆ B_cris ⊆ B_st` inside `B_dR`: the inclusions, the
periods they contain, Galois stability, the action on `log [p̃]`, the independence of the choices,
Fontaine's Lemme 4.3.1 and the transcendence of `log [p̃]` over `B_cris`, and the isomorphism
`B_cris[X] ≃ B_st`, `X ↦ log [p̃]`. -/

open Polynomial PadicComplexInt

variable (p : ℕ) [Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

-- The inclusions `B_cris^+ ⊆ B_cris ⊆ B_st` and `B_cris ⊆ B_max`.
example : bCrisPlus p ≤ bSt p := (bCrisPlus_le_bCris p).trans (bCris_le_bSt p)

example : bCris p ≤ bMax p := bCris_le_bMax p

-- `t = log [ε]` and `1/t` lie in `B_cris`, and `log [p̃]` lies in `B_st`.
example : algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)) ∈ bCris p :=
  bCrisPlus_le_bCris p (algebraMap_mem_bCrisPlus p (logTeichmuller_mem_aCris p _))

example : (algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)))⁻¹ ∈ bCris p :=
  inv_logTeichmuller_epsilon_mem_bCris p

example : algebraMap 𝔹⁺ 𝔹 (logPTilde p) ∈ bSt p := algebraMap_logPTilde_mem_bSt p

-- `B_cris` and `B_st` are Galois stable, and `σ(log [p̃]) - log [p̃] ∈ B_cris`.
example (σ : Gal(PadicAlgCl p/ℚ_[p])) {x : 𝔹} (hx : x ∈ bCris p) :
    galoisBDeRham p σ x ∈ bCris p :=
  galoisBDeRham_mem_bCris p σ hx

example (σ : Gal(PadicAlgCl p/ℚ_[p])) :
    galoisBDeRham p σ (algebraMap 𝔹⁺ 𝔹 (logPTilde p)) ∈ bSt p :=
  galoisBDeRham_mem_bSt p σ (algebraMap_logPTilde_mem_bSt p)

example (σ : Gal(PadicAlgCl p/ℚ_[p])) :
    galoisBDeRham p σ (algebraMap 𝔹⁺ 𝔹 (logPTilde p)) - algebraMap 𝔹⁺ 𝔹 (logPTilde p) ∈
      bCris p := by
  rw [galoisBDeRham_algebraMap_logPTilde, add_sub_cancel_left]
  exact bCrisPlus_le_bCris p (algebraMap_mem_bCrisPlus p (logTeichmuller_mem_aCris p _))

-- `B_cris` and `B_st` do not depend on the choice of generators: for instance they are the
-- same for a unit multiple of `ξ` and for `ε` itself.
example (c : 𝔸ˣ) (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) =
    Ideal.span {xi p * (c : 𝔸)}) :
    bSt p = Algebra.adjoin ℚ_[p] (algebraMap 𝔹⁺ 𝔹 '' (toBDeRhamPlus hgen).range ∪
      {(algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)))⁻¹} ∪
        {algebraMap 𝔹⁺ 𝔹 (logPTilde p)}) :=
  bSt_eq_adjoin_of_generators p hgen (untilt_epsilon p)
    (isPrimitiveRoot_untilt_frobeniusEquiv_symm_epsilon p)

-- Fontaine's Lemme 4.3.1: `log [p̃]` is not in the fraction field of `B_cris`; in particular
-- `log [p̃] ∉ B_cris`.
example {a b : 𝔹} (ha : a ∈ bCris p) (hb : b ∈ bCris p) (ha0 : a ≠ 0) :
    a * algebraMap 𝔹⁺ 𝔹 (logPTilde p) ≠ b :=
  mul_algebraMap_logPTilde_ne_of_mem_bCris p ha hb ha0

example : algebraMap 𝔹⁺ 𝔹 (logPTilde p) ∉ bCris p := fun h =>
  mul_algebraMap_logPTilde_ne_of_mem_bCris p (Subalgebra.one_mem _) h one_ne_zero (one_mul _)

-- `log [p̃]` is transcendental over `B_cris`: no nonzero polynomial over `B_cris` vanishes at it.
example (P : (bCris p)[X]) (hP : aeval (algebraMap 𝔹⁺ 𝔹 (logPTilde p)) P = 0) : P = 0 :=
  aeval_logPTilde_bCris_injective p (hP.trans (map_zero _).symm)

-- `B_st` is a polynomial ring over `B_cris`, with `X ↦ log [p̃]`.
example : (bCrisPolynomialEquiv p X : 𝔹) = algebraMap 𝔹⁺ 𝔹 (logPTilde p) :=
  coe_bCrisPolynomialEquiv_X p

example (a : bCris p) :
    (bCrisPolynomialEquiv p (C a * X + 1) : 𝔹) = a * algebraMap 𝔹⁺ 𝔹 (logPTilde p) + 1 := by
  rw [map_add, map_mul, map_one, Subalgebra.coe_add, Subalgebra.coe_mul,
    coe_bCrisPolynomialEquiv_C, coe_bCrisPolynomialEquiv_X, Subalgebra.coe_one]
