/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd.lean`
and
`P2M/Sol/S_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd.lean`
and
`Definitions/Def_LanglandsTunnell_RankinSelbergEuler.lean`
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

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import MathlibExt.NumberTheory.NumberField.AbsNormSummable

@[expose] public section

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain NumberField

namespace NumberField

variable (F : Type*) [Field F] [NumberField F] {K : Type*} [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type*} [CommRing R]

/-- The primes of `𝓞 K` lying over a given prime `p` of `𝓞 F`. -/
def primeFibre (p : HeightOneSpectrum (𝓞 F)) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔓 | 𝔓.under (𝓞 F) = p}

@[simp] theorem mem_primeFibre (p : HeightOneSpectrum (𝓞 F)) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    𝔓 ∈ primeFibre F p ↔ 𝔓.under (𝓞 F) = p :=
  Iff.rfl

/-- The local factor at `𝔓` of the induced Euler polynomial, with the
inertia degree of `𝔓` over its underlying prime as the exponent of `X`. -/
def inducedFactor (c : HeightOneSpectrum (𝓞 K) → R) (𝔓 : HeightOneSpectrum (𝓞 K)) : R[X] :=
  C 1 - C (c 𝔓) * X ^ ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)

/-- The Euler polynomial at `p` induced from coefficients `c` on the primes
of the extension: the finite product of the local factors over the fibre. -/
def inducedEulerPoly (c : HeightOneSpectrum (𝓞 K) → R) (p : HeightOneSpectrum (𝓞 F)) : R[X] :=
  ∏ᶠ 𝔓 ∈ primeFibre F p, inducedFactor F c 𝔓

end NumberField

namespace NumberField

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)]

private theorem algebraMap_injective : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hmem := Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) (𝓞 K)))
  have hnz : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) (𝓞 K))) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hne
  rw [RingHom.mem_ker, map_natCast] at hmem
  exact hnz (Nat.cast_eq_zero.mp hmem)

private theorem isTorsionFree : Module.IsTorsionFree (𝓞 F) (𝓞 K) := by
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_injective F K)

variable [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

private theorem primeFibre_finite (p : HeightOneSpectrum (𝓞 F)) :
    (primeFibre (K := K) F p).Finite := by
  haveI := isTorsionFree F K
  haveI : p.asIdeal.IsMaximal := p.isPrime.isMaximal p.ne_bot
  have hfin : (Ideal.primesOver p.asIdeal (𝓞 K)).Finite :=
    IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)
  refine (hfin.preimage (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) ?_).subset ?_
  · intro a _ b _ hab
    exact HeightOneSpectrum.ext hab
  · intro 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    show 𝔓.asIdeal ∈ Ideal.primesOver p.asIdeal (𝓞 K)
    refine ⟨𝔓.isPrime, ⟨?_⟩⟩
    rw [← h𝔓]
    rfl

private theorem absNorm_eq (𝔓 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔓.asIdeal =
      Ideal.absNorm (𝔓.under (𝓞 F)).asIdeal ^
        ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
  haveI : Module.Finite (𝓞 F) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 K)
  haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 F)).asIdeal := ⟨rfl⟩
  exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal (𝔓.under (𝓞 F)).asIdeal
    (𝔓.under (𝓞 F)).isPrime (𝔓.under (𝓞 F)).ne_bot

private theorem eval_inducedFactor (c : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (inducedFactor F c 𝔓).eval (((Ideal.absNorm (𝔓.under (𝓞 F)).asIdeal : ℕ) : ℂ) ^ (-s)) =
      1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s) := by
  simp only [inducedFactor, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  congr 2
  rw [absNorm_eq F K 𝔓, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    ← Complex.cpow_nat_mul]

private theorem factor_eq (c : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (p : HeightOneSpectrum (𝓞 F)) :
    ((inducedEulerPoly F c p).eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
      ∏ 𝔓 ∈ (primeFibre_finite F K p).toFinset,
        (1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  unfold inducedEulerPoly
  rw [finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite F K p), eval_prod,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
  rw [Set.Finite.mem_toFinset, mem_primeFibre] at h𝔓
  rw [← h𝔓, eval_inducedFactor F K c s 𝔓]

/-- Regrouping an Euler product: if the product over the primes of `𝓞 K` of
the inverse local factors `1 - c 𝔓 * N𝔓 ^ (-s)` converges to `Z`, then so does
the product over the primes of `𝓞 F` of the inverse induced Euler polynomials
evaluated at `Np ^ (-s)`. -/
public theorem hasProd_inv_eval_inducedEulerPoly_of_hasProd
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (s Z : ℂ)
    (h : HasProd (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      (1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) Z) :
    HasProd (fun p : HeightOneSpectrum (𝓞 F) =>
      ((inducedEulerPoly F c p).eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) Z := by
  classical
  let e := Equiv.sigmaFiberEquiv (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 F))
  have h2 := (e.hasProd_iff).mpr h
  refine HasProd.sigma h2 fun p => ?_
  haveI : Finite {𝔓 : HeightOneSpectrum (𝓞 K) // 𝔓.under (𝓞 F) = p} :=
    (primeFibre_finite F K p).to_subtype
  haveI := Fintype.ofFinite {𝔓 : HeightOneSpectrum (𝓞 K) // 𝔓.under (𝓞 F) = p}
  rw [factor_eq F K c s p,
    Finset.prod_subtype (primeFibre_finite F K p).toFinset
      (p := fun 𝔓 => 𝔓.under (𝓞 F) = p)
      (fun 𝔓 => by rw [Set.Finite.mem_toFinset, mem_primeFibre])]
  exact hasProd_fintype _

end NumberField

end
