/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

@[expose] public section

namespace MetaMathlibExt

open Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

/-
Source: Peng Gao and Liangyi Zhao, "Ratios conjecture of cubic L-functions of prime
moduli," arXiv:2311.08626v3, Indagationes Mathematicae. Definition of cubic residue
symbol leg {·}{·}_3 for K = Q(ω), O_K = Z[ω], ω = hZeta.toInteger.
Bytes [25829,26379) of RatioconjcubicHeckeLfcnsPrim_031.tex.
-/

public abbrev omega {zeta : K} (hZeta : IsPrimitiveRoot zeta 3) :
    NumberField.RingOfIntegers K :=
  hZeta.toInteger

omit [IsCyclotomicExtension {3} ℚ K] in
public lemma exists_cubic_root_eq_pow
    {zeta : K} [IsCyclotomicExtension {3} ℚ K]
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
    (ha : a ∉ P) :
    ∃ c : NumberField.RingOfIntegers K,
      c ∈ ({(1 : NumberField.RingOfIntegers K),
        omega hZeta, omega hZeta ^ 2} : Set _) ∧
      Ideal.Quotient.mk P c =
        Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3) := by
  classical
  have : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPbot
  let _ : Field (NumberField.RingOfIntegers K ⧸ P) :=
    Ideal.Quotient.field P
  have : Finite (NumberField.RingOfIntegers K ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne P)
  let _ : Fintype (NumberField.RingOfIntegers K ⧸ P) :=
    Fintype.ofFinite _
  have hAbsNeOne : Ideal.absNorm P ≠ 1 := by
    intro h
    have hTop : P = ⊤ := (Ideal.absNorm_eq_one_iff (I := P)).mp h
    exact hPprime.ne_top hTop
  have hCoprime : Nat.Coprime (Ideal.absNorm P) 3 := hNormCoprime
  have hPrim : IsPrimitiveRoot
      (Ideal.Quotient.mk P (omega (K := K) hZeta)) 3 :=
    hZeta.toInteger_isPrimitiveRoot.idealQuotient_mk hAbsNeOne hCoprime
  have hCardEq :
      Fintype.card (NumberField.RingOfIntegers K ⧸ P) =
        Ideal.absNorm P := by
    calc Fintype.card (NumberField.RingOfIntegers K ⧸ P)
        = Nat.card (NumberField.RingOfIntegers K ⧸ P) :=
          Fintype.card_eq_nat_card
      _ = Submodule.cardQuot P := (Submodule.cardQuot_apply (S := P)).symm
      _ = Ideal.absNorm P := (Ideal.absNorm_apply (I := P)).symm
  have hMkOmegaNeZero : Ideal.Quotient.mk P (omega hZeta) ≠ 0 := by
    intro hEq
    have hMem : (omega hZeta) ∈ P :=
      (Ideal.Quotient.eq_zero_iff_mem).mp hEq
    have hpow1 : (Ideal.Quotient.mk P (omega hZeta)) ^ 3 = 1 :=
      hPrim.pow_eq_one
    have : (0 : NumberField.RingOfIntegers K ⧸ P) ^ (3 : ℕ) = 1 := by
      rw [← hEq, hpow1]
    simp at this
  have hMkANeZero : Ideal.Quotient.mk P a ≠ 0 := by
    intro hEq
    rw [Ideal.Quotient.eq_zero_iff_mem] at hEq
    exact ha hEq
  have hPowCardOmega :
      (Ideal.Quotient.mk P (omega hZeta)) ^
        (Fintype.card (NumberField.RingOfIntegers K ⧸ P) - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one
      (Ideal.Quotient.mk P (omega hZeta)) hMkOmegaNeZero
  have hDvd :
      3 ∣ Fintype.card (NumberField.RingOfIntegers K ⧸ P) - 1 :=
    hPrim.dvd_of_pow_eq_one _ hPowCardOmega
  rw [hCardEq] at hDvd
  have hPowA :
      (Ideal.Quotient.mk P a) ^
        (Fintype.card (NumberField.RingOfIntegers K ⧸ P) - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one
      (Ideal.Quotient.mk P a) hMkANeZero
  rw [hCardEq] at hPowA
  have hThreeDvd : 3 ∣ Ideal.absNorm P - 1 := hDvd
  have hExp :
      3 * ((Ideal.absNorm P - 1) / 3) = Ideal.absNorm P - 1 :=
    Nat.mul_div_cancel' hThreeDvd
  have hEulerCube :
      (Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3)) ^ 3 = 1 := by
    calc (Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3)) ^ 3
        = (Ideal.Quotient.mk P a) ^
            (((Ideal.absNorm P - 1) / 3) * 3) := by rw [← pow_mul]
      _ = (Ideal.Quotient.mk P a) ^ (3 * ((Ideal.absNorm P - 1) / 3)) := by
          rw [Nat.mul_comm]
      _ = (Ideal.Quotient.mk P a) ^ (Ideal.absNorm P - 1) := by rw [hExp]
      _ = 1 := hPowA
  obtain ⟨b, hb⟩ :=
    Ideal.Quotient.mk_surjective
      (I := P) (Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3))
  have hbCube : Ideal.Quotient.mk P (b ^ 3 - 1) = 0 := by
    rw [map_sub, map_pow, hb, map_one, sub_eq_zero.mpr hEulerCube]
  have hCubeEq :
      b ^ 3 - 1 = (b - 1) * (b - omega hZeta) * (b - omega hZeta ^ 2) :=
    IsCyclotomicExtension.Rat.Three.cube_sub_one_eq_mul hZeta b
  have hMkProdZero :
      Ideal.Quotient.mk P ((b - 1) * (b - omega hZeta) *
        (b - omega hZeta ^ 2)) = 0 := by
    rw [← hCubeEq, hbCube]
  rw [map_mul, map_mul] at hMkProdZero
  have hOr :
      Ideal.Quotient.mk P (b - 1) = 0 ∨
        Ideal.Quotient.mk P (b - omega hZeta) = 0 ∨
          Ideal.Quotient.mk P (b - omega hZeta ^ 2) = 0 := by
    have h1 :
        Ideal.Quotient.mk P (b - 1) *
            Ideal.Quotient.mk P (b - omega hZeta) *
              Ideal.Quotient.mk P (b - omega hZeta ^ 2) = 0 := hMkProdZero
    rcases mul_eq_zero.mp h1 with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1' | h2'
      · left; exact h1'
      · right; left; exact h2'
    · right; right; exact h3
  rcases hOr with h1 | h2 | h3
  · refine ⟨1, by simp, ?_⟩
    have hmk1 : Ideal.Quotient.mk P (b - 1) = 0 := h1
    rw [map_sub, sub_eq_zero] at hmk1
    rw [← hb, hmk1]
  · refine ⟨omega hZeta, by simp, ?_⟩
    have hmk2 : Ideal.Quotient.mk P (b - omega hZeta) = 0 := h2
    rw [map_sub, sub_eq_zero] at hmk2
    rw [← hb, hmk2]
  · refine ⟨omega hZeta ^ 2, by simp, ?_⟩
    have hmk3 : Ideal.Quotient.mk P (b - omega hZeta ^ 2) = 0 := h3
    rw [map_sub, sub_eq_zero] at hmk3
    rw [← hb, hmk3]

open Classical in
public noncomputable def primeIdealValidCubicSymbol
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
    (ha : a ∉ P) : NumberField.RingOfIntegers K :=
  Classical.choose
    (exists_cubic_root_eq_pow hZeta P a hPprime hPbot hNormCoprime ha)

open Classical in
public lemma primeIdealValidCubicSymbol_mem
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
    (ha : a ∉ P) :
    primeIdealValidCubicSymbol hZeta P a hPprime hPbot hNormCoprime ha ∈
      ({(1 : NumberField.RingOfIntegers K),
        omega hZeta, omega hZeta ^ 2} : Set _) :=
  (Classical.choose_spec
    (exists_cubic_root_eq_pow hZeta P a hPprime hPbot hNormCoprime ha)).1

open Classical in
public lemma primeIdealValidCubicSymbol_spec
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
    (ha : a ∉ P) :
    Ideal.Quotient.mk P
        (primeIdealValidCubicSymbol hZeta P a hPprime hPbot hNormCoprime ha) =
      Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3) :=
  (Classical.choose_spec
    (exists_cubic_root_eq_pow hZeta P a hPprime hPbot hNormCoprime ha)).2

-- Characterization: primitive-root distinctness and uniqueness.

omit [IsCyclotomicExtension {3} ℚ K] in
public lemma omegaQuotient_isPrimitiveRoot
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
    IsPrimitiveRoot (Ideal.Quotient.mk P (omega (K := K) hZeta)) 3 := by
  have hNeBot : P ≠ ⊥ := hPbot
  have hAbsNeOne : Ideal.absNorm P ≠ 1 := by
    intro h
    have hTop : P = ⊤ := (Ideal.absNorm_eq_one_iff (I := P)).mp h
    exact hPprime.ne_top hTop
  have _ : P ≠ ⊥ := hNeBot
  exact hZeta.toInteger_isPrimitiveRoot.idealQuotient_mk hAbsNeOne hNormCoprime

omit [IsCyclotomicExtension {3} ℚ K] in
public lemma mk_one_ne_mk_omega
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
    Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) ≠
      Ideal.Quotient.mk P (omega (K := K) hZeta) := by
  intro hEq
  have hPrim :=
    omegaQuotient_isPrimitiveRoot (K := K) hZeta P hPprime hPbot hNormCoprime
  have hOne : Ideal.Quotient.mk P (omega (K := K) hZeta) = 1 := by
    rw [← hEq, map_one]
  exact hPrim.ne_one (by norm_num) hOne

omit [IsCyclotomicExtension {3} ℚ K] in
public lemma mk_one_ne_mk_omega_sq
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
    Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) ≠
      Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) := by
  intro hEq
  have hPrim :=
    omegaQuotient_isPrimitiveRoot (K := K) hZeta P hPprime hPbot hNormCoprime
  have hPow2 :
      (Ideal.Quotient.mk P (omega (K := K) hZeta)) ^ 2 = 1 := by
    rw [← map_pow, ← hEq, map_one]
  have hNe :
      (Ideal.Quotient.mk P (omega (K := K) hZeta)) ^ 2 ≠ 1 :=
    hPrim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  exact hNe hPow2

omit [IsCyclotomicExtension {3} ℚ K] in
public lemma mk_omega_ne_mk_omega_sq
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
    Ideal.Quotient.mk P (omega (K := K) hZeta) ≠
      Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) := by
  intro hEq
  have hPrim :=
    omegaQuotient_isPrimitiveRoot (K := K) hZeta P hPprime hPbot hNormCoprime
  have hMkNeZero :
      Ideal.Quotient.mk P (omega (K := K) hZeta) ≠ 0 := by
    intro hZero
    have hpow : (Ideal.Quotient.mk P (omega (K := K) hZeta)) ^ 3 = 1 :=
      hPrim.pow_eq_one
    have : (0 : NumberField.RingOfIntegers K ⧸ P) ^ (3 : ℕ) = 1 := by
      rw [← hZero, hpow]
    simp at this
  have hPowEq :
      Ideal.Quotient.mk P (omega (K := K) hZeta) =
        Ideal.Quotient.mk P (omega (K := K) hZeta) ^ 2 := by
    rw [← map_pow, hEq]
  have hIsMax : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPbot
  let _ : Field (NumberField.RingOfIntegers K ⧸ P) :=
    Ideal.Quotient.field P
  have hMul :
      Ideal.Quotient.mk P (omega (K := K) hZeta) *
        (1 - Ideal.Quotient.mk P (omega (K := K) hZeta)) = 0 := by
    have hSub :
        Ideal.Quotient.mk P (omega (K := K) hZeta) -
          Ideal.Quotient.mk P (omega (K := K) hZeta) ^ 2 = 0 := by
      rw [← hPowEq, sub_self]
    have h1 :
        Ideal.Quotient.mk P (omega (K := K) hZeta) *
            (1 - Ideal.Quotient.mk P (omega (K := K) hZeta)) =
          Ideal.Quotient.mk P (omega (K := K) hZeta) -
            Ideal.Quotient.mk P (omega (K := K) hZeta) ^ 2 := by
      ring
    rw [h1, hSub]
  rcases mul_eq_zero.mp hMul with hZero | hOne
  · exact hMkNeZero hZero
  · have hEqOne :
        Ideal.Quotient.mk P (omega (K := K) hZeta) = 1 := by
      have hSubZero :
          1 - Ideal.Quotient.mk P (omega (K := K) hZeta) = 0 := hOne
      have h2 :
          Ideal.Quotient.mk P (omega (K := K) hZeta) =
            1 - (1 - Ideal.Quotient.mk P (omega (K := K) hZeta)) := by
        ring
      rw [h2, hSubZero, sub_zero]
    exact hPrim.ne_one (by norm_num) hEqOne

omit [IsCyclotomicExtension {3} ℚ K] in
public lemma cubicRoot_quotient_pairwise_distinct
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
    Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) ≠
        Ideal.Quotient.mk P (omega (K := K) hZeta) ∧
      Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) ≠
        Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) ∧
      Ideal.Quotient.mk P (omega (K := K) hZeta) ≠
        Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) :=
  ⟨mk_one_ne_mk_omega hZeta P hPprime hPbot hNormCoprime,
    mk_one_ne_mk_omega_sq hZeta P hPprime hPbot hNormCoprime,
    mk_omega_ne_mk_omega_sq hZeta P hPprime hPbot hNormCoprime⟩

public lemma primeIdealValidCubicSymbol_unique
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
    (ha : a ∉ P)
    (c : NumberField.RingOfIntegers K)
    (hcMem : c ∈ ({(1 : NumberField.RingOfIntegers K),
        omega hZeta, omega hZeta ^ 2} : Set _))
    (hcSpec : Ideal.Quotient.mk P c =
        Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3)) :
    c = primeIdealValidCubicSymbol hZeta P a hPprime hPbot hNormCoprime ha := by
  have hValidMem :=
    primeIdealValidCubicSymbol_mem hZeta P a hPprime hPbot hNormCoprime ha
  have hValidSpec :=
    primeIdealValidCubicSymbol_spec hZeta P a hPprime hPbot hNormCoprime ha
  have hEq :
      Ideal.Quotient.mk P c =
        Ideal.Quotient.mk P
          (primeIdealValidCubicSymbol hZeta P a hPprime hPbot
            hNormCoprime ha) := by
    rw [hcSpec, hValidSpec]
  have hPair :=
    cubicRoot_quotient_pairwise_distinct (K := K) hZeta P hPprime hPbot
      hNormCoprime
  have h1neW := hPair.1
  have h1neW2 := hPair.2.1
  have hWneW2 := hPair.2.2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcMem hValidMem
  rcases hcMem with rfl | rfl | rfl
  · rcases hValidMem with hV | hV | hV
    · exact hV.symm
    · exfalso
      have :
          Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) =
            Ideal.Quotient.mk P (omega (K := K) hZeta) := by
        rw [hEq, hV]
      exact h1neW this
    · exfalso
      have :
          Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) =
            Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) := by
        rw [hEq, hV]
      exact h1neW2 this
  · rcases hValidMem with hV | hV | hV
    · exfalso
      have :
          Ideal.Quotient.mk P (omega (K := K) hZeta) =
            Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) := by
        rw [hEq, hV]
      exact h1neW this.symm
    · exact hV.symm
    · exfalso
      have :
          Ideal.Quotient.mk P (omega (K := K) hZeta) =
            Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) := by
        rw [hEq, hV]
      exact hWneW2 this
  · rcases hValidMem with hV | hV | hV
    · exfalso
      have :
          Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) =
            Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) := by
        rw [hEq, hV]
      exact h1neW2 this.symm
    · exfalso
      have :
          Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) =
            Ideal.Quotient.mk P (omega (K := K) hZeta) := by
        rw [hEq, hV]
      exact hWneW2 this.symm
    · exact hV.symm

public lemma primeIdealValidCubicSymbol_characterization
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
    (ha : a ∉ P)
    (c : NumberField.RingOfIntegers K) :
    (c = primeIdealValidCubicSymbol hZeta P a hPprime hPbot hNormCoprime ha ↔
      c ∈ ({(1 : NumberField.RingOfIntegers K), omega hZeta,
        omega hZeta ^ 2} : Set _) ∧
        Ideal.Quotient.mk P c =
          Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3)) := by
  constructor
  · intro hEq
    rw [hEq]
    exact ⟨primeIdealValidCubicSymbol_mem hZeta P a hPprime hPbot hNormCoprime ha,
      primeIdealValidCubicSymbol_spec hZeta P a hPprime hPbot hNormCoprime ha⟩
  · intro ⟨hMem, hSpec⟩
    exact primeIdealValidCubicSymbol_unique hZeta P a hPprime hPbot
      hNormCoprime ha c hMem hSpec

open Classical in
/-- **Totalized prime-ideal cubic symbol.** Let $K$ be a number field that is the third
cyclotomic extension of $\mathbb{Q}$, with ring of integers $\mathcal{O}_K$, let $\zeta \in K$ be
a primitive cube root of unity and let $\omega$ be $\zeta$ regarded as an element of
$\mathcal{O}_K$. For an ideal $P$ of $\mathcal{O}_K$ and $a \in \mathcal{O}_K$: if $P$ is a
nonzero prime ideal whose absolute norm $N(P)$ is coprime to $3$, the value is $0$ when
$a \in P$, and otherwise the unique $c \in \{1, \omega, \omega^2\}$ with
$c \equiv a^{(N(P) - 1)/3} \pmod{P}$; for every other ideal $P$ the value is $1$. -/
public noncomputable def primeIdealCubicSymbolFactorRaw
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K) : NumberField.RingOfIntegers K :=
  if hPprime : P.IsPrime then
    if hPbot : P ≠ ⊥ then
      if hCop : Nat.Coprime (Ideal.absNorm P) 3 then
        if ha : a ∈ P then 0
        else primeIdealValidCubicSymbol hZeta P a hPprime hPbot hCop ha
      else 1
    else 1
  else 1

public lemma primeIdealCubicSymbolFactorRaw_of_not_isPrime
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hNotPrime : ¬ P.IsPrime) :
    primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
  simp [primeIdealCubicSymbolFactorRaw, hNotPrime]

public lemma primeIdealCubicSymbolFactorRaw_bot
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a : NumberField.RingOfIntegers K) :
    primeIdealCubicSymbolFactorRaw hZeta
        (⊥ : Ideal (NumberField.RingOfIntegers K)) a = 1 := by
  simp [primeIdealCubicSymbolFactorRaw]

public lemma primeIdealCubicSymbolFactorRaw_of_not_coprime
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNotCop : ¬ Nat.Coprime (Ideal.absNorm P) 3) :
    primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
  simp [primeIdealCubicSymbolFactorRaw, hPprime, hPbot, hNotCop]

public lemma primeIdealCubicSymbolFactorRaw_eq_one_of_isPrime_of_bot
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hBot : P = ⊥) :
    primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
  have hNotBot : ¬ (P ≠ ⊥) := by rw [hBot]; simp
  simp [primeIdealCubicSymbolFactorRaw, hPprime, hNotBot]

open Classical in
/-- **Totalized cubic residue symbol.** Let $K$ be a number field that is the third cyclotomic
extension of $\mathbb{Q}$, with ring of integers $\mathcal{O}_K$, and let $\zeta \in K$ be a
primitive cube root of unity. For $a, n \in \mathcal{O}_K$, the value is $0$ if $n = 0$;
otherwise it is the product, over the prime ideals $P$ in the factorization of the principal
ideal $(n)$ counted with multiplicity, of the totalized prime-ideal cubic symbol of $a$ at $P$
(which is $1$ unless $P$ is a nonzero prime ideal whose absolute norm is coprime to $3$). -/
public noncomputable def cubicResidueSymbolRaw
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a n : NumberField.RingOfIntegers K) : NumberField.RingOfIntegers K :=
  if n = 0 then 0
  else
    let I := Ideal.span ({n} : Set (NumberField.RingOfIntegers K))
    let facs := UniqueFactorizationMonoid.normalizedFactors I
    (facs.map (fun P => primeIdealCubicSymbolFactorRaw hZeta P a)).prod

public lemma cubicResidueSymbolRaw_unit
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a : NumberField.RingOfIntegers K)
    (u : NumberField.RingOfIntegers K) (hu : IsUnit u) :
    cubicResidueSymbolRaw hZeta a u = 1 := by
  unfold cubicResidueSymbolRaw
  have hu0 : u ≠ 0 := IsUnit.ne_zero hu
  simp only [hu0, ↓reduceIte]
  have hSpanTop :
      Ideal.span ({u} : Set (NumberField.RingOfIntegers K)) = ⊤ :=
    Ideal.span_singleton_eq_top.mpr hu
  have hIsUnitIdeal :
      IsUnit (Ideal.span ({u} : Set (NumberField.RingOfIntegers K))) := by
    rw [Ideal.isUnit_iff, hSpanTop]
  have hFacs :
      UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({u} : Set _)) = 0 := by
    exact UniqueFactorizationMonoid.normalizedFactors_of_isUnit hIsUnitIdeal
  simp [hFacs]

public lemma cubicResidueSymbolRaw_mul
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a m n : NumberField.RingOfIntegers K)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    cubicResidueSymbolRaw hZeta a (m * n) =
      cubicResidueSymbolRaw hZeta a m * cubicResidueSymbolRaw hZeta a n := by
  unfold cubicResidueSymbolRaw
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [hm, hn, hmn, ↓reduceIte]
  have hSpanMul :
      Ideal.span ({m * n} : Set (NumberField.RingOfIntegers K)) =
        Ideal.span ({m} : Set _) * Ideal.span ({n} : Set _) := by
    rw [Ideal.span_singleton_mul_span_singleton]
  have hmBot :
      Ideal.span ({m} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hm
  have hnBot :
      Ideal.span ({n} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hn
  have hFacMul :
      UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({m * n} : Set _)) =
        UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({m} : Set _)) +
          UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({n} : Set _)) := by
    rw [hSpanMul]
    exact UniqueFactorizationMonoid.normalizedFactors_mul hmBot hnBot
  simp only [hFacMul, Multiset.map_add, Multiset.prod_add]

public lemma cubicResidueSymbolRaw_prime
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a p : NumberField.RingOfIntegers K)
    (hpPrime : Prime p)
    (hpNeZero : p ≠ 0) :
    cubicResidueSymbolRaw hZeta a p =
      primeIdealCubicSymbolFactorRaw hZeta (Ideal.span {p}) a := by
  unfold cubicResidueSymbolRaw
  simp only [hpNeZero, ↓reduceIte]
  have hSpanPrime :
      (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hpPrime
  have hSpanNeBot :
      Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hpNeZero
  have hPrimeIdeal :
      Prime (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
  have hIrred :
      Irreducible (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    hPrimeIdeal.irreducible
  have hFac :
      UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({p} : Set _)) = {Ideal.span {p}} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrred,
      normalize_eq]
  simp [hFac]

public lemma cubicResidueSymbolRaw_prime_dvd
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a p : NumberField.RingOfIntegers K)
    (hpPrime : Prime p)
    (hpNeZero : p ≠ 0)
    (hNormCop :
      Nat.Coprime
        (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
    (hdvd : p ∣ a) :
    cubicResidueSymbolRaw hZeta a p = 0 := by
  rw [cubicResidueSymbolRaw_prime hZeta a p hpPrime hpNeZero]
  have hSpanPrime :
      (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hpPrime
  have hSpanNeBot :
      Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hpNeZero
  have hMem :
      a ∈ Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) :=
    Ideal.mem_span_singleton.mpr hdvd
  simp only [primeIdealCubicSymbolFactorRaw,
    dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hNormCop, dite_eq_left hMem]

public lemma cubicResidueSymbolRaw_prime_not_dvd
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a p : NumberField.RingOfIntegers K)
    (hpPrime : Prime p)
    (hpNeZero : p ≠ 0)
    (hNormCop :
      Nat.Coprime
        (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
    (hndvd : ¬ p ∣ a) :
    cubicResidueSymbolRaw hZeta a p ∈
        ({(1 : NumberField.RingOfIntegers K),
          omega hZeta, omega hZeta ^ 2} : Set _) ∧
      Ideal.Quotient.mk (Ideal.span {p})
          (cubicResidueSymbolRaw hZeta a p) =
        Ideal.Quotient.mk (Ideal.span {p}) a ^
          ((Ideal.absNorm (Ideal.span {p}) - 1) / 3) := by
  have hNotMem :
      a ∉ Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) := by
    rwa [Ideal.mem_span_singleton]
  rw [cubicResidueSymbolRaw_prime hZeta a p hpPrime hpNeZero]
  have hSpanPrime :
      (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hpPrime
  have hSpanNeBot :
      Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hpNeZero
  have hEq :
      primeIdealCubicSymbolFactorRaw hZeta (Ideal.span {p}) a =
        primeIdealValidCubicSymbol hZeta (Ideal.span {p}) a
          hSpanPrime hSpanNeBot hNormCop hNotMem := by
    simp only [primeIdealCubicSymbolFactorRaw,
      dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hNormCop,
      dite_eq_right hNotMem]
  rw [hEq]
  constructor
  · exact primeIdealValidCubicSymbol_mem hZeta _ _
      hSpanPrime hSpanNeBot hNormCop hNotMem
  · exact primeIdealValidCubicSymbol_spec hZeta _ _
      hSpanPrime hSpanNeBot hNormCop hNotMem

/-- **Cubic residue symbol at a prime ideal.** Let $K$ be a number field that is the third
cyclotomic extension of $\mathbb{Q}$, with ring of integers $\mathcal{O}_K$, let $\zeta \in K$ be
a primitive cube root of unity and let $\omega$ be $\zeta$ regarded as an element of
$\mathcal{O}_K$. For a nonzero prime ideal $P$ of $\mathcal{O}_K$ whose absolute norm $N(P)$ is
coprime to $3$ and for $a \in \mathcal{O}_K$, the cubic residue symbol $(a/P)_3$ is $0$ if
$a \in P$, and otherwise the unique $c \in \{1, \omega, \omega^2\}$ with
$c \equiv a^{(N(P) - 1)/3} \pmod{P}$. -/
public noncomputable def primeIdealCubicSymbol
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (_hPprime : P.IsPrime)
    (_hPbot : P ≠ ⊥)
    (_hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
    NumberField.RingOfIntegers K :=
  primeIdealCubicSymbolFactorRaw hZeta P a

/-- **Cubic residue denominators.** Let $K$ be a number field that is the third cyclotomic
extension of $\mathbb{Q}$, with ring of integers $\mathcal{O}_K$. An element $n \in \mathcal{O}_K$
is a cubic residue denominator when $n \neq 0$ and the absolute norm of the principal ideal
$(n)$ is coprime to $3$. -/
public def IsCubicResidueDenominator
    (n : NumberField.RingOfIntegers K) : Prop :=
  n ≠ 0 ∧ Nat.Coprime (Ideal.absNorm (Ideal.span {n})) 3

/-- **Cubic residue symbol modulo an element.** Let $K$ be a number field that is the third
cyclotomic extension of $\mathbb{Q}$, with ring of integers $\mathcal{O}_K$, let $\zeta \in K$ be
a primitive cube root of unity and let $\omega$ be $\zeta$ regarded as an element of
$\mathcal{O}_K$. For $a \in \mathcal{O}_K$ and a cubic residue denominator $n$ (that is,
$n \neq 0$ and the absolute norm of the principal ideal $(n)$ is coprime to $3$), the cubic
residue symbol $(a/n)_3$ is the product, over the prime ideals $P$ in the factorization of $(n)$
counted with multiplicity, of the value that is $0$ if $a \in P$ and otherwise the unique
$c \in \{1, \omega, \omega^2\}$ with $c \equiv a^{(N(P) - 1)/3} \pmod{P}$, where $N(P)$ is the
absolute norm of $P$. Each such $P$ is a nonzero prime ideal whose absolute norm is coprime
to $3$. -/
public noncomputable def cubicResidueSymbol
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a n : NumberField.RingOfIntegers K)
    (_hValid : IsCubicResidueDenominator n) :
    NumberField.RingOfIntegers K :=
  cubicResidueSymbolRaw hZeta a n

public lemma cubicResidueSymbol_unit {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)
    (a : NumberField.RingOfIntegers K) (u : NumberField.RingOfIntegers K)
    (hu : IsUnit u) (hValid : IsCubicResidueDenominator u) :
    cubicResidueSymbol hZeta a u hValid = 1 := by
  simpa [cubicResidueSymbol] using cubicResidueSymbolRaw_unit hZeta a u hu

public lemma cubicResidueSymbol_mul {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)
    (a : NumberField.RingOfIntegers K) (m : NumberField.RingOfIntegers K)
    (n : NumberField.RingOfIntegers K) (hmValid : IsCubicResidueDenominator m)
    (hnValid : IsCubicResidueDenominator n)
    (hmnValid : IsCubicResidueDenominator (m * n)) :
    cubicResidueSymbol hZeta a (m * n) hmnValid =
      cubicResidueSymbol hZeta a m hmValid * cubicResidueSymbol hZeta a n hnValid := by
  simpa [cubicResidueSymbol] using
    cubicResidueSymbolRaw_mul hZeta a m n hmValid.1 hnValid.1

public lemma cubicResidueSymbol_prime
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a p : NumberField.RingOfIntegers K)
    (hpPrime : Prime p)
    (hpValid : IsCubicResidueDenominator p) :
    cubicResidueSymbol hZeta a p hpValid =
      primeIdealCubicSymbol hZeta (Ideal.span {p}) a
        (Ideal.isPrime_span_singleton_of_prime hpPrime)
        (by
          rw [Ne, Ideal.span_singleton_eq_bot]
          exact hpValid.1)
        hpValid.2 := by
  simpa [cubicResidueSymbol, primeIdealCubicSymbol] using
    cubicResidueSymbolRaw_prime hZeta a p hpPrime hpValid.1

public lemma cubicResidueSymbol_prime_dvd
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a p : NumberField.RingOfIntegers K)
    (hpPrime : Prime p)
    (hpValid : IsCubicResidueDenominator p)
    (hdvd : p ∣ a) :
    cubicResidueSymbol hZeta a p hpValid = 0 := by
  simpa [cubicResidueSymbol] using
    cubicResidueSymbolRaw_prime_dvd
      hZeta a p hpPrime hpValid.1 hpValid.2 hdvd

public lemma cubicResidueSymbol_prime_not_dvd
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a p : NumberField.RingOfIntegers K)
    (hpPrime : Prime p)
    (hpValid : IsCubicResidueDenominator p)
    (hndvd : ¬ p ∣ a) :
    cubicResidueSymbol hZeta a p hpValid ∈
        ({(1 : NumberField.RingOfIntegers K),
          omega hZeta, omega hZeta ^ 2} : Set _) ∧
      Ideal.Quotient.mk (Ideal.span {p})
          (cubicResidueSymbol hZeta a p hpValid) =
        Ideal.Quotient.mk (Ideal.span {p}) a ^
          ((Ideal.absNorm (Ideal.span {p}) - 1) / 3) := by
  simpa [cubicResidueSymbol] using
    cubicResidueSymbolRaw_prime_not_dvd
      hZeta a p hpPrime hpValid.1 hpValid.2 hndvd

end MetaMathlibExt
