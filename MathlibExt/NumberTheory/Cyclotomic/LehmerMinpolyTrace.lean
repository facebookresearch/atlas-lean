/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace MetaMathlibExt

private theorem minpoly_add_inv_eq_of_minpoly_eq {K : Type*} [Field K] [CharZero K]
    {L : Type*} [Field L] [CharZero L] {n : ℕ} (hn : 0 < n)
    {zeta : K} {omega : L}
    (hpowK : zeta ^ n = 1) (hpowC : omega ^ n = 1)
    (hmin : minpoly ℤ zeta = minpoly ℤ omega)
    (hintK : IsIntegral ℤ zeta) (hintC : IsIntegral ℤ omega) :
    minpoly ℤ (zeta + zeta⁻¹) = minpoly ℤ (omega + omega⁻¹) := by
  have memK0 : zeta ∈ Algebra.adjoin ℤ ({zeta} : Set K) :=
    Algebra.self_mem_adjoin_singleton ℤ zeta
  have memC0 : omega ∈ Algebra.adjoin ℤ ({omega} : Set L) :=
    Algebra.self_mem_adjoin_singleton ℤ omega
  have memK : zeta + zeta ^ (n - 1) ∈ Algebra.adjoin ℤ ({zeta} : Set K) :=
    add_mem memK0 (pow_mem memK0 (n - 1))
  have memC : omega + omega ^ (n - 1) ∈ Algebra.adjoin ℤ ({omega} : Set L) :=
    add_mem memC0 (pow_mem memC0 (n - 1))
  have hn1 : n - 1 + 1 = n := by omega
  have hinvK : zeta⁻¹ = zeta ^ (n - 1) := by
    have h1 : zeta ^ (n - 1) * zeta = 1 := by
      rw [← pow_succ, hn1]
      exact hpowK
    exact (eq_inv_of_mul_eq_one_left h1).symm
  have hinvC : omega⁻¹ = omega ^ (n - 1) := by
    have h1 : omega ^ (n - 1) * omega = 1 := by
      rw [← pow_succ, hn1]
      exact hpowC
    exact (eq_inv_of_mul_eq_one_left h1).symm
  have hrootK : (minpoly.equivAdjoin hintK) (AdjoinRoot.root (minpoly ℤ zeta)) =
      (⟨zeta, memK0⟩ : ↥(Algebra.adjoin ℤ ({zeta} : Set K))) := by
    have h1 := minpoly.coe_equivAdjoin hintK
    have h2 := AdjoinRoot.Minpoly.coe_toAdjoin_mk_X (R := ℤ) (S := K) (x := zeta)
    apply Subtype.ext
    change ((minpoly.equivAdjoin hintK) (AdjoinRoot.root (minpoly ℤ zeta)) : K) = zeta
    rw [h1]
    exact h2
  have hrootC : (minpoly.equivAdjoin hintC) (AdjoinRoot.root (minpoly ℤ omega)) =
      (⟨omega, memC0⟩ : ↥(Algebra.adjoin ℤ ({omega} : Set L))) := by
    have h1 := minpoly.coe_equivAdjoin hintC
    have h2 := AdjoinRoot.Minpoly.coe_toAdjoin_mk_X (R := ℤ) (S := L) (x := omega)
    apply Subtype.ext
    change ((minpoly.equivAdjoin hintC) (AdjoinRoot.root (minpoly ℤ omega)) : L) = omega
    rw [h1]
    exact h2
  have keyK : ∀ {Q : Polynomial ℤ} (_ : minpoly ℤ zeta = Q),
      ∃ e : AdjoinRoot Q ≃ₐ[ℤ] ↥(Algebra.adjoin ℤ ({zeta} : Set K)),
        e (AdjoinRoot.root Q) = ⟨zeta, memK0⟩ := by
    intro Q hQ
    subst hQ
    exact ⟨minpoly.equivAdjoin hintK, hrootK⟩
  have keyC : ∀ {Q : Polynomial ℤ} (_ : minpoly ℤ omega = Q),
      ∃ e : AdjoinRoot Q ≃ₐ[ℤ] ↥(Algebra.adjoin ℤ ({omega} : Set L)),
        e (AdjoinRoot.root Q) = ⟨omega, memC0⟩ := by
    intro Q hQ
    subst hQ
    exact ⟨minpoly.equivAdjoin hintC, hrootC⟩
  obtain ⟨eK, hK⟩ := keyK hmin
  obtain ⟨eC, hC⟩ := keyC rfl
  have hgen : (eK.symm.trans eC) ⟨zeta, memK0⟩ = ⟨omega, memC0⟩ := by
    have hsymm : eK.symm ⟨zeta, memK0⟩ = AdjoinRoot.root (minpoly ℤ omega) := by
      have h := congrArg (⇑eK.symm) hK
      rw [AlgEquiv.symm_apply_apply] at h
      exact h.symm
    calc (eK.symm.trans eC) ⟨zeta, memK0⟩ = eC (eK.symm ⟨zeta, memK0⟩) := rfl
      _ = eC (AdjoinRoot.root (minpoly ℤ omega)) := by rw [hsymm]
      _ = ⟨omega, memC0⟩ := hC
  have htrace : (eK.symm.trans eC) ⟨zeta + zeta ^ (n - 1), memK⟩ =
      ⟨omega + omega ^ (n - 1), memC⟩ := by
    have hdecompK : (⟨zeta + zeta ^ (n - 1), memK⟩ :
        ↥(Algebra.adjoin ℤ ({zeta} : Set K))) =
        ⟨zeta, memK0⟩ + ⟨zeta, memK0⟩ ^ (n - 1) := Subtype.ext (by simp)
    have hdecompC : (⟨omega, memC0⟩ + ⟨omega, memC0⟩ ^ (n - 1) :
        ↥(Algebra.adjoin ℤ ({omega} : Set L))) = ⟨omega + omega ^ (n - 1), memC⟩ :=
      Subtype.ext (by simp)
    calc (eK.symm.trans eC) ⟨zeta + zeta ^ (n - 1), memK⟩
        = (eK.symm.trans eC) (⟨zeta, memK0⟩ + ⟨zeta, memK0⟩ ^ (n - 1)) := by
          rw [hdecompK]
      _ = (eK.symm.trans eC) ⟨zeta, memK0⟩ +
          ((eK.symm.trans eC) ⟨zeta, memK0⟩) ^ (n - 1) := by rw [map_add, map_pow]
      _ = ⟨omega, memC0⟩ + ⟨omega, memC0⟩ ^ (n - 1) := by rw [hgen]
      _ = ⟨omega + omega ^ (n - 1), memC⟩ := hdecompC
  have msub : minpoly ℤ (⟨zeta + zeta ^ (n - 1), memK⟩ :
      ↥(Algebra.adjoin ℤ ({zeta} : Set K))) =
      minpoly ℤ (⟨omega + omega ^ (n - 1), memC⟩ :
        ↥(Algebra.adjoin ℤ ({omega} : Set L))) := by
    have h := minpoly.algEquiv_eq (eK.symm.trans eC) ⟨zeta + zeta ^ (n - 1), memK⟩
    rw [htrace] at h
    exact h.symm
  have downK : minpoly ℤ (zeta + zeta ^ (n - 1)) =
      minpoly ℤ (⟨zeta + zeta ^ (n - 1), memK⟩ :
        ↥(Algebra.adjoin ℤ ({zeta} : Set K))) :=
    minpoly.algHom_eq (Subalgebra.val (Algebra.adjoin ℤ ({zeta} : Set K)))
      Subtype.coe_injective ⟨zeta + zeta ^ (n - 1), memK⟩
  have downC : minpoly ℤ (omega + omega ^ (n - 1)) =
      minpoly ℤ (⟨omega + omega ^ (n - 1), memC⟩ :
        ↥(Algebra.adjoin ℤ ({omega} : Set L))) :=
    minpoly.algHom_eq (Subalgebra.val (Algebra.adjoin ℤ ({omega} : Set L)))
      Subtype.coe_injective ⟨omega + omega ^ (n - 1), memC⟩
  calc minpoly ℤ (zeta + zeta⁻¹) = minpoly ℤ (zeta + zeta ^ (n - 1)) := by rw [hinvK]
    _ = minpoly ℤ (⟨zeta + zeta ^ (n - 1), memK⟩ :
      ↥(Algebra.adjoin ℤ ({zeta} : Set K))) := downK
    _ = minpoly ℤ (⟨omega + omega ^ (n - 1), memC⟩ :
      ↥(Algebra.adjoin ℤ ({omega} : Set L))) := msub
    _ = minpoly ℤ (omega + omega ^ (n - 1)) := downC.symm
    _ = minpoly ℤ (omega + omega⁻¹) := by rw [hinvC]

/-- **The real cyclotomic polynomial is the minimal polynomial of $\zeta + \zeta^{-1}$.** Let $K$
be a field of characteristic zero, let $n > 2$ be a natural number, and let $\zeta \in K$ be a
primitive $n$-th root of unity. Then the real cyclotomic polynomial $\psi_n$ equals the minimal
polynomial of $\zeta + \zeta^{-1}$ over $\mathbb{Z}$.

Proves `Wanted` entry `realCyclotomicPolynomial_eq_minpoly_trace`.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of
Algebraic Cosine Values at Rational Multiples of π", Journal of Integer Sequences 19
(2016), source lines 83–90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex
source SHA-256 15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455
normalized no-final-newline span SHA-256
e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039
-/
theorem realCyclotomicPolynomial_eq_minpoly_trace {K : Type*} [Field K]
    [CharZero K] {n : ℕ} (hn : 2 < n) {zeta : K}
    (hprim : IsPrimitiveRoot zeta n) :
    realCyclotomicPolynomial n = minpoly ℤ (zeta + zeta⁻¹) := by
  have hn0 : n ≠ 0 := by omega
  have hnble : 0 < n := by omega
  have hprimC : IsPrimitiveRoot
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))) n :=
    Complex.isPrimitiveRoot_exp n hn0
  have e1 : Polynomial.cyclotomic n ℤ = minpoly ℤ zeta :=
    Polynomial.cyclotomic_eq_minpoly hprim hnble
  have e2 : Polynomial.cyclotomic n ℤ =
      minpoly ℤ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))) :=
    Polynomial.cyclotomic_eq_minpoly hprimC hnble
  have hmin : minpoly ℤ zeta =
      minpoly ℤ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))) :=
    e1.symm.trans e2
  have hpowK : zeta ^ n = 1 := hprim.pow_eq_one
  have hpowC : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))) ^ n = 1 :=
    hprimC.pow_eq_one
  have hintK : IsIntegral ℤ zeta := hprim.isIntegral hnble
  have hintC : IsIntegral ℤ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))) :=
    hprimC.isIntegral hnble
  have hfin := minpoly_add_inv_eq_of_minpoly_eq hnble hpowK hpowC hmin hintK hintC
  exact hfin.symm

end MetaMathlibExt
