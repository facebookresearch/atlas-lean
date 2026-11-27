/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff.lean`,
`P2M/Sol/S_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff.lean`,
`Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra.lean`,
`P2M/Sol/S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra.lean`,
`Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra_integralClosure.lean`,
`P2M/Sol/S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra_integralClosure.lean`,
`Theorems/Thm_CuspForm_exists_isNormalizedEigenform_ker_le_of_isPrime.lean`,
`P2M/Sol/S_CuspForm_exists_isNormalizedEigenform_ker_le_of_isPrime.lean`,
`Theorems/Thm_CuspForm_exists_isNormalizedEigenform_congruent_of_isMaximal.lean`, and
`P2M/Sol/S_CuspForm_exists_isNormalizedEigenform_congruent_of_isMaximal.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
public import MathlibExt.NumberTheory.ModularForms.HeckeAlgebraIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.FractionRing
import MathlibExt.NumberTheory.ModularForms.HeckeEigenform
import MathlibExt.NumberTheory.ModularForms.NormalizedEigenform
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0
import MathlibExt.RingTheory.Ideal.MinimalPrime.CharZeroEigenvector

/-!
# Hecke eigenvalues of weight-two normalized eigenforms

For a weight-two normalized eigenform `f` on `Γ₀(N)`, the Hecke algebra acts on `f` through
a ring homomorphism to `ℂ`; under an integral structure this character takes values in the
algebraic integers. Conversely, every characteristic-zero prime of the Hecke algebra away
from the level contains the annihilator of some normalized eigenform, which yields the
weight-two eigenform congruent to a given maximal ideal (the Deligne–Serre lifting step).

## Main statements

* `CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff`: the prime
  coefficients of a normalized eigenform are algebraic integers.
* `CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra`: the Hecke eigenvalues of a
  normalized eigenform form a ring homomorphism on the Hecke algebra.
* `CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra_integralClosure`: that ring
  homomorphism lands in the integral closure of `ℤ` in `ℂ`.
* `CuspForm.exists_isNormalizedEigenform_ker_le_of_isPrime`: a characteristic-zero prime
  of the Hecke algebra contains the annihilator of a normalized eigenform.
* `CuspForm.exists_isNormalizedEigenform_congruent_of_isMaximal`: a maximal ideal of the
  Hecke algebra containing `p` is the reduction of the Hecke eigenvalues of a normalized
  eigenform modulo a maximal ideal above `p` of the algebraic integers.
-/

@[expose] public section

noncomputable section

open UpperHalfPlane ModularFormClass
open scoped MatrixGroups ModularForm

namespace CuspForm

variable {N : ℕ}

private theorem qCoeff_add_aux {k : ℤ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (n : ℕ) : qCoeff ⇑(f + g) n = qCoeff ⇑f n + qCoeff ⇑g n := by
  simp only [qCoeff_eq, FunLike.coe_add]
  rw [ModularForm.qExpansion_add one_pos (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
    f g, map_add]

private theorem IsNormalizedEigenform.ne_zero_aux
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) : f ≠ 0 := by
  rintro rfl
  have h1 := hf.qCoeff_one
  have h0 := CuspForm.qCoeff_smul (N := N) (k := 2) 0 0 1
  rw [zero_smul, zero_mul] at h0
  exact zero_ne_one (h0.symm.trans h1)

/-- For `N ≠ 0`, under an integral structure, the `ℓ`-th `q`-expansion coefficient of a
weight-two normalized eigenform on `Γ₀(N)`, for a prime `ℓ`, is an algebraic integer. -/
theorem IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff [NeZero N]
    (hN : HasIntegralStructure N 2) {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ a : integralClosure ℤ ℂ, (a : ℂ) = qCoeff f ℓ := by
  refine ⟨⟨qCoeff f ℓ, (mem_integralClosure_iff ℤ ℂ).mpr ?_⟩, rfl⟩
  have hv : f ∈ Submodule.span ℂ ((intLattice N 2 : Submodule ℤ _) :
      Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by
    rw [(hasIntegralStructure_iff N 2).mp hN]
    exact Submodule.mem_top
  obtain ⟨-, heig⟩ := (isNormalizedEigenform_iff_heckeTLin f).mp hf
  by_cases hℓN : ℓ ∣ N
  · exact IsIntegral.of_mem_span_of_apply_eq_smul (intLattice N 2) (intLattice_fg N 2)
      (heckeULin 2 hℓN)
      (fun x hx => mem_intLattice_of_coe_eq_heckeU hℓ.ne_zero (coe_heckeULin_apply 2 hℓN x) hx)
      hv hf.ne_zero_aux ((heig ℓ hℓ).2 hℓN)
  · exact IsIntegral.of_mem_span_of_apply_eq_smul (intLattice N 2) (intLattice_fg N 2)
      (heckeTLin 2 hℓ hℓN)
      (fun x hx => mem_intLattice_of_coe_eq_heckeT (by norm_num) hℓ.ne_zero
        (coe_heckeTLin_apply 2 hℓ hℓN x) hx)
      hv hf.ne_zero_aux ((heig ℓ hℓ).1 hℓN)

private theorem apply_eq_qCoeff_one_smul_of_mem [NeZero N] {S : Set ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)}
    (ht : t ∈ heckeAlgebra N 2 S) : t f = qCoeff ⇑(t f) 1 • f := by
  have h1 : qCoeff ⇑f 1 = 1 := hf.qCoeff_one
  have hgen := (isNormalizedEigenform_iff_heckeTLin f).mp hf
  refine Algebra.adjoin_induction
    (p := fun (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) _ =>
      t f = qCoeff ⇑(t f) 1 • f) ?_ ?_ ?_ ?_ ht
  · rintro x (⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩)
    · have h := (hgen.2 ℓ hℓ).1 hℓN
      rw [h, CuspForm.qCoeff_smul, h1, mul_one]
    · have h := (hgen.2 q hq).2 hqN
      rw [h, CuspForm.qCoeff_smul, h1, mul_one]
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self,
      ← Int.cast_smul_eq_zsmul ℂ, CuspForm.qCoeff_smul, h1, mul_one]
  · intro x y _ _ hx hy
    rw [LinearMap.add_apply, qCoeff_add_aux, add_smul, ← hx, ← hy]
  · intro x y _ _ hx hy
    rw [mul_apply_eq_comp, hy, map_smul, hx, smul_smul, CuspForm.qCoeff_smul, h1, mul_one]

/-- For `N ≠ 0`, the Hecke eigenvalues of a weight-two normalized eigenform `f` on `Γ₀(N)` form a
ring homomorphism `χ` on the Hecke algebra away from `S`, with `χ(T_ℓ) = a_ℓ(f)` and
`χ(U_q) = a_q(f)`. -/
theorem IsNormalizedEigenform.exists_ringHom_heckeAlgebra [NeZero N]
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (S : Set ℕ) :
    ∃ χ : heckeAlgebra N 2 S →+* ℂ,
      (∀ t : heckeAlgebra N 2 S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = χ t • f) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        χ (heckeAlgebra.T hℓ hℓN hℓS) = qCoeff f ℓ) ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
        χ (heckeAlgebra.U hq hqN hqS) = qCoeff f q := by
  have h1 : qCoeff ⇑f 1 = 1 := hf.qCoeff_one
  have hgen := (isNormalizedEigenform_iff_heckeTLin f).mp hf
  let e : heckeAlgebra N 2 S → ℂ := fun t =>
    qCoeff ((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f) 1
  have key : ∀ t : heckeAlgebra N 2 S,
      (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = e t • f :=
    fun t => apply_eq_qCoeff_one_smul_of_mem hf t.2
  let χ : heckeAlgebra N 2 S →+* ℂ :=
    { toFun := e
      map_one' := by
        change qCoeff ⇑((1 : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f) 1 = 1
        rw [one_apply_eq_self, h1]
      map_mul' := fun t t' => by
        change qCoeff ⇑(((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) *
          (t' : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) f) 1 = e t * e t'
        rw [mul_apply_eq_comp, key t', map_smul, key t, smul_smul, CuspForm.qCoeff_smul, h1,
          mul_one, mul_comm]
      map_zero' := by
        change qCoeff ⇑((0 : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f) 1 = 0
        rw [LinearMap.zero_apply]
        have := CuspForm.qCoeff_smul (0 : ℂ) f 1
        rwa [zero_smul, zero_mul] at this
      map_add' := fun t t' => by
        change qCoeff ⇑(((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) +
          (t' : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) f) 1 = e t + e t'
        rw [LinearMap.add_apply, qCoeff_add_aux] }
  refine ⟨χ, key, fun ℓ hℓ hℓN hℓS => ?_, fun q hq hqN hqS => ?_⟩
  · change qCoeff ⇑((heckeTLin 2 hℓ hℓN) f) 1 = qCoeff ⇑f ℓ
    rw [(hgen.2 ℓ hℓ).1 hℓN, CuspForm.qCoeff_smul, h1, mul_one]
  · change qCoeff ⇑((heckeULin 2 hqN) f) 1 = qCoeff ⇑f q
    rw [(hgen.2 q hq).2 hqN, CuspForm.qCoeff_smul, h1, mul_one]

/-- For `N ≠ 0`, under an integral structure, the Hecke eigenvalues of a weight-two normalized
eigenform on `Γ₀(N)` form a ring homomorphism from the Hecke algebra to the algebraic integers. -/
theorem IsNormalizedEigenform.exists_ringHom_heckeAlgebra_integralClosure [NeZero N]
    (hN : HasIntegralStructure N 2) {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) (S : Set ℕ) :
    ∃ χ : heckeAlgebra N 2 S →+* integralClosure ℤ ℂ, ∀ t : heckeAlgebra N 2 S,
      (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = (χ t : ℂ) • f := by
  obtain ⟨χ, hχ, hT, hU⟩ := hf.exists_ringHom_heckeAlgebra S
  have hmem : ∀ t : heckeAlgebra N 2 S, χ t ∈ integralClosure ℤ ℂ := by
    rintro ⟨t, ht⟩
    refine Algebra.adjoin_induction (p := fun t ht => χ ⟨t, ht⟩ ∈ integralClosure ℤ ℂ)
      ?_ ?_ ?_ ?_ ht
    · rintro x (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
      · obtain ⟨a, ha⟩ := hf.exists_integralClosure_coe_eq_qCoeff hN ℓ hℓ
        have : χ ⟨heckeTLin 2 hℓ hℓN, heckeTLin_mem_heckeAlgebra hℓ hℓN hℓS⟩ = qCoeff ⇑f ℓ :=
          hT ℓ hℓ hℓN hℓS
        rw [this, ← ha]
        exact a.2
      · obtain ⟨a, ha⟩ := hf.exists_integralClosure_coe_eq_qCoeff hN q hq
        have : χ ⟨heckeULin 2 hqN, heckeULin_mem_heckeAlgebra hq hqN hqS⟩ = qCoeff ⇑f q :=
          hU q hq hqN hqS
        rw [this, ← ha]
        exact a.2
    · intro r
      have : (⟨algebraMap ℤ _ r, Subalgebra.algebraMap_mem _ r⟩ : heckeAlgebra N 2 S) =
          algebraMap ℤ (heckeAlgebra N 2 S) r := rfl
      rw [this, eq_intCast (algebraMap ℤ (heckeAlgebra N 2 S)) r, map_intCast χ]
      have h := Subalgebra.algebraMap_mem (integralClosure ℤ ℂ) r
      rwa [eq_intCast] at h
    · intro x y hx hy hx' hy'
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : heckeAlgebra N 2 S) = ⟨x, hx⟩ + ⟨y, hy⟩ :=
        rfl
      rw [this, χ.map_add]
      exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : heckeAlgebra N 2 S) = ⟨x, hx⟩ * ⟨y, hy⟩ :=
        rfl
      rw [this, map_mul χ]
      exact mul_mem hx' hy'
  exact ⟨χ.codRestrict (integralClosure ℤ ℂ) hmem, fun t => by rw [hχ t]; rfl⟩

end CuspForm

private theorem exists_ringHom_complex_injective_aux (A : Type*) [CommRing A] [IsDomain A]
    [CharZero A] [Module.Finite ℤ A] : ∃ φ : A →+* ℂ, Function.Injective φ := by
  have : Algebra.IsAlgebraic ℤ A := Algebra.IsAlgebraic.of_finite ℤ A
  have : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  have : Algebra.IsAlgebraic ℤ (FractionRing A) := Algebra.IsAlgebraic.trans ℤ A (FractionRing A)
  have : CharZero (FractionRing A) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective A _)
  let ψ : FractionRing A →ₐ[ℤ] ℂ := IsAlgClosed.lift
  exact ⟨ψ.toRingHom.comp (algebraMap A (FractionRing A)),
    ψ.toRingHom.injective.comp (IsFractionRing.injective A (FractionRing A))⟩

namespace CuspForm

variable {N : ℕ}

/-- For `N ≠ 0`, under an integral structure, every prime `𝔭` of the weight-two Hecke algebra
away from the level with `𝔭 ∩ ℤ = 0` contains the annihilator of some normalized eigenform. -/
theorem exists_isNormalizedEigenform_ker_le_of_isPrime [NeZero N]
    (hN : HasIntegralStructure N 2) (𝔭 : Ideal (heckeAlgebra N 2 {ℓ | ℓ ∣ N}))
    (h𝔭 : 𝔭.IsPrime)
    (hchar : ∀ n : ℤ, algebraMap ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) n ∈ 𝔭 → n = 0) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
      ∀ t : heckeAlgebra N 2 {ℓ | ℓ ∣ N},
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = 0 → t ∈ 𝔭 := by
  classical
  have : Module.Finite ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :=
    hN.moduleFinite_heckeAlgebra (by norm_num) _
  have : IsDomain (heckeAlgebra N 2 {ℓ | ℓ ∣ N} ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  have : CharZero (heckeAlgebra N 2 {ℓ | ℓ ∣ N} ⧸ 𝔭) := charZero_of_inj_zero fun n hn => by
    have hmem : algebraMap ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) n ∈ 𝔭 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, map_natCast]
      exact hn
    exact_mod_cast hchar n hmem
  have : Module.Finite ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N} ⧸ 𝔭) := Module.Finite.quotient ℤ 𝔭
  obtain ⟨φ, hφ⟩ := exists_ringHom_complex_injective_aux (heckeAlgebra N 2 {ℓ | ℓ ∣ N} ⧸ 𝔭)
  let χ : heckeAlgebra N 2 {ℓ | ℓ ∣ N} →+* ℂ := φ.comp (Ideal.Quotient.mk 𝔭)
  have hkerχ : ∀ t, χ t = 0 ↔ t ∈ 𝔭 := by
    intro t
    constructor
    · intro h
      have : Ideal.Quotient.mk 𝔭 t = 0 := hφ (by rw [map_zero]; exact h)
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · intro h
      change φ (Ideal.Quotient.mk 𝔭 t) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
  obtain ⟨g, hg0, hg⟩ := hN.exists_ne_zero_forall_apply_eq_smul (by norm_num) χ
  let av : ℕ → ℂ := fun ℓ =>
    if h : ℓ.Prime ∧ ¬ ℓ ∣ N then χ (heckeAlgebra.T h.1 h.2 h.2) else 0
  have hav : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      av ℓ = χ (heckeAlgebra.T hℓ hℓN hℓN) := by
    intro ℓ hℓ hℓN
    simp [av, hℓ, hℓN]
  have hgT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ {ℓ | ℓ ∣ N} →
      heckeTLin 2 hℓ hℓN g = av ℓ • g := by
    intro ℓ hℓ hℓN _
    rw [hav ℓ hℓ hℓN, ← heckeAlgebra.coe_T (k := 2) (S := {ℓ | ℓ ∣ N}) hℓ hℓN hℓN]
    exact hg _
  obtain ⟨f, hf, hcoeff⟩ :=
    exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul hg0 av {ℓ | ℓ ∣ N} hgT
  refine ⟨f, hf, ?_⟩
  have hfχ : ∀ (x : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
      (hx : x ∈ heckeAlgebra N 2 {ℓ | ℓ ∣ N}), x f = χ ⟨x, hx⟩ • f := by
    intro x hx
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · rintro x (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
      · have e1 : qCoeff f ℓ = χ (heckeAlgebra.T hℓ hℓN hℓN) := by
          rw [← hav ℓ hℓ hℓN]
          exact hcoeff ℓ hℓ hℓN hℓN
        change heckeTLin 2 hℓ hℓN f = χ (heckeAlgebra.T hℓ hℓN hℓN) • f
        rw [(((isNormalizedEigenform_iff_heckeTLin f).mp hf).2 ℓ hℓ).1 hℓN, e1]
      · exact absurd hqN hqS
    · intro n
      have e : χ (⟨algebraMap ℤ _ n, Subalgebra.algebraMap_mem _ n⟩ :
          heckeAlgebra N 2 {ℓ | ℓ ∣ N}) = (n : ℂ) := by
        change χ (algebraMap ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) n) = n
        simp only [eq_intCast, map_intCast]
      rw [e, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self,
        Int.cast_smul_eq_zsmul]
    · intro x y hx hy ihx ihy
      rw [LinearMap.add_apply, ihx, ihy, ← add_smul]
      congr 1
      exact (map_add χ (⟨x, hx⟩ : heckeAlgebra N 2 {ℓ | ℓ ∣ N})
        (⟨y, hy⟩ : heckeAlgebra N 2 {ℓ | ℓ ∣ N})).symm
    · intro x y hx hy ihx ihy
      rw [mul_apply_eq_comp, ihy, map_smul, ihx, smul_smul, mul_comm]
      congr 1
      exact (map_mul χ (⟨x, hx⟩ : heckeAlgebra N 2 {ℓ | ℓ ∣ N})
        (⟨y, hy⟩ : heckeAlgebra N 2 {ℓ | ℓ ∣ N})).symm
  intro t ht
  rw [← hkerχ]
  have h := hfχ t.1 t.2
  rw [ht] at h
  rcases smul_eq_zero.mp h.symm with h0 | h0
  · simpa using h0
  · exact absurd h0 hf.ne_zero_aux

/-- **Eigenforms from a maximal ideal of the Hecke algebra.** Let `N ≠ 0`, assume an integral
structure in weight two, and let `𝔪₁` be a maximal ideal of the Hecke algebra away from the level
containing `p`. Then there are a
normalized eigenform `f` and a maximal ideal `𝔪'` of the algebraic integers containing `p`
such that `a_ℓ(f) ≡ b (mod 𝔪')` whenever `T_ℓ ≡ b (mod 𝔪₁)`. -/
theorem exists_isNormalizedEigenform_congruent_of_isMaximal [NeZero N]
    (hN : HasIntegralStructure N 2) (𝔪₁ : Ideal (heckeAlgebra N 2 {ℓ | ℓ ∣ N}))
    (h𝔪₁ : 𝔪₁.IsMaximal) {p : ℕ} (hp𝔪 : (p : heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (b : ℤ),
        heckeAlgebra.T hℓ hℓN hℓN - (b : heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = qCoeff f ℓ ∧ a - (b : integralClosure ℤ ℂ) ∈ 𝔪' := by
  classical
  have : Module.Finite ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :=
    hN.moduleFinite_heckeAlgebra (by norm_num) _
  have : Module.Free ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :=
    hN.moduleFree_heckeAlgebra (by norm_num) _
  have := h𝔪₁
  have : Module.IsTorsionFree ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :=
    Module.Free.instIsTorsionFree ℤ _
  let : Field (heckeAlgebra N 2 {ℓ | ℓ ∣ N} ⧸ 𝔪₁) := Ideal.Quotient.field 𝔪₁
  obtain ⟨𝔭, h𝔭min, h𝔭le, h𝔭char, -, -, -, -, -, -, -⟩ :=
    DeligneSerre.exists_charZero_eigenvector_of_residual_character
      (T := heckeAlgebra N 2 {ℓ | ℓ ∣ N}) (M := heckeAlgebra N 2 {ℓ | ℓ ∣ N})
      (k := heckeAlgebra N 2 {ℓ | ℓ ∣ N} ⧸ 𝔪₁) (Ideal.Quotient.mk 𝔪₁)
  rw [Ideal.mk_ker] at h𝔭le
  obtain ⟨f, hf, hann⟩ := exists_isNormalizedEigenform_ker_le_of_isPrime hN 𝔭
    h𝔭min.1.1 h𝔭char
  obtain ⟨χ, hχ⟩ := hf.exists_ringHom_heckeAlgebra_integralClosure hN {ℓ | ℓ ∣ N}
  have hkerχ : RingHom.ker χ ≤ 𝔪₁ := by
    intro t ht
    refine h𝔭le (hann t ?_)
    rw [hχ t, RingHom.mem_ker.mp ht]
    simp
  let : Algebra (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) (integralClosure ℤ ℂ) := χ.toAlgebra
  have : IsScalarTower ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) (integralClosure ℤ ℂ) := by
    refine IsScalarTower.of_algebraMap_eq fun n => ?_
    change algebraMap ℤ (integralClosure ℤ ℂ) n =
      χ (algebraMap ℤ (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) n)
    simp only [eq_intCast, map_intCast]
  have : Algebra.IsIntegral (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) (integralClosure ℤ ℂ) :=
    ⟨fun x => IsIntegral.tower_top (R := ℤ) (integralClosure.isIntegral x)⟩
  obtain ⟨𝔪', h𝔪'max, h𝔪'comap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := integralClosure ℤ ℂ) 𝔪₁
      (by rw [RingHom.algebraMap_toAlgebra]; exact hkerχ)
  have hmem : ∀ t ∈ 𝔪₁, χ t ∈ 𝔪' := by
    intro t ht
    have hcomap : t ∈ 𝔪'.under (heckeAlgebra N 2 {ℓ | ℓ ∣ N}) := h𝔪'comap ▸ ht
    rwa [Ideal.mem_under, RingHom.algebraMap_toAlgebra] at hcomap
  refine ⟨f, hf, 𝔪', h𝔪'max, ?_, ?_⟩
  · have := hmem _ hp𝔪
    rwa [map_natCast] at this
  · intro ℓ hℓ hℓN b hTb
    refine ⟨χ (heckeAlgebra.T hℓ hℓN hℓN), ?_, ?_⟩
    · have hTf : ((heckeAlgebra.T hℓ hℓN hℓN : heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = qCoeff f ℓ • f := by
        rw [heckeAlgebra.coe_T]
        exact (((isNormalizedEigenform_iff_heckeTLin f).mp hf).2 ℓ hℓ).1 hℓN
      have h2 := hχ (heckeAlgebra.T hℓ hℓN hℓN)
      rw [hTf] at h2
      have hsub : (qCoeff f ℓ - (χ (heckeAlgebra.T hℓ hℓN hℓN) : ℂ)) • f = 0 := by
        rw [sub_smul, h2, sub_self]
      rcases smul_eq_zero.mp hsub with h0 | h0
      · exact (sub_eq_zero.mp h0).symm
      · exact absurd h0 hf.ne_zero_aux
    · have h := hmem _ hTb
      rwa [map_sub, map_intCast] at h

end CuspForm

end
