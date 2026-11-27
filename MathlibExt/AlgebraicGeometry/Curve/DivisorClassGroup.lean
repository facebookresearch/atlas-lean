/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import MathlibExt.AlgebraicGeometry.Curve.ChartDichotomy
public import MathlibExt.AlgebraicGeometry.Curve.LPolynomial
public import MathlibExt.AlgebraicGeometry.Curve.Place
public import MathlibExt.AlgebraicGeometry.Curve.PlaceCongr
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Ring.Subring.Pointwise
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Divisors and principal divisors of a function field

The degree of a place, divisors, their degree map, principal divisors and the class group
`Pic0` are defined in `MathlibExt.AlgebraicGeometry.Curve.LPolynomial`, and the residue field
`AlgebraicCurve.Place.ResidueField` in `MathlibExt.AlgebraicGeometry.Curve.ChartDichotomy`. This
file adds the order criterion `Place.ord_eq_zero_iff_adicValuation_eq_one`, the condition that
every nonzero function has a principal divisor of degree zero (`HasPrincipalDivisors`), the full
class group `Pic`, the condition `AbelJacobiCard` counting the `p ^ n`-torsion of `Pic0` (stated
with Mathlib's `AddSubgroup.torsionBy`), the action of `F ≃ₐ[K] F` on places, divisors and `Pic0`,
and the places attached to height-one primes of a Dedekind domain with fraction field `F`. The
action on places is the transport `Place.congrRingEquiv` of
`MathlibExt.AlgebraicGeometry.Curve.PlaceCongr` along `σ`, and its effect on orders, residue fields
and degrees is read off from that transport.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F} (v : Place K F)

theorem ord_eq_zero_iff_adicValuation_eq_one {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by
  simp only [ord, neg_eq_zero]
  constructor
  · intro h
    have h2 := exp_log (v.adicValuation_ne_zero hf)
    rw [h, exp_zero] at h2
    exact h2.symm
  · intro h
    rw [h, log_one]

end Place

class HasPrincipalDivisors : Prop where
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0

abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal (K := K) (F := F)

namespace Pic0

variable {K F}

@[simp]
theorem mk_zero : mk (0 : Divisor.degZero (K := K) (F := F)) = 0 := rfl

end Pic0

/-- **Torsion count of `Pic0`.** `AbelJacobiCard K F p g` says that `p` is prime and that, for every
`n`, the `p ^ n`-torsion subgroup `AddSubgroup.torsionBy (Pic0 K F) (p ^ n)` has `p ^ (2 * g * n)`
elements. This is the count expected when `F` is the function field of a curve of genus `g` over an
algebraically closed field `K` and `p` is different from the characteristic of `K`. Since
`p ^ (2 * g * n)` is positive for a prime `p`, the condition forces every `p ^ n`-torsion subgroup
to be finite (`Nat.card` is `0` on an infinite type). Primality is part of the condition because
the count is degenerate otherwise: for `p = 1` it holds for every `g`, and for `p = 0` and `g ≥ 1`
it only says that `Pic0 K F` is infinite. -/
def AbelJacobiCard (p : ℕ) (g : ℕ) : Prop :=
  p.Prime ∧ ∀ n : ℕ, Nat.card (AddSubgroup.torsionBy (Pic0 K F) (p ^ n : ℕ)) = p ^ (2 * g * n)

namespace Place

open scoped Pointwise

variable {K F}
variable (σ : F ≃ₐ[K] F)

/-- Pulling a valuation subring back along `σ.symm` is taking its image under `σ`. -/
private theorem comap_symm_eq_smul (A : ValuationSubring F) :
    A.comap (σ.toRingEquiv.symm : F →+* F) = σ • A := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

/-- The ring isomorphism from a valuation subring `A` of `F` onto its image `σ • A`, given by
`σ`. -/
def smulRingEquiv (A : ValuationSubring F) : A ≃+* (σ • A : ValuationSubring F) :=
  (comapSymmRingEquiv σ.toRingEquiv A).trans
    (RingEquiv.subringCongr (by exact congrArg ValuationSubring.toSubring (comap_symm_eq_smul σ A)))

@[simp]
theorem coe_smulRingEquiv_apply (A : ValuationSubring F) (x : A) :
    ((smulRingEquiv σ A x : (σ • A : ValuationSubring F)) : F) = σ x := rfl

/-- An automorphism `σ` of `F` over `K` sends a place `v` to its transport
`Place.congrRingEquiv σ.toRingEquiv σ.commutes v`, whose valuation subring is the image
`σ • v.toValuationSubring` (`smul_toValuationSubring`). -/
instance : SMul (F ≃ₐ[K] F) (Place K F) where
  smul σ v := congrRingEquiv σ.toRingEquiv σ.commutes v

variable (v : Place K F)

@[simp]
theorem smul_toValuationSubring : (σ • v).toValuationSubring = σ • v.toValuationSubring :=
  comap_symm_eq_smul σ v.toValuationSubring

/-- The action of the automorphisms of `F` over `K` on places. -/
instance : MulAction (F ≃ₐ[K] F) (Place K F) where
  one_smul v := by
    ext1
    rw [smul_toValuationSubring, one_smul]
  mul_smul σ τ v := by
    ext1
    simp only [smul_toValuationSubring]
    rw [mul_smul]

theorem ord_smul (f : F) : (σ • v).ord (σ f) = v.ord f :=
  ord_congrRingEquiv σ.toRingEquiv σ.commutes v f

/-- The `K`-algebra isomorphism from the residue field of `v` onto that of `σ • v` induced by
`σ`. -/
def smulResidueAlgEquiv : v.ResidueField ≃ₐ[K] (σ • v).ResidueField :=
  congrResidueAlgEquiv σ.toRingEquiv σ.commutes v

@[simp]
theorem deg_smul : (σ • v).deg = v.deg :=
  deg_congrRingEquiv σ.toRingEquiv σ.commutes v

end Place

namespace Divisor

open scoped Pointwise

variable {K F}

/-- An automorphism `σ` of `F` over `K` moves a divisor along its action on places:
`(σ • D) (σ • v) = D v`. -/
instance : DistribMulAction (F ≃ₐ[K] F) (Divisor K F) := Finsupp.comapDistribMulAction

theorem smul_def (σ : F ≃ₐ[K] F) (D : Divisor K F) :
    σ • D = Finsupp.mapDomain (σ • ·) D := rfl

@[simp]
theorem smul_single (σ : F ≃ₐ[K] F) (v : Place K F) (n : ℤ) :
    σ • Finsupp.single v n = Finsupp.single (σ • v) n := by
  rw [smul_def, Finsupp.mapDomain_single]

theorem smul_apply_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) (v : Place K F) :
    (σ • D) (σ • v) = D v := by
  rw [smul_def]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective σ) D v

theorem smul_apply (σ : F ≃ₐ[K] F) (D : Divisor K F) (w : Place K F) :
    (σ • D) w = D (σ⁻¹ • w) := by
  have : (σ • D) (σ • (σ⁻¹ • w)) = D (σ⁻¹ • w) := smul_apply_smul σ D (σ⁻¹ • w)
  rwa [smul_inv_smul] at this

@[simp]
theorem degree_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) : degree (σ • D) = degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, ih, smul_single, degree_single, degree_single,
        Place.deg_smul]

theorem smul_mem_degZero (σ : F ≃ₐ[K] F) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) : σ • D ∈ degZero (K := K) (F := F) := by
  rwa [mem_degZero, degree_smul]

theorem smul_mem_principal (σ : F ≃ₐ[K] F) {D : Divisor K F}
    (hD : D ∈ principal (K := K) (F := F)) : σ • D ∈ principal (K := K) (F := F) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨σ f, by simpa using hf, fun w => ?_⟩
  rw [smul_apply, hD (σ⁻¹ • w)]
  have h := Place.ord_smul σ (σ⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

end Divisor

namespace Pic0

open scoped Pointwise

variable {K F}

/-- The action of `σ` on divisors of degree zero, as an additive endomorphism of
`Divisor.degZero`. It preserves principal divisors, so it descends to the action of `σ` on
`Pic0 K F`. -/
def degZeroSMulHom (σ : F ≃ₐ[K] F) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((DistribSMul.toAddMonoidHom (Divisor K F) σ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.smul_mem_degZero σ D.2)

@[simp]
theorem coe_degZeroSMulHom (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroSMulHom σ D : Divisor K F) = σ • (D : Divisor K F) := rfl

/-- An automorphism `σ` of `F` over `K` acts on `Pic0 K F` through `degZeroSMulHom σ`. -/
instance : SMul (F ≃ₐ[K] F) (Pic0 K F) where
  smul σ := QuotientAddGroup.map _ _ (degZeroSMulHom σ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.smul_mem_principal σ hD)

theorem smul_mk (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    σ • (mk D) = mk (degZeroSMulHom σ D) := rfl

/-- The action of the automorphisms of `F` over `K` on `Pic0 K F`. -/
instance : DistribMulAction (F ≃ₐ[K] F) (Pic0 K F) where
  one_smul x := by
    obtain ⟨D, rfl⟩ := mk_surjective x
    rw [smul_mk]
    exact congrArg mk (Subtype.ext (by rw [coe_degZeroSMulHom, one_smul]))
  mul_smul σ τ x := by
    obtain ⟨D, rfl⟩ := mk_surjective x
    rw [smul_mk, smul_mk, smul_mk]
    exact congrArg mk (Subtype.ext (by simp only [coe_degZeroSMulHom]; rw [mul_smul]))
  smul_zero σ := by
    change σ • mk 0 = mk 0
    rw [smul_mk]
    exact congrArg mk (map_zero _)
  smul_add σ x y := by
    obtain ⟨D, rfl⟩ := mk_surjective x
    obtain ⟨E, rfl⟩ := mk_surjective y
    change σ • mk (D + E) = mk (degZeroSMulHom σ D) + mk (degZeroSMulHom σ E)
    rw [smul_mk]
    exact congrArg mk (map_add _ _ _)

end Pic0

namespace Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

open IsDedekindDomain.HeightOneSpectrum in
theorem isPrincipalIdealRing_valuationSubring (w : HeightOneSpectrum R) :
    IsPrincipalIdealRing ((w.valuation F).valuationSubring) := by
  rw [show (w.valuation F).valuationSubring = valuationSubringAtPrime F w from
    (valuationSubringAtPrime_eq_valuationSubring (K := F) w).symm]
  infer_instance

open IsDedekindDomain.HeightOneSpectrum in
def ofHeightOneSpectrum [Algebra K R] [IsScalarTower K R F] (w : HeightOneSpectrum R) :
    Place K F where
  toValuationSubring := (w.valuation F).valuationSubring
  algebraMap_mem' := fun a => by
    rw [Valuation.mem_valuationSubring_iff, IsScalarTower.algebraMap_apply K R F]
    exact w.valuation_le_one (algebraMap K R a)
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := isPrincipalIdealRing_valuationSubring w

@[simp]
theorem ofHeightOneSpectrum_toValuationSubring [Algebra K R] [IsScalarTower K R F]
    (w : HeightOneSpectrum R) :
    (ofHeightOneSpectrum (K := K) w).toValuationSubring = (w.valuation F).valuationSubring :=
  rfl

end Place

end AlgebraicCurve
