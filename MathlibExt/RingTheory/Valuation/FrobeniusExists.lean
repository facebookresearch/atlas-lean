/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean`,
`P2M/Sol/S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean`,
`Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_rat.lean`
and
`P2M/Sol/S_ValuationSubring_exists_isFrobeniusAt_rat.lean`
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

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import MathlibExt.AlgebraicGeometry.EllipticCurve.FrobeniusTrace
public import MathlibExt.RingTheory.Valuation.LiesOverPrime
import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Valuation.LocalSubring
import MathlibExt.RingTheory.Valuation.IntegralRepresentation

/-!
# Existence of Frobenius elements at places of `AlgebraicClosure ℚ`

Every valuation subring of `AlgebraicClosure ℚ` lying over a rational prime
`q` admits an automorphism over `ℚ` that is Frobenius at `q`, and for every
prime there is such a valuation subring.
-/

@[expose] public section

open scoped Pointwise

namespace ValuationSubring.FrobeniusExistsAux

local notation "ℚ̄" => AlgebraicClosure ℚ

local notation "ℤ̄" => integralClosure ℤ (AlgebraicClosure ℚ)

private theorem coe_mem (A : ValuationSubring ℚ̄) (b : ℤ̄) : (b : ℚ̄) ∈ A := by
  have hb : IsIntegral ℤ (b : ℚ̄) := b.2
  have hbA : IsIntegral A (b : ℚ̄) := by
    obtain ⟨p, hp, hpb⟩ := hb
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap A ℚ̄).comp (Int.castRingHom A) = algebraMap ℤ ℚ̄ :=
      RingHom.ext_int _ _
    rw [this]
    exact hpb
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := ℚ̄)).mp hbA
  rw [← hy]
  exact y.2

private noncomputable def toPlace (A : ValuationSubring ℚ̄) : ℤ̄ →+* A :=
  ((Subalgebra.val ℤ̄).toRingHom).codRestrict A.toSubring (coe_mem A)

private theorem coe_toPlace (A : ValuationSubring ℚ̄) (b : ℤ̄) :
    (toPlace A b : ℚ̄) = b :=
  rfl

private noncomputable def center (A : ValuationSubring ℚ̄) : Ideal ℤ̄ :=
  Ideal.comap (toPlace A) (IsLocalRing.maximalIdeal A)

private theorem mem_center_iff {A : ValuationSubring ℚ̄} {b : ℤ̄} :
    b ∈ center A ↔ (b : ℚ̄) ∈ A.nonunits := by
  rw [center, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, coe_toPlace]

private instance center_isPrime (A : ValuationSubring ℚ̄) : (center A).IsPrime :=
  Ideal.comap_isPrime _ _

private theorem center_under {q : ℕ} (hq : q.Prime) {A : ValuationSubring ℚ̄}
    (hA : A.LiesOverPrime q) : (center A).under ℤ = Ideal.span {(q : ℤ)} := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
  refine (hmax.eq_of_le ?_ ?_).symm
  · exact Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ ℤ̄ (q : ℤ) ∈ center A
    rw [mem_center_iff]
    have : ((algebraMap ℤ ℤ̄ (q : ℤ) : ℤ̄) : ℚ̄) = (q : ℚ̄) := by
      rw [map_natCast]; rfl
    rw [this]
    exact hA

private theorem mem_smul_nonunits_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {τ : L ≃ₐ[K] L} {A : ValuationSubring L} {x : L} :
    x ∈ (τ • A).nonunits ↔ τ.symm x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  have e0 : x = 0 ↔ τ.symm x = 0 := by
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h; simpa using congrArg τ h
  have e1 : x⁻¹ ∈ τ • A ↔ (τ.symm x)⁻¹ ∈ A := by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have : (τ⁻¹ : L ≃ₐ[K] L) • x⁻¹ = (τ.symm x)⁻¹ := by
      change τ.symm x⁻¹ = (τ.symm x)⁻¹
      exact map_inv₀ _ _
    rw [this]
  rw [e0, e1]

private theorem le_of_forall_notMem_nonunits {q : ℕ} (hq : q.Prime)
    {V W : ValuationSubring ℚ̄} (hV : V.LiesOverPrime q)
    (h : ∀ s : ℤ̄, (s : ℚ̄) ∉ V.nonunits → (s : ℚ̄) ∉ W.nonunits) : V ≤ W := by
  intro x hx
  obtain ⟨x', s, hs, hxs⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime V hq hV x hx
  have hsW : (s : ℚ̄) ∉ W.nonunits := h s hs
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hsW
  obtain ⟨hs0, hsinv⟩ := hsW
  have hx_eq : x = (x' : ℚ̄) * (s : ℚ̄)⁻¹ := by
    rw [← hxs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hx_eq]
  exact W.mul_mem _ _ (coe_mem W x') hsinv

private theorem smul_eq_of_smul_center_eq {q : ℕ} (hq : q.Prime) {A : ValuationSubring ℚ̄}
    (hA : A.LiesOverPrime q) {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g • center A = center A) :
    g • A = A := by
  classical
  have key : ∀ s : ℤ̄, (s : ℚ̄) ∈ (g • A).nonunits ↔ (s : ℚ̄) ∈ A.nonunits := by
    intro s
    rw [mem_smul_nonunits_iff, ← mem_center_iff (A := A), ← hg,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_center_iff]
    have : ((g⁻¹ • s : ℤ̄) : ℚ̄) = g.symm s := by
      rw [integralClosure.coe_smul, AlgEquiv.smul_def, AlgEquiv.aut_inv]
    rw [this]
  have hgA : (g • A).LiesOverPrime q := by
    change (q : ℚ̄) ∈ (g • A).nonunits
    rw [mem_smul_nonunits_iff, map_natCast]
    exact hA
  apply le_antisymm
  · exact le_of_forall_notMem_nonunits hq hgA fun s hs => fun h => hs ((key s).mpr h)
  · exact le_of_forall_notMem_nonunits hq hA fun s hs => fun h => hs ((key s).mp h)

private theorem exists_frobenius_algEquiv {q : ℕ} (hq : q.Prime) {A : ValuationSubring ℚ̄}
    [(center A).LiesOver (Ideal.span {(q : ℤ)})] :
    ∃ f : (ℤ̄ ⧸ center A) ≃ₐ[ℤ ⧸ Ideal.span {(q : ℤ)}] (ℤ̄ ⧸ center A),
      ∀ b : ℤ̄, f (Ideal.Quotient.mk (center A) b) = (Ideal.Quotient.mk (center A) b) ^ q := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hqmem : ((q : ℤ) : ℤ̄) ∈ center A := by
    have := (Ideal.mem_of_liesOver (center A) (Ideal.span {(q : ℤ)}) (q : ℤ)).mp
      (Ideal.mem_span_singleton_self _)
    simpa using this
  have : CharP (ℤ̄ ⧸ center A) q := by
    rw [CharP.charP_iff_prime_eq_zero hq]
    have : ((q : ℕ) : ℤ̄ ⧸ center A) = Ideal.Quotient.mk (center A) ((q : ℤ) : ℤ̄) := by
      simp
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hqmem
  let fr : (ℤ̄ ⧸ center A) →+* (ℤ̄ ⧸ center A) := frobenius (ℤ̄ ⧸ center A) q
  let fa : (ℤ̄ ⧸ center A) →ₐ[ℤ ⧸ Ideal.span {(q : ℤ)}] (ℤ̄ ⧸ center A) :=
    { fr with
      commutes' := fun r => by
        obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
        change fr (Ideal.Quotient.mk (center A) (algebraMap ℤ ℤ̄ n)) =
          Ideal.Quotient.mk (center A) (algebraMap ℤ ℤ̄ n)
        rw [eq_intCast, map_intCast, map_intCast] }
  have fa_apply : ∀ y, fa y = y ^ q := fun y => rfl
  have hinj : Function.Injective fa := by
    intro y₁ y₂ h
    rw [fa_apply, fa_apply] at h
    exact frobenius_inj (ℤ̄ ⧸ center A) q h
  have hsurj : Function.Surjective fa := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (b : ℚ̄) hq.pos
    have hcint : IsIntegral ℤ c := by
      refine IsIntegral.of_pow hq.pos ?_
      rw [hc]; exact b.2
    refine ⟨Ideal.Quotient.mk (center A) ⟨c, hcint⟩, ?_⟩
    rw [fa_apply, ← map_pow]
    congr 1
    exact Subtype.ext hc
  exact ⟨AlgEquiv.ofBijective fa ⟨hinj, hsurj⟩, fun b => rfl⟩

end ValuationSubring.FrobeniusExistsAux

namespace ValuationSubring

open FrobeniusExistsAux

/-- Every valuation subring of `AlgebraicClosure ℚ` lying over a rational
prime `q` admits an automorphism over `ℚ` that is Frobenius at `q` for it. -/
public theorem exists_isFrobeniusAt_of_liesOverPrime {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), A.IsFrobeniusAt φ q := by
  classical
  have : IsGalois ℚ (AlgebraicClosure ℚ) := by
    have h : @IsGalois ℚ _ (AlgebraicClosure ℚ) _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h
  have : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _
        (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact Algebra.isAlgebraic_iff_isIntegral.mp h
  let _ : TopologicalSpace (integralClosure ℤ (AlgebraicClosure ℚ)) := ⊥
  have : DiscreteTopology (integralClosure ℤ (AlgebraicClosure ℚ)) := ⟨rfl⟩
  have : ContinuousSMul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    have : FiniteDimensional ℚ
        (IntermediateField.adjoin ℚ {(b : AlgebraicClosure ℚ)}) :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (b : AlgebraicClosure ℚ))
    refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen
      (IntermediateField.adjoin ℚ {(b : AlgebraicClosure ℚ)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g • (b : AlgebraicClosure ℚ) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ (b : AlgebraicClosure ℚ))
  have : Algebra.IsInvariant ℤ (integralClosure ℤ (AlgebraicClosure ℚ))
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := ⟨fun b hb => by
    have hb' : (b : AlgebraicClosure ℚ) ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : integralClosure ℤ (AlgebraicClosure ℚ) =>
        (z : AlgebraicClosure ℚ)) (hb g)
    obtain ⟨r, hr⟩ := hb'
    have hrint : IsIntegral ℤ r := by
      have h := b.2
      rw [mem_integralClosure_iff, ← hr] at h
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ (AlgebraicClosure ℚ))
        (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mp h
    obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hrint
    refine ⟨n, Subtype.ext ?_⟩
    change ((algebraMap ℤ (integralClosure ℤ (AlgebraicClosure ℚ)) n :
      integralClosure ℤ (AlgebraicClosure ℚ)) : AlgebraicClosure ℚ) = b
    rw [← hr, ← hn]
    simp⟩
  have : (center A).LiesOver (Ideal.span {(q : ℤ)}) := ⟨(center_under hq hA).symm⟩
  obtain ⟨f, hf⟩ := exists_frobenius_algEquiv (A := A) hq
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Ideal.span {(q : ℤ)}) (center A) f
  have hgQ : (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • center A = center A := g.2
  have hgA : (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • A = A :=
    smul_eq_of_smul_center_eq hq hA hgQ
  have hgD : (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈
      A.decompositionSubgroup ℚ := MulAction.mem_stabilizer_iff.mpr hgA
  refine ⟨g, hgD, ?_⟩
  let ψ : integralClosure ℤ (AlgebraicClosure ℚ) →+* IsLocalRing.ResidueField A :=
    (IsLocalRing.residue A).comp (toPlace A)
  have hψ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
      ψ ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • b) = ψ b ^ q := by
    intro b
    have h1 : Ideal.Quotient.mk (center A) (g • b) =
        (Ideal.Quotient.mk (center A) b) ^ q := by
      rw [← hf b, ← hg, Ideal.Quotient.stabilizerHom_apply]
    rw [← map_pow, Ideal.Quotient.eq] at h1
    have h1' : toPlace A (g • b) - toPlace A (b ^ q) ∈ IsLocalRing.maximalIdeal A := by
      have := (Ideal.mem_comap (f := toPlace A)).mp h1
      rwa [map_sub] at this
    have h2 := (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal A)).mpr h1'
    change IsLocalRing.residue A
        (toPlace A ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • b)) =
      (IsLocalRing.residue A (toPlace A b)) ^ q
    rw [← map_pow, ← map_pow]
    exact h2
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨x', s, hs, hxs⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime A hq hA a a.2
  set d : A.decompositionSubgroup ℚ := ⟨g, hgD⟩
  have hψs : ψ s ≠ 0 := by
    intro h0
    apply hs
    have : toPlace A s ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.residue_eq_zero_iff _).mp h0
    rw [← ValuationSubring.coe_mem_nonunits_iff] at this
    exact this
  have e1 : a * toPlace A s = toPlace A x' := Subtype.ext hxs
  have e2 : (d • a) * toPlace A ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • s) =
      toPlace A ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • x') := by
    apply Subtype.ext
    change (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : AlgebraicClosure ℚ) *
        (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : AlgebraicClosure ℚ) =
      (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x' : AlgebraicClosure ℚ)
    rw [← map_mul, hxs]
  have e1' : IsLocalRing.residue A a * ψ s = ψ x' := by
    change IsLocalRing.residue A a * IsLocalRing.residue A (toPlace A s) =
      IsLocalRing.residue A (toPlace A x')
    rw [← map_mul, e1]
  have e2' : IsLocalRing.residue A (d • a) *
      ψ ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • s) =
      ψ ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • x') := by
    change IsLocalRing.residue A (d • a) * IsLocalRing.residue A
        (toPlace A ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • s)) =
      IsLocalRing.residue A
        (toPlace A ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • x'))
    rw [← map_mul, e2]
  rw [hψ s, hψ x', ← e1', mul_pow] at e2'
  have hcancel := mul_right_cancel₀ (pow_ne_zero q hψs) e2'
  change d • IsLocalRing.residue A a = (IsLocalRing.residue A a) ^ q
  have : d • (IsLocalRing.residue A a) = IsLocalRing.residue A (d • a) :=
    (IsLocalRing.ResidueField.residue_smul (A.decompositionSubgroup ℚ) d a).symm
  exact this.trans hcancel

/-- For every prime `ℓ` there is a valuation subring of `AlgebraicClosure ℚ`
lying over `ℓ`, together with an automorphism over `ℚ` that is Frobenius at
`ℓ` for it. -/
public theorem exists_isFrobeniusAt_rat (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ ∧
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ := by
  classical
  let O : Subalgebra ℤ (AlgebraicClosure ℚ) := integralClosure ℤ (AlgebraicClosure ℚ)
  have hℓZ : Prime (ℓ : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hℓ)
  have hPmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hℓZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ O) ≤ Ideal.span {(ℓ : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ O).injective_int]
    exact bot_le
  obtain ⟨𝔔, h𝔔max, h𝔔⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := O) (Ideal.span {(ℓ : ℤ)}) hker
  have hℓ𝔔 : (ℓ : O) ∈ 𝔔 := by
    have h : (ℓ : ℤ) ∈ 𝔔.under ℤ := by
      rw [h𝔔]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_under] using h
  obtain ⟨A, -, h𝔔A⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (A := O.toSubring) 𝔔 h𝔔max.ne_top
  have hA : A.LiesOverPrime ℓ := by
    have h : ((ℓ : O) : AlgebraicClosure ℚ) ∈ A.nonunits := h𝔔A ⟨(ℓ : O), hℓ𝔔, rfl⟩
    exact h
  obtain ⟨φ, hφ⟩ := exists_isFrobeniusAt_of_liesOverPrime hℓ A hA
  exact ⟨A, hA, φ, hφ⟩

end ValuationSubring
