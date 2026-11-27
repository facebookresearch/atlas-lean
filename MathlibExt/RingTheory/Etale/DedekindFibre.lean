/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt.lean`
and
`P2M/Sol/S_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt.lean`
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

public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Surjective
import MathlibExt.FieldTheory.SeparableAdjoinRoot

@[expose] public section

open Polynomial

private theorem formallyUnramified_quotient_of_forall
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (I : Ideal B)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], I ≤ P → Algebra.IsUnramifiedAt R P) :
    Algebra.FormallyUnramified R (B ⧸ I) := by
  rw [Algebra.formallyUnramified_iff_forall]
  intro Q
  let P : Ideal B := Q.1.comap (Ideal.Quotient.mk I)
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hIP : I ≤ P := fun x hx => by
    change Ideal.Quotient.mk I x ∈ Q.1
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact Q.1.zero_mem
  have : Algebra.IsUnramifiedAt R P := hunr P hIP
  let φ : Localization.AtPrime P →+* Localization.AtPrime Q.1 :=
    Localization.localRingHom P Q.1 (Ideal.Quotient.mk I) rfl
  have hφ : Function.Surjective φ :=
    RingHom.surjective_localRingHom_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective Q.1
  have hφalg : ∀ r : R, φ (algebraMap R _ r) = algebraMap R _ r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime P),
      Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply R (B ⧸ I) (Localization.AtPrime Q.1)]
    rfl
  let φa : Localization.AtPrime P →ₐ[R] Localization.AtPrime Q.1 :=
    { φ with commutes' := hφalg }
  exact Algebra.FormallyUnramified.of_surjective φa hφ

/-- **Étale fibre at a separable irreducible polynomial.** Let $k$ be a field and let $B$ be a
commutative ring that is an algebra over $k[X]$, and over $k$ through $k[X]$, such that $B$ is a
finite and torsion-free $k[X]$-module. Let $h \in k[X]$ be irreducible and separable, and suppose
that $B$ is unramified over $k[X]$ at every nonzero prime ideal of $B$ that contains the image of
$h$. Then the fibre $B / hB$ is an étale $k$-algebra. There is no domain or nontriviality
hypothesis on $B$: the statement covers products such as $k[X] \times k[X]$, and the zero ring,
whose fibre is zero. -/
public theorem Algebra.etale_quotient_map_span_of_forall_isUnramifiedAt
    {k : Type*} [Field k] (B : Type*) [CommRing B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B]
    [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hirr : Irreducible h) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ →
      Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) := by
  classical
  set I : Ideal B := Ideal.map (algebraMap k[X] B) (Ideal.span {h}) with hI
  have h0 : h ≠ 0 := hirr.ne_zero
  have hU : Algebra.FormallyUnramified k[X] (B ⧸ I) := by
    refine formallyUnramified_quotient_of_forall I (fun P hP hIP => ?_)
    have hhP : algebraMap k[X] B h ∈ P :=
      hIP (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self h))
    have hP0 : P ≠ ⊥ := fun hPbot => by
      -- `h • 1 = 0` in `B` would force `1 = 0`, i.e. `1 ∈ P`.
      rw [hPbot, Ideal.mem_bot, Algebra.algebraMap_eq_smul_one, smul_eq_zero] at hhP
      refine hhP.elim h0 fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 ?_)
      rw [h1]; exact P.zero_mem
    refine hunr P hP0 ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; exact hhP
  set 𝔪 : Ideal k[X] := I.comap (algebraMap k[X] B) with h𝔪
  have hle : Ideal.span {h} ≤ 𝔪 := Ideal.le_comap_map.trans (le_of_eq rfl)
  have hmax : (Ideal.span {h}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hirr
  have : Algebra.FiniteType k B :=
    Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  have : Algebra.FiniteType k (B ⧸ I) :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom k B (B ⧸ I))
      Ideal.Quotient.mk_surjective
  have : Algebra.FinitePresentation k (B ⧸ I) :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := B ⧸ I)).mp inferInstance
  by_cases hItop : I = ⊤
  · have : Subsingleton (B ⧸ I) := Ideal.Quotient.subsingleton_iff.2 hItop
    have : Algebra.FormallyUnramified k (B ⧸ I) :=
      Algebra.FormallyUnramified.of_surjective (Algebra.ofId k (B ⧸ I))
        (fun b => ⟨0, Subsingleton.elim _ _⟩)
    exact ⟨Algebra.FormallyEtale.of_formallyUnramified_of_field k (B ⧸ I), inferInstance⟩
  · have h𝔪ne : 𝔪 ≠ ⊤ := by
      intro htop
      apply hItop
      rw [Ideal.eq_top_iff_one]
      have : (1 : k[X]) ∈ 𝔪 := by rw [htop]; trivial
      simpa using (Ideal.mem_comap.1 this)
    have h𝔪eq : 𝔪 = Ideal.span {h} := (hmax.eq_of_le h𝔪ne hle).symm
    have : 𝔪.IsMaximal := h𝔪eq ▸ hmax
    let : Field (k[X] ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    -- `𝔪` is generated by the monic associate of `h`, which is irreducible and separable.
    have hu : IsUnit (C h.leadingCoeff⁻¹) := (inv_ne_zero (leadingCoeff_ne_zero.2 h0)).isUnit.map C
    have hf := associated_mul_unit_right h _ hu
    have e : (k[X] ⧸ 𝔪) ≃ₐ[k] AdjoinRoot (h * C h.leadingCoeff⁻¹) :=
      Ideal.quotientEquivAlgOfEq k (by rw [h𝔪eq, Ideal.span_singleton_mul_right_unit hu])
    have := (AdjoinRoot.powerBasis (monic_mul_leadingCoeff_inv h0).ne_zero).finite
    have : FiniteDimensional k (k[X] ⧸ 𝔪) := Module.Finite.equiv e.symm.toLinearEquiv
    have hsepK : Algebra.IsSeparable k (k[X] ⧸ 𝔪) :=
      (Algebra.isSeparable_iff_exists_monic_irreducible_separable k (k[X] ⧸ 𝔪)).2
        ⟨_, monic_mul_leadingCoeff_inv h0, hf.irreducible hirr, hsep.of_dvd hf.symm.dvd, ⟨e⟩⟩
    have : Algebra.FormallyUnramified k (k[X] ⧸ 𝔪) := by
      have := hsepK; exact Algebra.FormallyUnramified.of_isSeparable k (k[X] ⧸ 𝔪)
    have : Algebra.FormallyUnramified (k[X] ⧸ 𝔪) (B ⧸ I) :=
      Algebra.FormallyUnramified.of_restrictScalars k[X] (k[X] ⧸ 𝔪) (B ⧸ I)
    have : IsScalarTower k (k[X] ⧸ 𝔪) (B ⧸ I) := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply k k[X] (B ⧸ I),
        IsScalarTower.algebraMap_apply k k[X] (k[X] ⧸ 𝔪),
        IsScalarTower.algebraMap_apply k[X] (k[X] ⧸ 𝔪) (B ⧸ I)])
    have : Algebra.FormallyUnramified k (B ⧸ I) :=
      Algebra.FormallyUnramified.comp k (k[X] ⧸ 𝔪) (B ⧸ I)
    exact ⟨Algebra.FormallyEtale.of_formallyUnramified_of_field k (B ⧸ I), inferInstance⟩

/-- **Étale fibre of a Dedekind domain at a separable irreducible polynomial.** Let $k$ be a field
and let $B$ be a Dedekind domain that is an algebra over $k[X]$, and over $k$ through $k[X]$, such
that $B$ is a finite and torsion-free $k[X]$-module. Let $h \in k[X]$ be irreducible and
separable, and suppose that $B$ is unramified over $k[X]$ at every nonzero prime ideal of $B$ that
contains the image of $h$. Then the fibre $B / hB$ is an étale $k$-algebra. This is the form in
which the source states the result; it is the Dedekind-domain case of
`Algebra.etale_quotient_map_span_of_forall_isUnramifiedAt`, which needs no hypothesis on $B$
beyond finiteness and torsion-freeness. -/
public theorem IsDedekindDomain.etale_quotient_map_span_of_forall_isUnramifiedAt
    {k : Type*} [Field k] (B : Type*) [CommRing B] [IsDedekindDomain B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B]
    [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hirr : Irreducible h) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ →
      Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) :=
  Algebra.etale_quotient_map_span_of_forall_isUnramifiedAt B h hirr hsep hunr
