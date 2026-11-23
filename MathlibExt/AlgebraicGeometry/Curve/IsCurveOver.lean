/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_IsCurveOver.lean`,
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`,
`Theorems/Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean`
and
`P2M/Sol/S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean`
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

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import MathlibExt.AlgebraicGeometry.Curve.Place

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Etale.Field

@[expose] public section

open KaehlerDifferential

namespace AlgebraicCurve

universe u v

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- A divisor on the curve with function field `F` over `K`: a finitely
supported integer combination of places. -/
abbrev Divisor := Place K F →₀ ℤ

namespace Divisor

variable {K F}

/-- The degree of a divisor, weighted by the degrees of its places. -/
noncomputable def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

@[simp]
theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * v.deg := by
  simp [degree]

/-- The subgroup of divisors of degree zero. -/
noncomputable def degZero : AddSubgroup (Divisor K F) := degree.ker

theorem mem_degZero {D : Divisor K F} :
    D ∈ degZero (K := K) (F := F) ↔ degree D = 0 :=
  Iff.rfl

/-- A divisor is principal if it is the divisor of orders of a single
nonzero function at every place. -/
def IsPrincipal (D : Divisor K F) : Prop :=
  ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f

/-- The subgroup of principal divisors. -/
def principal : AddSubgroup (Divisor K F) where
  carrier := {D | IsPrincipal D}
  zero_mem' := ⟨1, one_ne_zero, fun v => by simp⟩
  add_mem' := by
    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩
    exact ⟨f * g, mul_ne_zero hf hg, fun v => by
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩
  neg_mem' := by
    rintro D ⟨f, hf, hD⟩
    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by
      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩

theorem mem_principal {D : Divisor K F} :
    D ∈ principal (K := K) (F := F) ↔ IsPrincipal D :=
  Iff.rfl

end Divisor

/-- Every nonzero function has a principal divisor of degree zero. This is
the function-field analogue of the product formula. -/
class HasPrincipalDivisors : Prop where
  /-- The divisor of orders of `f` has degree zero. -/
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0

/-- `F` is the function field of a curve over `K`: principal divisors
behave as for a curve, every residue field is finite over `K`, and the
module of Kähler differentials is free of rank one over `F`. -/
class IsCurveOver : Prop extends HasPrincipalDivisors K F where
  /-- Every residue field is finite over `K`. -/
  finiteResidue : ∀ v : Place K F, Module.Finite K v.ResidueField
  /-- The Kähler differentials are free of rank one. -/
  kaehler_free_rank_one : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

namespace IsCurveOver

variable {K F}

theorem hasPrincipalDivisors [h : IsCurveOver K F] : HasPrincipalDivisors K F :=
  h.toHasPrincipalDivisors

theorem finite_residueField [IsCurveOver K F] (v : Place K F) :
    Module.Finite K v.ResidueField :=
  IsCurveOver.finiteResidue v

instance instFiniteResidue [IsCurveOver K F] (v : Place K F) : v.FiniteResidue :=
  ⟨IsCurveOver.finiteResidue v⟩

instance instFreeKaehler [h : IsCurveOver K F] : Module.Free F Ω[F⁄K] :=
  h.kaehler_free_rank_one.1

theorem finrank_kaehler [h : IsCurveOver K F] : Module.finrank F Ω[F⁄K] = 1 :=
  h.kaehler_free_rank_one.2

instance instNontrivialKaehler [IsCurveOver K F] : Nontrivial Ω[F⁄K] :=
  Module.nontrivial_of_finrank_eq_succ (n := 0) finrank_kaehler

end IsCurveOver

namespace Place

variable {K F}

theorem deg_eq_one_of_isAlgClosed_of_finite [IsAlgClosed K] (v : Place K F)
    [Module.Finite K v.ResidueField] : v.deg = 1 := by
  have : Algebra.IsIntegral K v.ResidueField :=
    Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField)
    hbij).toLinearEquiv.finrank_eq).symm

end Place

namespace IsCurveOver

variable {K F}

theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F]
    (v : Place K F) : v.deg = 1 :=
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  v.deg_eq_one_of_isAlgClosed_of_finite

theorem forall_deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] :
    ∀ w : Place K F, w.deg = 1 :=
  deg_eq_one_of_isAlgClosed

theorem not_isSeparable [IsCurveOver K F] : ¬ Algebra.IsSeparable K F := by
  intro hsep
  haveI : Algebra.FormallyUnramified K F :=
    Algebra.FormallyUnramified.of_isSeparable K F
  exact false_of_nontrivial_of_subsingleton Ω[F⁄K]

theorem not_isAlgebraic [PerfectField K] [IsCurveOver K F] :
    ¬ Algebra.IsAlgebraic K F := by
  intro halg
  exact not_isSeparable (K := K) (F := F)
    Algebra.IsAlgebraic.isSeparable_of_perfectField

instance instTranscendental [PerfectField K] [IsCurveOver K F] :
    Algebra.Transcendental K F :=
  Algebra.transcendental_iff_not_isAlgebraic.mpr not_isAlgebraic

theorem exists_transcendental [PerfectField K] [IsCurveOver K F] :
    ∃ t : F, Transcendental K t :=
  Algebra.Transcendental.transcendental

theorem trdeg_pos [PerfectField K] [IsCurveOver K F] :
    0 < Algebra.trdeg K F :=
  _root_.trdeg_pos K F

theorem trdeg_ne_zero [PerfectField K] [IsCurveOver K F] :
    Algebra.trdeg K F ≠ 0 :=
  trdeg_pos.ne'

theorem one_le_trdeg [PerfectField K] [IsCurveOver K F] :
    1 ≤ Algebra.trdeg K F :=
  Cardinal.one_le_iff_pos.mpr trdeg_pos

theorem trdeg_eq_one [PerfectField K] [IsCurveOver K F]
    (htrdeg : Algebra.trdeg K F ≤ 1) : Algebra.trdeg K F = 1 :=
  le_antisymm htrdeg IsCurveOver.one_le_trdeg

end IsCurveOver

open IntermediateField Algebra
open scoped IntermediateField.algebraAdjoinAdjoin

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
variable {ι : Type*} {v : ι → F}

private noncomputable def kaehlerAdjoinBasis (hv : AlgebraicIndependent K v) :
    Module.Basis ι (IntermediateField.adjoin K (Set.range v))
      Ω[(IntermediateField.adjoin K (Set.range v))⁄K] := by
  let Kv : IntermediateField K F := IntermediateField.adjoin K (Set.range v)
  letI : Algebra (MvPolynomial ι K) Kv :=
    ((algebraMap (Algebra.adjoin K (Set.range v)) Kv).comp
      (hv.aevalEquiv : MvPolynomial ι K →+* Algebra.adjoin K (Set.range v))).toAlgebra
  haveI : IsScalarTower K (MvPolynomial ι K) Kv :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K Kv a
        = algebraMap (Algebra.adjoin K (Set.range v)) Kv
          (hv.aevalEquiv (algebraMap K _ a))
      rw [AlgEquiv.commutes]; rfl
  haveI : IsFractionRing (MvPolynomial ι K) Kv :=
    IsFractionRing.of_ringEquiv_left hv.aevalEquiv.toRingEquiv (fun _ => rfl)
  haveI : Algebra.FormallyEtale (MvPolynomial ι K) Kv :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial ι K))
  exact ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange Kv).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (MvPolynomial ι K) Kv)

private noncomputable def kaehlerOfSeparatingTranscendentalBasis (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] :
    Module.Basis ι F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (IntermediateField.adjoin K (Set.range v)) F :=
    Algebra.FormallyEtale.of_isSeparable _ _
  ((kaehlerAdjoinBasis hv).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (IntermediateField.adjoin K (Set.range v)) F)

private theorem finrank_kaehler_eq_card_of_separating {s : Finset F}
    (hs : AlgebraicIndependent K ((↑) : s → F))
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F] :
    Module.finrank F Ω[F⁄K] = s.card := by
  rw [Module.finrank_eq_card_basis (kaehlerOfSeparatingTranscendentalBasis hs),
    Fintype.card_coe]

private theorem finrank_kaehler_eq_card_of_separating' {s : Finset F}
    (hs : AlgebraicIndependent K ((↑) : s → F))
    [hsep : Algebra.IsSeparable (IntermediateField.adjoin K (s : Set F)) F] :
    Module.finrank F Ω[F⁄K] = s.card := by
  have heq : IntermediateField.adjoin K (s : Set F)
      = IntermediateField.adjoin K (Set.range ((↑) : s → F)) := by
    rw [Subtype.range_coe]
  let e : (IntermediateField.adjoin K (s : Set F)) ≃ₐ[K]
      (IntermediateField.adjoin K (Set.range ((↑) : s → F))) :=
    IntermediateField.equivOfEq heq
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F :=
    Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun x => rfl)
  exact finrank_kaehler_eq_card_of_separating hs

namespace IsCurveOver

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem trdeg_le_one [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] : Algebra.trdeg K F ≤ 1 := by
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  haveI := hsep
  have hcard : s.card = 1 := by
    rw [← finrank_kaehler_eq_card_of_separating' hs.1,
      IsCurveOver.finrank_kaehler]
  have htr := hs.cardinalMk_eq_trdeg
  rw [Cardinal.mk_coe_finset, hcard, Nat.cast_one] at htr
  exact htr.symm.le

theorem trdeg_eq_one_of_perfectField [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F = 1 :=
  IsCurveOver.trdeg_eq_one trdeg_le_one

/-- A curve over a perfect field admits a separating transcendental
element: some `t` transcendental over `K` such that `F` is finite and
separable over `K⟮t⟯`. -/
theorem exists_separating_transcendental [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧
      Algebra.IsSeparable K⟮t⟯ F := by
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have hcard : s.card = 1 := by
    have htr := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset,
      IsCurveOver.trdeg_eq_one_of_perfectField] at htr
    exact_mod_cast htr
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
  have htr : Transcendental K t := by
    have h1 := hs.1
    rw [show ((↑) : (↑({t} : Finset F)) → F) = fun _ => t from
      funext fun x => (Finset.mem_singleton.mp x.2).symm ▸ rfl] at h1
    exact (algebraicIndependent_unique_type_iff
      (ι := (↑({t} : Finset F)))).mp h1
  have heq : IntermediateField.adjoin K (↑({t} : Finset F) : Set F) = K⟮t⟯ := by
    rw [Finset.coe_singleton]
  haveI hsep' : Algebra.IsSeparable K⟮t⟯ F :=
    Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.equivOfEq heq).toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun _ => rfl)
  haveI : Algebra.EssFiniteType K⟮t⟯ F :=
    Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  exact ⟨t, htr, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep'⟩

end IsCurveOver

end AlgebraicCurve
