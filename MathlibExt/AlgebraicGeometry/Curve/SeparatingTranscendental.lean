/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean`
and
`P2M/Sol/S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOver
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Etale.Field

/-!
# Separating transcendental elements of curve function fields

This file proves that the function field of a curve over a perfect field has a separating
transcendental element.

## Main statement

* `AlgebraicCurve.IsCurveOver.exists_separating_transcendental`
-/

namespace CurveGenus.SeparatingTranscendental

set_option linter.unusedSectionVars false
noncomputable section

open KaehlerDifferential Algebra IntermediateField

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace IsCurveOver
open _root_.AlgebraicCurve.IsCurveOver

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem not_isSeparable [IsCurveOver K F] : ¬ Algebra.IsSeparable K F := by
  intro hsep
  have : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  exact false_of_nontrivial_of_subsingleton Ω[F⁄K]

private theorem not_isAlgebraic [PerfectField K] [IsCurveOver K F] :
    ¬ Algebra.IsAlgebraic K F := by
  intro halg
  exact not_isSeparable (K := K) (F := F) Algebra.IsAlgebraic.isSeparable_of_perfectField

private scoped instance instTranscendental [PerfectField K] [IsCurveOver K F] :
    Algebra.Transcendental K F :=
  Algebra.transcendental_iff_not_isAlgebraic.mpr not_isAlgebraic

private theorem exists_transcendental [PerfectField K] [IsCurveOver K F] :
    ∃ t : F, Transcendental K t :=
  Algebra.Transcendental.transcendental

private theorem trdeg_pos [PerfectField K] [IsCurveOver K F] :
    0 < Algebra.trdeg K F :=
  _root_.trdeg_pos K F

private theorem trdeg_ne_zero [PerfectField K] [IsCurveOver K F] :
    Algebra.trdeg K F ≠ 0 :=
  trdeg_pos.ne'

private theorem one_le_trdeg [PerfectField K] [IsCurveOver K F] :
    1 ≤ Algebra.trdeg K F :=
  Cardinal.one_le_iff_pos.mpr trdeg_pos

end IsCurveOver
open scoped _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve.IsCurveOver

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open scoped _root_.AlgebraicCurve.IsCurveOver in
private theorem IsCurveOver.trdeg_eq_one [PerfectField K] [IsCurveOver K F]
    (htrdeg : Algebra.trdeg K F ≤ 1) :
    Algebra.trdeg K F = 1 :=
  le_antisymm htrdeg IsCurveOver.one_le_trdeg

end AlgebraicCurve
open scoped _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve.IsCurveOver
    _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve

noncomputable section

open _root_.KaehlerDifferential
open _root_.IntermediateField
open _root_.TensorProduct
open _root_.Algebra.TensorProduct
open _root_.Module
open scoped IntermediateField.algebraAdjoinAdjoin

namespace AlgebraicCurve
open _root_.AlgebraicCurve

universe u₁ u₂

variable {K : Type u₁} {F : Type u₂} [Field K] [Field F] [Algebra K F]

variable {ι : Type*} {v : ι → F}

private def kaehlerAdjoinBasis (hv : AlgebraicIndependent K v) :
    Basis ι (IntermediateField.adjoin K (Set.range v))
      Ω[(IntermediateField.adjoin K (Set.range v))⁄K] := by
  let Kv : IntermediateField K F := IntermediateField.adjoin K (Set.range v)
  letI : Algebra (MvPolynomial ι K) Kv :=
    ((algebraMap (Algebra.adjoin K (Set.range v)) Kv).comp
      (hv.aevalEquiv : MvPolynomial ι K →+* Algebra.adjoin K (Set.range v))).toAlgebra
  haveI : IsScalarTower K (MvPolynomial ι K) Kv :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap K Kv a
        = algebraMap (Algebra.adjoin K (Set.range v)) Kv (hv.aevalEquiv (algebraMap K _ a))
      rw [AlgEquiv.commutes]; rfl
  haveI : IsFractionRing (MvPolynomial ι K) Kv :=
    IsFractionRing.of_ringEquiv_left hv.aevalEquiv.toRingEquiv (fun _ => rfl)
  haveI : Algebra.FormallyEtale (MvPolynomial ι K) Kv :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial ι K))
  exact ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange Kv).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial ι K) Kv)

private def kaehlerOfSeparatingTranscendentalBasis (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] : Basis ι F Ω[F⁄K] :=
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
  have : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F :=
    Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun x => rfl)
  exact finrank_kaehler_eq_card_of_separating hs

namespace IsCurveOver
open _root_.AlgebraicCurve.IsCurveOver

private theorem trdeg_le_one [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F ≤ 1 := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have := hsep
  have hcard : s.card = 1 := by
    rw [← finrank_kaehler_eq_card_of_separating' hs.1, IsCurveOver.finrank_kaehler]
  have htr := hs.cardinalMk_eq_trdeg
  rw [Cardinal.mk_coe_finset, hcard, Nat.cast_one] at htr
  exact htr.symm.le

private theorem trdeg_eq_one_of_perfectField [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] : Algebra.trdeg K F = 1 :=
  IsCurveOver.trdeg_eq_one trdeg_le_one

end IsCurveOver
open scoped _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve.IsCurveOver
    _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve

end AlgebraicCurve
open scoped _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve.IsCurveOver
    _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve

open _root_.IntermediateField
open _root_.Algebra
open _root_.TensorProduct.Algebra
open _root_.Algebra.TensorProduct.Algebra

namespace AlgebraicCurve
open _root_.AlgebraicCurve

universe u₁ u₂

variable {K : Type u₁} {F : Type u₂} [Field K] [Field F] [Algebra K F]

namespace IsCurveOver
open _root_.AlgebraicCurve.IsCurveOver

private theorem exists_separating_transcendental_s6 [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have hcard : s.card = 1 := by
    have htr := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, IsCurveOver.trdeg_eq_one_of_perfectField] at htr
    exact_mod_cast htr
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
  have htr : Transcendental K t := by
    have h1 := hs.1
    rw [show ((↑) : (↑({t} : Finset F)) → F) = fun _ => t from
      funext fun x => (Finset.mem_singleton.mp x.2).symm ▸ rfl] at h1
    exact (algebraicIndependent_unique_type_iff (ι := (↑({t} : Finset F)))).mp h1
  have heq : IntermediateField.adjoin K (↑({t} : Finset F) : Set F) = K⟮t⟯ := by
    rw [Finset.coe_singleton]
  have hsep' : Algebra.IsSeparable K⟮t⟯ F :=
    Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.equivOfEq heq).toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun _ => rfl)
  have : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  exact ⟨t, htr, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep'⟩

end IsCurveOver
open scoped _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve.IsCurveOver
    _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve

end AlgebraicCurve
open scoped _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve.IsCurveOver
    _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve

open IntermediateField _root_.Algebra _root_.TensorProduct.Algebra
    _root_.Algebra.TensorProduct.Algebra in
/-- The function field `F` of a curve over a perfect field `K` contains a transcendental `t` such
that `F / K(t)` is finite and separable. -/
public theorem _root_.AlgebraicCurve.IsCurveOver.exists_separating_transcendental {K : Type*}
    {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F :=
  AlgebraicCurve.IsCurveOver.exists_separating_transcendental_s6

end
open scoped _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve.IsCurveOver
    _root_.CurveGenus.SeparatingTranscendental.AlgebraicCurve

end

end SeparatingTranscendental

end CurveGenus
