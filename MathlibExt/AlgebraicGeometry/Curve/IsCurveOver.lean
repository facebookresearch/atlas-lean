/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_IsCurveOver.lean`
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

public import Mathlib.RingTheory.Kaehler.Basic
public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

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

/-!
# Function fields of curves

`IsCurveOver K F`, defined in `MathlibExt.AlgebraicGeometry.Curve.LPolynomial`, says that every
nonzero element of `F` has a degree-zero principal divisor, residue fields of places are finite
over `K`, and the Kähler differentials of `F / K` are free of rank one. This file derives the
instances `HasPrincipalDivisors K F`, `Module.Finite K v.ResidueField` and the Kähler instances from
it, and shows that every place has degree one over an algebraically closed field. From the rank-one
Kähler condition alone it shows that `F` is not separable over `K`. Over a perfect field it shows
that `F` is transcendental over `K` and, when `F` is also essentially of finite type over `K`, that
`F` has transcendence degree one.
-/

@[expose] public section

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver

variable {K F}

instance (priority := 100) toHasPrincipalDivisors [IsCurveOver K F] :
    HasPrincipalDivisors K F :=
  ⟨IsCurveOver.exists_divisor⟩

theorem hasPrincipalDivisors [IsCurveOver K F] : HasPrincipalDivisors K F :=
  inferInstance

instance instFiniteResidueField [IsCurveOver K F] (v : Place K F) :
    Module.Finite K v.ResidueField :=
  IsCurveOver.finiteResidue v

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
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  change Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

end Place

namespace IsCurveOver

variable {K F}

theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.deg = 1 :=
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  v.deg_eq_one_of_isAlgClosed_of_finite

theorem forall_deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] :
    ∀ w : Place K F, w.deg = 1 :=
  deg_eq_one_of_isAlgClosed

/-- **A curve function field is not separable over its base.** If `F` is the function field of a
curve over `K`, then `F` is not a separable algebraic extension of `K`. Only the rank-one Kähler
condition is used, with no hypothesis on `K`: a separable algebraic extension is formally
unramified, so its module of Kähler differentials is zero, while `Ω[F⁄K]` has rank one. -/
theorem not_isSeparable [IsCurveOver K F] : ¬ Algebra.IsSeparable K F := by
  intro hsep
  have : Algebra.FormallyUnramified K F :=
    Algebra.FormallyUnramified.of_isSeparable K F
  exact false_of_nontrivial_of_subsingleton Ω[F⁄K]

/-- **A curve function field over a perfect field is not algebraic.** If `K` is a perfect field
and `F` is the function field of a curve over `K`, then `F` is not algebraic over `K`. The
perfect-field hypothesis makes every algebraic extension of `K` separable, which
`not_isSeparable` rules out. -/
theorem not_isAlgebraic [PerfectField K] [IsCurveOver K F] :
    ¬ Algebra.IsAlgebraic K F := by
  intro halg
  exact not_isSeparable (K := K) (F := F)
    Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- **A curve function field over a perfect field is transcendental.** If `K` is a perfect field
and `F` is the function field of a curve over `K`, then `F` is transcendental over `K`: some
element of `F` is transcendental over `K`. -/
instance instTranscendental [PerfectField K] [IsCurveOver K F] :
    Algebra.Transcendental K F :=
  Algebra.transcendental_iff_not_isAlgebraic.mpr not_isAlgebraic

end IsCurveOver

open IntermediateField Algebra
open scoped IntermediateField.algebraAdjoinAdjoin

section KaehlerBasis

variable {K F}
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
      change algebraMap K Kv a
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
  have : Algebra.IsSeparable
      (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F :=
    Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun x => rfl)
  exact finrank_kaehler_eq_card_of_separating hs

end KaehlerBasis

namespace IsCurveOver

variable {K F}

/-- **A curve function field has transcendence degree at most one.** If `K` is a perfect field,
`F` is essentially of finite type over `K`, and `F` is the function field of a curve over `K`, then
the transcendence degree of `F` over `K` is at most one. The first two hypotheses give `F` a
separating transcendence basis over `K`, which indexes a basis of `Ω[F⁄K]`, a module of rank
one. -/
theorem trdeg_le_one [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] : Algebra.trdeg K F ≤ 1 := by
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have := hsep
  have hcard : s.card = 1 := by
    rw [← finrank_kaehler_eq_card_of_separating' hs.1,
      IsCurveOver.finrank_kaehler]
  have htr := hs.cardinalMk_eq_trdeg
  rw [Cardinal.mk_coe_finset, hcard, Nat.cast_one] at htr
  exact htr.symm.le

/-- **A curve function field has transcendence degree one.** If `K` is a perfect field, `F` is
essentially of finite type over `K`, and `F` is the function field of a curve over `K`, then `F`
has transcendence degree one over `K`. The upper bound is `trdeg_le_one`, and the lower bound
holds because `F` is transcendental over `K`. -/
theorem trdeg_eq_one_of_perfectField [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F = 1 :=
  le_antisymm trdeg_le_one (Cardinal.one_le_iff_pos.mpr (trdeg_pos K F))

end IsCurveOver

end AlgebraicCurve
