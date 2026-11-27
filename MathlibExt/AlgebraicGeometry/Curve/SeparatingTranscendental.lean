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

end AlgebraicCurve

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

end SeparatingTranscendental

end CurveGenus
