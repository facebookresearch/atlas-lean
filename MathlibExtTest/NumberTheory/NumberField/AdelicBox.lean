/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdelicBox

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField MeasureTheory

namespace AdelicBoxTest

/-- Test-site measurable space on the adele ring over `ℚ`, from the
reducible Borel measurable space used by the Haar measures. -/
instance : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ

/-- Test-site Borel space on the adele ring over `ℚ`. -/
instance : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ

/-- Unfolding: membership in the integral finite adeles is integrality at
every finite place. -/
example (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    x ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ ↔
      ∀ v : HeightOneSpectrum (𝓞 ℚ), x v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

/-- The zero finite adele is integral. -/
example : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
    NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :=
  fun _ => zero_mem _

/-- Characterization: every adele over `ℚ` can be shifted by a unique
principal adele into the adelic box. This instantiates all hypotheses
(`Field ℚ` and `NumberField ℚ`) at the zero adele. -/
example : ∃! k : ℚ, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k + (0 : AdeleRing (𝓞 ℚ) ℚ) ∈
    NumberField.AdelicBox.adelicBox ℚ :=
  NumberField.AdelicBox.existsUnique_algebraMap_add_mem_adelicBox ℚ 0

/-- The adelic box over `ℚ` is a fundamental domain for the principal
adeles, for the additive Haar measure. -/
example : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
    (NumberField.AdelicBox.adelicBox ℚ) (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
  NumberField.AdelicBox.isAddFundamentalDomain_adelicBox_adelicAddHaar ℚ

/-- The additive Haar measure of the adelic box over `ℚ` is positive and
finite. -/
example : 0 < NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
      (NumberField.AdelicBox.adelicBox ℚ) ∧
    NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
      (NumberField.AdelicBox.adelicBox ℚ) < ⊤ :=
  ⟨NumberField.AdelicBox.adelicAddHaar_adelicBox_pos ℚ,
    NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ⟩

/-- The centre of adelic `GL(2)` over `ℚ` is isomorphic to the units of the
adele ring: Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar`
identifies it with the range of the scalar map, which is injective. -/
example : Nonempty ((AdeleRing (𝓞 ℚ) ℚ)ˣ ≃*
    Subgroup.center (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) :=
  ⟨(MonoidHom.ofInjective (NumberField.AdelicCentre.scalar_injective (𝓞 ℚ) ℚ)).trans
    (MulEquiv.subgroupCongr Matrix.GeneralLinearGroup.center_eq_range_scalar.symm)⟩

/-- A scalar matrix over the adeles of `ℚ` maps to the identity of adelic
`PGL(2)`. -/
example (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a) :
      NumberField.AdelicCentre.AdelicPGL2 (𝓞 ℚ) ℚ) = 1 := by
  rw [QuotientGroup.eq_one_iff, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact MonoidHom.mem_range.mpr ⟨a, rfl⟩

/-- Instance search shows that adelic `PGL(2)` over `ℚ` is a Hausdorff, locally
compact topological group, from Mathlib's quotient-group instances, the
library's instances on adelic `GL(2)` and
`NumberField.AdelicCentre.isClosed_center`. -/
example : IsTopologicalGroup (NumberField.AdelicCentre.AdelicPGL2 (𝓞 ℚ) ℚ) ∧
    T2Space (NumberField.AdelicCentre.AdelicPGL2 (𝓞 ℚ) ℚ) ∧
    LocallyCompactSpace (NumberField.AdelicCentre.AdelicPGL2 (𝓞 ℚ) ℚ) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The Haar measure on adelic `PGL(2)` over `ℚ` is a Haar measure. -/
example : @Measure.IsHaarMeasure (NumberField.AdelicCentre.AdelicPGL2 (𝓞 ℚ) ℚ) _ _
    (NumberField.AdelicCentre.pglBorel (𝓞 ℚ) ℚ)
    (NumberField.AdelicCentre.adelicPGLHaar (𝓞 ℚ) ℚ) :=
  NumberField.AdelicCentre.isHaarMeasure_adelicPGLHaar (𝓞 ℚ) ℚ

/-- The image of all of adelic `GL(2)` over `ℚ`, that is adelic `PGL(2)`, has
positive Haar measure. -/
example : 0 < NumberField.AdelicCentre.adelicPGLHaar (𝓞 ℚ) ℚ
    ((QuotientGroup.mk : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →
      NumberField.AdelicCentre.AdelicPGL2 (𝓞 ℚ) ℚ) '' Set.univ) :=
  NumberField.AdelicCentre.adelicPGLHaar_image_pos (𝓞 ℚ) ℚ
    ⟨Set.univ, isOpen_univ, Set.univ_nonempty, Set.Subset.rfl⟩

/-- Boundary case: the centre of adelic `GL(2)` over `ℚ` lies in `{1}` times
the centre, so its image, the identity of adelic `PGL(2)`, has finite Haar
measure. -/
example : NumberField.AdelicCentre.adelicPGLHaar (𝓞 ℚ) ℚ
    ((QuotientGroup.mk : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →
      NumberField.AdelicCentre.AdelicPGL2 (𝓞 ℚ) ℚ) ''
        (Subgroup.center (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
          Set (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))) < ⊤ :=
  NumberField.AdelicCentre.adelicPGLHaar_image_lt_top_of_subset (𝓞 ℚ) ℚ (C := {1})
    isCompact_singleton fun z hz => Set.mem_mul.mpr ⟨1, Set.mem_singleton 1, z, hz, one_mul z⟩

end AdelicBoxTest

end
