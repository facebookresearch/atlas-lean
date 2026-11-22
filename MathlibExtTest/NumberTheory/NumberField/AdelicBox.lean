/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.Matrix
public import MathlibExt.NumberTheory.NumberField.AdelicBox

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField MeasureTheory

/-- Test-site measurable space on the adele ring over `ℚ`, from the
reducible Borel measurable space used by the Haar measures. -/
instance : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ

/-- Test-site Borel space on the adele ring over `ℚ`. -/
instance : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ

/-- Test-site topological group structure on adelic `GL(2)` over `ℚ`,
from its description as units of the matrix ring. -/
instance : IsTopologicalGroup (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (IsTopologicalGroup
    (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))ˣ)

/-- Test-site local compactness of matrices over the adele ring. -/
instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → AdeleRing (𝓞 ℚ) ℚ))

/-- Test-site local compactness of adelic `GL(2)` over `ℚ`. -/
instance : LocallyCompactSpace (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (LocallyCompactSpace
    (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))ˣ)

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

/-- The centre of adelic `GL(2)` over `ℚ` is the range of the scalar map. -/
example : Subgroup.center (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) =
    (Matrix.GeneralLinearGroup.scalar (Fin 2) :
      (AdeleRing (𝓞 ℚ) ℚ)ˣ →* _).range :=
  NumberField.AdelicCentre.center_eq_range_scalar (𝓞 ℚ) ℚ

/-- The Haar measure on adelic `PGL(2)` over `ℚ` is a Haar measure. -/
example : @Measure.IsHaarMeasure (NumberField.AdelicCentre.AdelicPGL2 (𝓞 ℚ) ℚ) _ _
    (NumberField.AdelicCentre.pglBorel (𝓞 ℚ) ℚ)
    (NumberField.AdelicCentre.adelicPGLHaar (𝓞 ℚ) ℚ) :=
  NumberField.AdelicCentre.isHaarMeasure_adelicPGLHaar (𝓞 ℚ) ℚ

end
