/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_NumberField_AdelicHaar.lean`
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

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import MathlibExt.NumberTheory.NumberField.AdeleLocallyCompact
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.Topology.Algebra.Group.Matrix

@[expose] public section

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct

noncomputable section

namespace NumberField.AdelicHaar


section Adele

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

instance t2Space_infiniteAdeleRing : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))

instance t2Space_adeleRing : T2Space (AdeleRing R K) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing R K))

@[reducible] def adeleBorel : MeasurableSpace (AdeleRing R K) := borel _

theorem borelSpace_adeleBorel : @BorelSpace (AdeleRing R K) _ (adeleBorel R K) :=
  @BorelSpace.mk _ _ (adeleBorel R K) rfl

variable [Module.Free ℤ R] [Module.Finite ℤ R]

def adelicAddHaar [NumberField K] [LocallyCompactSpace (AdeleRing R K)] :
    @Measure (AdeleRing R K) (adeleBorel R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  exact Measure.addHaar

theorem isAddHaarMeasure_adelicAddHaar [NumberField K]
    [LocallyCompactSpace (AdeleRing R K)] :
    @Measure.IsAddHaarMeasure (AdeleRing R K) _ _ (adeleBorel R K) (adelicAddHaar R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  exact Measure.isAddHaarMeasure_addHaarMeasure _

end Adele

section GeneralLinear

variable (n : Type*) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

instance t2Space_gl_adeleRing [Fintype n] [DecidableEq n] :
    T2Space (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  inferInstance

@[reducible] def glBorel [Fintype n] [DecidableEq n] :
    MeasurableSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) := borel _

theorem borelSpace_glBorel [Fintype n] [DecidableEq n] :
    @BorelSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) _ (glBorel n R K) :=
  @BorelSpace.mk _ _ (glBorel n R K) rfl

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K] [Fintype n] [DecidableEq n]

instance locallyCompactSpace_matrix_adeleRing [LocallyCompactSpace (AdeleRing R K)] :
    LocallyCompactSpace (Matrix n n (AdeleRing R K)) :=
  inferInstanceAs (LocallyCompactSpace (n → n → AdeleRing R K))

instance isTopologicalGroup_gl_adeleRing :
    IsTopologicalGroup (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  inferInstanceAs (IsTopologicalGroup ((Matrix n n (AdeleRing R K))ˣ))

instance locallyCompactSpace_gl_adeleRing [LocallyCompactSpace (AdeleRing R K)] :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  inferInstanceAs (LocallyCompactSpace ((Matrix n n (AdeleRing R K))ˣ))

def adelicGLHaar
    [LocallyCompactSpace (Matrix.GeneralLinearGroup n (AdeleRing R K))] :
    @Measure (Matrix.GeneralLinearGroup n (AdeleRing R K)) (glBorel n R K) := by
  letI := glBorel n R K
  haveI := borelSpace_glBorel n R K
  exact Measure.haar

theorem isHaarMeasure_adelicGLHaar
    [LocallyCompactSpace (Matrix.GeneralLinearGroup n (AdeleRing R K))] :
    @Measure.IsHaarMeasure (Matrix.GeneralLinearGroup n (AdeleRing R K)) _ _
      (glBorel n R K) (adelicGLHaar n R K) := by
  letI := glBorel n R K
  haveI := borelSpace_glBorel n R K
  exact Measure.isHaarMeasure_haarMeasure _

end GeneralLinear

end NumberField.AdelicHaar

end
