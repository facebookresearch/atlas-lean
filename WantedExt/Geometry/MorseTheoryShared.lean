/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared Morse-theory API

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This neutral helper module is shared by the Morse inequalities and weak Morse inequality wanted entries. The definitions are the trusted (non-hole) helpers from leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e, distributed under the Apache License, Version 2.0; unchanged apart from the namespace.
-/
module

public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.MorseTheoryShared

open scoped ContDiff

def IsCriticalPoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : Prop :=
  mfderiv I (modelWithCornersSelf ℝ ℝ) f x = 0

noncomputable def localHessian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  iteratedFDeriv ℝ 2 (f ∘ (extChartAt I x).symm) (extChartAt I x x)

def IsNondegenerateCritical
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : Prop :=
  IsCriticalPoint I f x ∧
    ∀ v : E, (∀ w : E, localHessian I f x ![v, w] = 0) → v = 0

structure IsMorseFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] (f : M → ℝ) : Prop where
  smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ f
  critical_finite : {x : M | IsCriticalPoint I f x}.Finite
  nondegenerate : ∀ x : M, IsCriticalPoint I f x → IsNondegenerateCritical I f x

noncomputable def morseIndex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : ℕ :=
  sSup {k : ℕ | ∃ S : Submodule ℝ E,
    Module.finrank ℝ S = k ∧
      ∀ v ∈ S, v ≠ 0 → localHessian I f x ![v, v] < 0}

noncomputable def morseCount
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (k : ℕ) : ℕ :=
  {x : M | IsCriticalPoint I f x ∧ morseIndex I f x = k}.ncard

noncomputable def bettiNumber (M : Type) [TopologicalSpace M] (k : ℕ) : ℕ :=
  Module.finrank ℝ
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℝ) k).obj
        (ModuleCat.of ℝ ℝ)).obj (TopCat.of M))

end MathlibExt.Geometry.MorseTheoryShared
