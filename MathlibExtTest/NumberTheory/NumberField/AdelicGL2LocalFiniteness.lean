/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdelicGL2LocalFiniteness

@[expose] public section

open NumberField

universe u

/-- Consumer with the original binders: the field is taken in `Type`, as in
the source statement, and the conclusion is the local-finiteness property. -/
private theorem exactSource (F : Type) [Field F] [NumberField F] :
    AdelicKernelLocalFiniteness F :=
  NumberField.adelicKernelLocalFiniteness F

/-- The same statement at an arbitrary universe level. -/
public theorem exactSource_universe (F : Type u) [Field F] [NumberField F] :
    AdelicKernelLocalFiniteness F :=
  NumberField.adelicKernelLocalFiniteness F

/-- The expanded form, with the original compact-set binders. -/
example (F : Type*) [Field F] [NumberField F] (C : Set (AdelicGL2 (𝓞 F) F))
    (hC : IsCompact C) (x y : AdelicGL2 (𝓞 F) F) :
    {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      x⁻¹ * globalPoints (𝓞 F) F γ * y ∈ C}.Finite :=
  NumberField.adelicKernelLocalFiniteness F C hC x y

/-- Boundary case: the empty compact set contains no rational point. -/
example (F : Type*) [Field F] [NumberField F] (x y : AdelicGL2 (𝓞 F) F) :
    {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      x⁻¹ * globalPoints (𝓞 F) F γ * y ∈ (∅ : Set (AdelicGL2 (𝓞 F) F))}.Finite := by
  simp

/-- The identity rational point is counted exactly when `x⁻¹ * y` lies in
the compact set, so the membership hypothesis cannot be dropped. -/
example (F : Type*) [Field F] [NumberField F] (C : Set (AdelicGL2 (𝓞 F) F))
    (x y : AdelicGL2 (𝓞 F) F) (h : x⁻¹ * y ∈ C) :
    (1 : Matrix.GeneralLinearGroup (Fin 2) F) ∈
      {γ : Matrix.GeneralLinearGroup (Fin 2) F |
        x⁻¹ * globalPoints (𝓞 F) F γ * y ∈ C} := by
  simpa using h
