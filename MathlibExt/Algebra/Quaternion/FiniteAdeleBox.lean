/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Submodule_FiniteAdeleBox.lean`
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
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

@[expose] public section

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace Submodule

variable {D : Type*} [Ring D] [Algebra ℚ D]

def finiteAdeleBox (Λ : Submodule ℤ D) : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  AddSubgroup.closure
    {x | ∃ z ∈ Λ, ∃ a : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] a}

def ofFiniteIdele (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Submodule ℤ D :=
  (AddSubgroup.toIntSubmodule
      ((finiteAdeleBox Λ).map
        (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)))).comap
    ((Algebra.TensorProduct.includeLeft :
        D →ₐ[ℚ] D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toLinearMap.restrictScalars ℤ)

def finiteIdeleStabilizer (Λ : Submodule ℤ D) : Subgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  MulAction.stabilizer (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ
    ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))

def conjByFiniteIdele (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule ℤ D :=
  (AddSubgroup.toIntSubmodule
      ((finiteAdeleBox Λ).map
        ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
          (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))))).comap
    ((Algebra.TensorProduct.includeLeft :
        D →ₐ[ℚ] D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toLinearMap.restrictScalars ℤ)

variable (D) in

def finiteIdeleDiagonal : Dˣ →* (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom :
    D →+* D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toMonoidHom

@[simp] theorem val_finiteIdeleDiagonal_apply (d : Dˣ) :
    ((finiteIdeleDiagonal D d : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (d : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

theorem mem_ofFiniteIdele_iff (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (z : D) :
    z ∈ ofFiniteIdele Λ g ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Iff.rfl

theorem mem_conjByFiniteIdele_iff (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (z : D) :
    z ∈ conjByFiniteIdele Λ g ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (finiteAdeleBox Λ).map
          ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
              D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
            (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
  Iff.rfl

theorem mem_finiteIdeleStabilizer_iff (Λ : Submodule ℤ D) (u : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ finiteIdeleStabilizer Λ ↔
      u • ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))
        = ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Iff.rfl

end Submodule

end
