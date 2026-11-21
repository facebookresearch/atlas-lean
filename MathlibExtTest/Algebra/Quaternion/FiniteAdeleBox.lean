/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.ClassSetHecke

@[expose] public section

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D)

theorem exactSource_finiteAdeleBox (z : D) :
    z ∈ Submodule.ofFiniteIdele Λ
        (1 : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (Submodule.finiteAdeleBox Λ).map
          (AddMonoidHom.mulLeft (1 : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Submodule.mem_ofFiniteIdele_iff Λ 1 z

example : (0 : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ :=
  zero_mem _

example (d : Dˣ) :
    ((Submodule.finiteIdeleDiagonal D d :
      (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (d : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Submodule.val_finiteIdeleDiagonal_apply d

example (u : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      u • ((Submodule.finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) =
        ((Submodule.finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Submodule.mem_finiteIdeleStabilizer_iff Λ u

end
