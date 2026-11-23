/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AdicCompletionRestrictScalars.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers
of the Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra

@[expose] public section

universe u₁ u₂

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B]
  (𝔭 : Ideal A)

/-- Restricting scalars along `A → B` identifies the submodule cut out by the
`n`-th power of the extended ideal `𝔭 B` with the submodule cut out by the
`n`-th power of `𝔭` acting on `B` as an `A`-module. -/
theorem restrictScalars_map_pow_smul_top (n : ℕ) :
    (((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B).restrictScalars A) =
      (𝔭 ^ n • ⊤ : Submodule A B) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
    Submodule.restrictScalars_top]

/-- The levelwise identification of quotients underlying `restrictScalarsEquiv`:
at each level `n`, the quotient of `B` by the extended ideal power, viewed as
an `A`-module, is the quotient of `B` as an `A`-module by the `𝔭`-power
submodule. -/
noncomputable def levelRestrictScalarsEquiv (n : ℕ) :
    (B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) ≃ₗ[A]
      B ⧸ (𝔭 ^ n • ⊤ : Submodule A B) :=
  (Submodule.Quotient.restrictScalarsEquiv A _).symm.trans
    (Submodule.quotEquivOfEq _ _ (restrictScalars_map_pow_smul_top B 𝔭 n))

/-- The levelwise identification sends the class of `b` to the class of `b`. -/
theorem levelRestrictScalarsEquiv_mk (n : ℕ) (b : B) :
    levelRestrictScalarsEquiv B 𝔭 n (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk b :=
  rfl

/-- The levelwise identifications are compatible with the transition maps
of the two inverse systems defining the completions. -/
theorem transitionMap_levelRestrictScalarsEquiv {m n : ℕ} (hmn : m ≤ n)
    (y : B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) :
    transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n y) =
      levelRestrictScalarsEquiv B 𝔭 m
        (transitionMap (𝔭.map (algebraMap A B)) B hmn y) :=
  Quotient.inductionOn' y fun _ => rfl

/-- Restriction of scalars identifies the completion of the `B`-algebra `B`
at the extended ideal `𝔭 B` with the `𝔭`-adic completion of `B` viewed as
an `A`-module. No Noetherian, completeness, or finite-generation hypothesis
is needed: the two inverse systems have the same levels after restricting
scalars. -/
noncomputable def restrictScalarsEquiv :
    AdicCompletion (𝔭.map (algebraMap A B)) B ≃ₗ[A] AdicCompletion 𝔭 B where
  toFun x := ⟨fun n => levelRestrictScalarsEquiv B 𝔭 n (x.val n),
    fun {m n} hmn => by
      change transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n (x.val n)) =
        levelRestrictScalarsEquiv B 𝔭 m (x.val m)
      rw [← x.prop hmn]
      exact transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn (x.val n)⟩
  invFun y := ⟨fun n => (levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n),
    fun {m n} hmn => by
      change transitionMap (𝔭.map (algebraMap A B)) B hmn
          ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)) =
        (levelRestrictScalarsEquiv B 𝔭 m).symm (y.val m)
      rw [← y.prop hmn, LinearEquiv.eq_symm_apply,
        ← transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn
          ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)),
        LinearEquiv.apply_symm_apply]⟩
  map_add' x y := by
    ext n
    exact map_add (levelRestrictScalarsEquiv B 𝔭 n) _ _
  map_smul' a x := by
    ext n
    exact map_smul (levelRestrictScalarsEquiv B 𝔭 n) a _
  left_inv x := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).symm_apply_apply _
  right_inv y := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).apply_symm_apply _

/-- The identification is compatible with the canonical maps from `B`:
the image of `b` in the extended-ideal completion maps to the image of `b`
in the `𝔭`-adic completion. -/
theorem restrictScalarsEquiv_of (b : B) :
    restrictScalarsEquiv B 𝔭 (of (𝔭.map (algebraMap A B)) B b) = of 𝔭 B b := by
  ext n
  rfl

/-- The inverse identification is likewise compatible with the canonical
maps from `B`. -/
theorem restrictScalarsEquiv_symm_of (b : B) :
    (restrictScalarsEquiv B 𝔭).symm (of 𝔭 B b) =
      of (𝔭.map (algebraMap A B)) B b := by
  ext n
  rfl

end AdicCompletion
