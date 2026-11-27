/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_SigmaAdelicAction.lean`,
`Theorems/Thm_AutomorphicForm_adelicHeight_sigmaAdelicAct.lean`
and
`P2M/Sol/S_AutomorphicForm_adelicHeight_sigmaAdelicAct.lean`
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

public import MathlibExt.NumberTheory.AutomorphicForm.FnTwist
public import MathlibExt.NumberTheory.NumberField.AdelicHeight
public import MathlibExt.NumberTheory.NumberField.IdeleGaloisDescent
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import MathlibExt.NumberTheory.NumberField.AdeleRingAut

/-!
# Galois twists of adelic `GL₂` and the adelic height

Given a Galois descent datum `D` on the adele ring of a number field `E` over `F`, an
automorphism `σ : E ≃ₐ[F] E` acts on `GL₂(𝔸_E)` entrywise through `D.act σ`
(`AutomorphicForm.sigmaAdelicAct`). This action preserves the adelic height
(`AutomorphicForm.adelicHeight_sigmaAdelicAct`): `D.act σ` permutes the places of `E` and
preserves the normalized norms of the place components.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicHeight

namespace AutomorphicForm

section Action

variable (F E : Type*) [Field F] [Field E] [NumberField E] [Algebra F E]
  (D : IdeleGaloisDescent (𝓞 E) F E)

/-- The entrywise action of `σ` on `GL₂(𝔸_E)` through the descent datum `D`. -/
def sigmaAdelicAct (σ : E ≃ₐ[F] E) : AdelicGL2 (𝓞 E) E →* AdelicGL2 (𝓞 E) E :=
  Matrix.GeneralLinearGroup.map (D.act σ : RingAut (AdeleRing (𝓞 E) E)).toRingHom

theorem sigmaAdelicAct_apply (σ : E ≃ₐ[F] E) (g : AdelicGL2 (𝓞 E) E) (i j : Fin 2) :
    (sigmaAdelicAct F E D σ g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 E) E)) i j =
      D.act σ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 E) E)) i j) :=
  rfl

theorem sigmaAdelicAct_one : sigmaAdelicAct F E D 1 = MonoidHom.id _ := by
  ext g i j
  rw [sigmaAdelicAct_apply, map_one]
  rfl

theorem sigmaAdelicAct_mul (σ τ : E ≃ₐ[F] E) :
    sigmaAdelicAct F E D (σ * τ) = (sigmaAdelicAct F E D σ).comp (sigmaAdelicAct F E D τ) := by
  ext g i j
  rw [MonoidHom.comp_apply, sigmaAdelicAct_apply, sigmaAdelicAct_apply, sigmaAdelicAct_apply,
    map_mul]
  rfl

end Action

/-- The adelic height on `GL₂(𝔸_L)` is invariant under the action of `L ≃ₐ[K] L` through
a Galois descent datum on the adele ring. -/
theorem adelicHeight_sigmaAdelicAct (K L : Type*) [Field K] [Field L] [NumberField L]
    [Algebra K L] (D : IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) :
    adelicHeight L (sigmaAdelicAct K L D σ g) = adelicHeight L g := by
  let φ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L := D.act σ
  have hφ : Continuous φ := D.continuous_act σ
  have hφ' : Continuous φ.symm := D.continuous_act_symm σ
  have hτ : ∀ x : L, φ (algebraMap L (AdeleRing (𝓞 L) L) x) =
      algebraMap L (AdeleRing (𝓞 L) L) ((σ : L ≃+* L) x) := D.compat σ
  refine adelicHeight_map_of_norm_eq φ.toRingHom (MulAction.toPerm σ)
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv (σ : L ≃+* L)))
    (fun v => ?_) (fun v a => ?_) (fun w a => ?_) g
  · change (σ • v).mult = v.mult
    unfold InfinitePlace.mult
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd (InfinitePlace.isReal_smul_iff.mp h₁) h₂
    · exact absurd (InfinitePlace.isReal_smul_iff.mpr h₂) h₁
    · rfl
  · exact AdeleRing.norm_fst_map_comap φ hφ hφ' (σ : L ≃+* L) hτ v a
  · exact AdeleRing.norm_snd_map_equivOfRingEquiv φ hφ hφ' (σ : L ≃+* L) hτ w a

end AutomorphicForm
