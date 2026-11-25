/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CuspForm_AdelicLift.lean`,
`Definitions/Def_NumberField_AdelicLevel.lean`,
`Definitions/Def_AdelicDock_LocalEmbedding.lean`,
`Definitions/Def_LanglandsTunnell_DeltaLift.lean`
and
`P2M/Sol/S_CuspForm_exists_isAdelicLiftOf.lean`
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

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import MathlibExt.NumberTheory.NumberField.AdelicGL2LocalFiniteness
public import MathlibExt.NumberTheory.NumberField.HeckeCharacter
public import MathlibExt.NumberTheory.NumberField.AdelicLevel
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace NumberField.AdelicLevel

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The component of an archimedean `GL(2)` element at one infinite place. -/
def archComponent (w : InfinitePlace K) :
    GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.map (archEval K w)

theorem idealBound_of_ne_bot {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N v =
      WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ)) :=
  ite_eq_right hN

theorem idealBound_le_one (N : Ideal R) (v : HeightOneSpectrum R) :
    idealBound R N v ≤ 1 := by
  by_cases hN : N = ⊥
  · rw [hN]; simp [idealBound]
  · rw [idealBound_of_ne_bot R hN, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp

/-- The integral finite adeles: those integral at every finite place. -/
def integralFiniteAdeles : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, x v ∈ v.adicCompletionIntegers K}

/-- Matrices over the finite adeles with trivial archimedean part. -/
def finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j)

theorem mapMatrix_arch_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (adeleArch R K).mapMatrix (finMat R K g) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [finMat, RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch]
  · simp [finMat, RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch,
      Matrix.one_apply_ne h]

theorem mapMatrix_fin_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (adeleFin R K).mapMatrix (finMat R K g) = g := by
  ext i j
  rfl

theorem matrix_eq_of_mapMatrix_arch_fin_eq
    {M N : Matrix (Fin 2) (Fin 2) (AdeleRing R K)}
    (h₁ : (adeleArch R K).mapMatrix M = (adeleArch R K).mapMatrix N)
    (h₂ : (adeleFin R K).mapMatrix M = (adeleFin R K).mapMatrix N) : M = N := by
  ext i j
  apply Prod.ext
  · have h := congrFun (congrFun h₁ i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h
    exact h
  · have h := congrFun (congrFun h₂ i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h
    exact h

theorem finMat_one : finMat R K 1 = 1 :=
  matrix_eq_of_mapMatrix_arch_fin_eq (R := R) (K := K)
    (M := finMat R K 1) (N := 1)
    (by rw [mapMatrix_arch_finMat, map_one])
    (by rw [mapMatrix_fin_finMat, map_one])

theorem finMat_mul (g h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    finMat R K (g * h) = finMat R K g * finMat R K h :=
  matrix_eq_of_mapMatrix_arch_fin_eq (R := R) (K := K)
    (M := finMat R K (g * h)) (N := finMat R K g * finMat R K h)
    (by rw [map_mul, mapMatrix_arch_finMat, mapMatrix_arch_finMat,
      mapMatrix_arch_finMat, mul_one])
    (by rw [map_mul, mapMatrix_fin_finMat, mapMatrix_fin_finMat,
      mapMatrix_fin_finMat])

/-- Embedding finite adelic `GL(2)` into adelic `GL(2)`. -/
def finEmbed : GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (AdeleRing R K) where
  toFun g := ⟨finMat R K g,
    finMat R K ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _),
    by rw [← finMat_mul, Units.mul_inv, finMat_one],
    by rw [← finMat_mul, Units.inv_mul, finMat_one]⟩
  map_one' := Units.ext (by simp only [Units.val_one]; exact finMat_one R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact finMat_mul R K _ _)

@[simp] theorem coe_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ((finEmbed R K g : GL (Fin 2) (AdeleRing R K)) : Matrix _ _ _) = finMat R K g := rfl

theorem glFin_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    glFin R K (finEmbed R K g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, coe_finEmbed]; rfl

theorem glArch_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    glArch R K (finEmbed R K g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, coe_finEmbed, Units.val_one]; rfl

theorem finEmbed_injective : Function.Injective (finEmbed R K) :=
  fun g h hgh => by rw [← glFin_finEmbed R K g, ← glFin_finEmbed R K h, hgh]

end NumberField.AdelicLevel

namespace AdelicDock

/-- The principal ideal generated by `N` in the integers of `ℚ`. -/
def ratLevel (N : ℕ) : Ideal (𝓞 ℚ) := Ideal.span {(N : 𝓞 ℚ)}

theorem ratLevel_ne_bot {N : ℕ} (hN : N ≠ 0) : ratLevel N ≠ ⊥ := by
  rw [ratLevel, Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hN

theorem ratLevel_one : ratLevel 1 = ⊤ := by
  rw [ratLevel, Nat.cast_one, Ideal.span_singleton_one]

end AdelicDock

namespace LanglandsTunnell

/-- The real archimedean component of a rational adelic `GL(2)` element. -/
theorem rat_infinitePlace_isReal :
    InfinitePlace.IsReal (default : InfinitePlace ℚ) :=
  InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr (by
    ext x
    rw [eq_ratCast]
    simp))

def ratArchGL2 (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal
      rat_infinitePlace_isReal).toRingHom
    (NumberField.AdelicLevel.archComponent ℚ default
      (NumberField.AdelicLevel.glArch (𝓞 ℚ) ℚ g))

end LanglandsTunnell

namespace CuspForm

variable {M : ℕ}

open scoped ModularForm in
/-- A function on adelic `GL(2)` is an adelic lift of a weight-two cusp
form when it is left rational-invariant, right invariant under the finite
level-one subgroup at level `M`, and recovers the cusp form at the
archimedean place on elements with trivial finite part. -/
def IsAdelicLiftOf (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  (∀ (γ : GL (Fin 2) ℚ) (x : NumberField.AdelicGL2 (𝓞 ℚ) ℚ),
      φ (NumberField.globalPoints (𝓞 ℚ) ℚ γ * x) = φ x) ∧
    (∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M),
      ∀ x, φ (x * NumberField.AdelicLevel.finEmbed (𝓞 ℚ) ℚ u) = φ x) ∧
    ∀ h : NumberField.AdelicGL2 (𝓞 ℚ) ℚ,
      NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
          φ h = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I

theorem IsAdelicLiftOf.left_inv {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφg : IsAdelicLiftOf g φ)
    (γ : GL (Fin 2) ℚ) (x : NumberField.AdelicGL2 (𝓞 ℚ) ℚ) :
    φ (NumberField.globalPoints (𝓞 ℚ) ℚ γ * x) = φ x :=
  hφg.1 γ x

theorem IsAdelicLiftOf.level_inv {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφg : IsAdelicLiftOf g φ) :
    ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M),
      ∀ x, φ (x * NumberField.AdelicLevel.finEmbed (𝓞 ℚ) ℚ u) = φ x :=
  hφg.2.1

open scoped ModularForm in
theorem IsAdelicLiftOf.apply_eq {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφg : IsAdelicLiftOf g φ)
    (h : NumberField.AdelicGL2 (𝓞 ℚ) ℚ)
    (hfin : NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    φ h = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I :=
  hφg.2.2 h hfin hpos

end CuspForm

end
