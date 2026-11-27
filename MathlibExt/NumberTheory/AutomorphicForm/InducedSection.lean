/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_AdelicLsXi.lean`,
`Definitions/Def_AutomorphicForm_BorelSubgroup.lean`,
`Definitions/Def_AutomorphicForm_InducedSection.lean`,
`Definitions/Def_AutomorphicForm_EtaFamily.lean`
and
`Definitions/Def_AutomorphicForm_WeylIntertwining.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.ConstantTerm
public import MathlibExt.NumberTheory.NumberField.AdelicGL2LocalFiniteness
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Borel subgroup, induced sections and the Weyl intertwining integral

For a commutative ring `A`, `borelSubgroup A` is the upper-triangular subgroup of `GL(2, A)`,
with diagonal characters `borelDiagFst` and `borelDiagSnd`. Over the adeles of a global field,
`IsInducedSection R K χ₁ χ₂ φ` says that `φ` transforms on the left under the Borel subgroup
by `χ₁ ⊠ χ₂`. We also define the unramified twists `etaFst` and `etaSnd` of a pair of idele
characters, the Weyl element and the Weyl intertwining integral.
-/

@[expose] public section

open NumberField MeasureTheory

noncomputable section

namespace AutomorphicForm

section Borel

variable (A : Type*) [CommRing A]

/-- **Borel subgroup of `GL(2)`.** The upper-triangular (Borel) subgroup of `GL(2, A)`. -/
def borelSubgroup : Subgroup (GL (Fin 2) A) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0}
  mul_mem' := by
    intro x y hx hy
    have hx' : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
    have hy' : (y : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hy
    change ((x * y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx', hy']
    ring
  one_mem' := by
    change ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_one]
    exact Matrix.one_apply_ne (by decide)
  inv_mem' := by
    intro x hx
    have hx' : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
    change ((x⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
    simp [Matrix.adjugate_fin_two, hx']

@[simp] theorem mem_borelSubgroup_iff {x : GL (Fin 2) A} :
    x ∈ borelSubgroup A ↔ (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := Iff.rfl

variable {A}

/-- **Diagonal entries of a Borel element.** The diagonal entries of an element of
`borelSubgroup A` are units, with inverses the diagonal entries of its inverse. -/
theorem borelSubgroup_diag_mul_inv (b : ↥(borelSubgroup A)) (i : Fin 2) :
    ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i i *
        (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i i = 1 ∧
      (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i i *
        ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i i = 1 := by
  have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
  have hinv : (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
      Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := (b⁻¹).2
  have h1 : (((b : GL (Fin 2) A) * ((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
      GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i i = 1 := by
    rw [← Subgroup.coe_mul, mul_inv_cancel]
    simp
  have h2 : ((((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) * (b : GL (Fin 2) A) :
      GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i i = 1 := by
    rw [← Subgroup.coe_mul, inv_mul_cancel]
    simp
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h1 h2
  simp only [Subgroup.coe_inv] at hinv h1 h2 ⊢
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at h1 h2 ⊢
    rw [hinv, mul_zero, add_zero] at h1
    rw [hb, mul_zero, add_zero] at h2
    exact ⟨h1, h2⟩
  · simp only [Fin.mk_one, Fin.isValue] at h1 h2 ⊢
    rw [hb, zero_mul, zero_add] at h1
    rw [hinv, zero_mul, zero_add] at h2
    exact ⟨h1, h2⟩

theorem borelSubgroup_diag_mul (b c : ↥(borelSubgroup A)) (i : Fin 2) :
    (((b * c : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i i =
      ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i i *
        ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i i := by
  have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
  have hc : ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := c.2
  rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> simp [hb, hc]

/-- **First diagonal character of the Borel subgroup.** The character of `borelSubgroup A` given
by the upper-left entry. -/
def borelDiagFst : ↥(borelSubgroup A) →* Aˣ where
  toFun b :=
    { val := ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
      inv := (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
      val_inv := (borelSubgroup_diag_mul_inv b 0).1
      inv_val := (borelSubgroup_diag_mul_inv b 0).2 }
  map_one' := by
    apply Units.ext
    simp
  map_mul' b c := Units.ext (borelSubgroup_diag_mul b c 0)

/-- **Second diagonal character of the Borel subgroup.** The character of `borelSubgroup A`
given by the lower-right entry. -/
def borelDiagSnd : ↥(borelSubgroup A) →* Aˣ where
  toFun b :=
    { val := ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
      inv := (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
      val_inv := (borelSubgroup_diag_mul_inv b 1).1
      inv_val := (borelSubgroup_diag_mul_inv b 1).2 }
  map_one' := by
    apply Units.ext
    simp
  map_mul' b c := Units.ext (borelSubgroup_diag_mul b c 1)

@[simp] theorem borelDiagFst_apply_val (b : ↥(borelSubgroup A)) :
    ((borelDiagFst b : Aˣ) : A) = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 := rfl

@[simp] theorem borelDiagSnd_apply_val (b : ↥(borelSubgroup A)) :
    ((borelDiagSnd b : Aˣ) : A) = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 := rfl

theorem unipotentGL2_mem_borelSubgroup (x : A) : unipotentGL2 x ∈ borelSubgroup A := by
  simp

theorem borelDiagFst_unipotentGL2 (x : A) :
    borelDiagFst ⟨unipotentGL2 x, unipotentGL2_mem_borelSubgroup x⟩ = 1 := by
  apply Units.ext
  simp

theorem borelDiagSnd_unipotentGL2 (x : A) :
    borelDiagSnd ⟨unipotentGL2 x, unipotentGL2_mem_borelSubgroup x⟩ = 1 := by
  apply Units.ext
  simp

end Borel

section InducedSection

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **Adelic Borel subgroup.** The upper-triangular (Borel) subgroup of `GL(2, 𝔸_K)`. -/
abbrev adelicBorel : Subgroup (AdelicGL2 R K) := borelSubgroup (AdeleRing R K)

/-- **Induced section.** A function on `GL(2, 𝔸_K)` is an induced section for the pair of idele
characters `(χ₁, χ₂)` if it transforms on the left under the Borel subgroup by `χ₁ ⊠ χ₂`. -/
def IsInducedSection (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL2 R K → ℂ) : Prop :=
  ∀ (b : AdelicGL2 R K) (hb : b ∈ adelicBorel R K) (g : AdelicGL2 R K),
    φ (b * g)
      = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
        * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * φ g

/-- **Unitary idele character.** An idele character is unitary if all its values have absolute
value one. -/
def IsUnitaryChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AdeleRing R K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1

variable {R K}

theorem isInducedSection_unipotent_mul {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (x : AdeleRing R K)
    (g : AdelicGL2 R K) :
    φ (unipotentGL2 x * g) = φ g := by
  rw [hφ (unipotentGL2 x) (unipotentGL2_mem_borelSubgroup x) g, borelDiagFst_unipotentGL2,
    borelDiagSnd_unipotentGL2]
  simp

/-- **Complex power of a positive idele character.** The character `x ↦ α(x) ^ s` for a
positive real-valued idele character `α` and `s : ℂ`. -/
def cpowChar (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) :
    (AdeleRing R K)ˣ →* ℂˣ where
  toFun x := Units.mk0 ((((α x : ℝˣ) : ℝ) : ℂ) ^ s)
    (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (hα x).ne')))
  map_one' := by
    apply Units.ext
    change ((((α 1 : ℝˣ) : ℝ) : ℂ)) ^ s = 1
    rw [map_one, Units.val_one, Complex.ofReal_one, Complex.one_cpow]
  map_mul' x y := by
    apply Units.ext
    change ((((α (x * y) : ℝˣ) : ℝ) : ℂ)) ^ s
        = ((((α x : ℝˣ) : ℝ) : ℂ)) ^ s * ((((α y : ℝˣ) : ℝ) : ℂ)) ^ s
    rw [map_mul, Units.val_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (hα x).le (hα y).le s

@[simp] theorem cpowChar_apply_val (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    ((cpowChar α hα s x : ℂˣ) : ℂ) = (((α x : ℝˣ) : ℝ) : ℂ) ^ s := rfl

theorem norm_cpowChar_apply (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    ‖((cpowChar α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (hα x) s

/-- **First character of the principal series.** The character `μ · α ^ (s + 1/2)` of the
principal series attached to `μ`. -/
def etaFst (μ : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) : (AdeleRing R K)ˣ →* ℂˣ :=
  μ * cpowChar α hα (s + 1 / 2)

/-- **Second character of the principal series.** The character `ν · α ^ (-(s + 1/2))` of the
principal series attached to `ν`. -/
def etaSnd (ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) : (AdeleRing R K)ˣ →* ℂˣ :=
  ν * cpowChar α hα (-(s + 1 / 2))

theorem etaFst_apply (μ : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    etaFst μ α hα s x = μ x * cpowChar α hα (s + 1 / 2) x := rfl

theorem etaSnd_apply (ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    etaSnd ν α hα s x = ν x * cpowChar α hα (-(s + 1 / 2)) x := rfl

end InducedSection

section Weyl

variable {K : Type*} [Field K]

/-- **Weyl element of `GL(2)`.** The Weyl element `!![0, 1; 1, 0]` of `GL(2, K)`. -/
def gl2Weyl : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[simp] theorem gl2Weyl_val :
    ((gl2Weyl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

theorem gl2Weyl_inv : (gl2Weyl : GL (Fin 2) K)⁻¹ = gl2Weyl := Units.ext rfl

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **Adelic Weyl element.** The Weyl element as a rational point of `GL(2, 𝔸_K)`. -/
def adelicWeyl : AdelicGL2 R K :=
  globalPoints R K gl2Weyl

theorem adelicWeyl_inv : (adelicWeyl R K)⁻¹ = adelicWeyl R K := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

variable [MeasurableSpace (AdeleRing R K)]

/-- **Weyl intertwining integral.** The integral `∫ f (w⁻¹ n(x) g) dν(x)` of `f` at `g`. -/
def weylIntertwiningIntegral (ν : Measure (AdeleRing R K))
    (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) : ℂ :=
  ∫ x, f ((adelicWeyl R K)⁻¹ * unipotentGL2 x * g) ∂ν

end Weyl

end AutomorphicForm
