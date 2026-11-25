/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Basic
public import MathlibExt.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Algebra.Star.Subalgebra

/-!
# Unitization and finite C-star matrices

The unitization of a finite matrix algebra maps canonically into matrices over
the unitization.  Its image consists exactly of matrices whose scalar
coordinates form one scalar multiple of the identity matrix.

The constructions in this file are stated for an arbitrary finite index
type `ι`.  The projection-`K0` layer in
`MathlibExt.KTheory.CStar.K0.MatrixUnitization` specializes to `Fin n`,
because its amplification computation flattens `Fin k × Fin n` to
`Fin (k * n)` and concludes `n`-fold addition; that `Fin` arithmetic has no
analogue for a general finite index type.
-/

@[expose] public section

open scoped CStarAlgebra ComplexOrder Matrix

namespace CStarMatrix

noncomputable section

universe u v

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type. Entrywise
inclusion of a matrix algebra into matrices over the unitization of its coefficient algebra.
-/
def matrixInr
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] :
    CStarMatrix ι ι A →⋆ₙₐ[ℂ]
      CStarMatrix ι ι (Unitization ℂ A) :=
  CStarMatrix.mapₙₐ (Unitization.inrNonUnitalStarAlgHom ℂ A)

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type. For `M :
CStarMatrix ι ι A` and `i` and `j : ι`. Exact entry action of the entrywise matrix inclusion.
-/
@[simp]
theorem matrixInr_apply
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι]
    (M : CStarMatrix ι ι A) (i j : ι) :
    matrixInr A M i j = Unitization.inr (M i j) :=
  rfl

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type with decidable
equality. The canonical star-algebra map from the unitization of a matrix algebra to matrices over
the unitization.
-/
def matrixUnitizationMap
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Unitization ℂ (CStarMatrix ι ι A) →⋆ₐ[ℂ]
      CStarMatrix ι ι (Unitization ℂ A) :=
  Unitization.starLift (matrixInr A)

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type with decidable
equality. For `x : Unitization ℂ (CStarMatrix ι ι A)` and `i` and `j : ι`. Exact entry action of the
unitization-to-matrix map.
-/
@[simp]
theorem matrixUnitizationMap_apply
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Unitization ℂ (CStarMatrix ι ι A))
    (i j : ι) :
    matrixUnitizationMap A x i j =
      (if i = j then Unitization.inl x.fst else 0) +
        Unitization.inr (x.snd i j) := by
  change (algebraMap ℂ (CStarMatrix ι ι (Unitization ℂ A)) x.fst +
      matrixInr A x.snd) i j = _
  simp [CStarMatrix.algebraMap_apply, Unitization.algebraMap_eq_inl]

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type with decidable
equality. For `x : Unitization ℂ (CStarMatrix ι ι A)` and `i` and `j : ι`. The scalar coordinate of
each entry in the image is diagonal and constant along the diagonal.
-/
@[simp, nolint simpNF]
theorem matrixUnitizationMap_apply_fst
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Unitization ℂ (CStarMatrix ι ι A))
    (i j : ι) :
    (matrixUnitizationMap A x i j).fst =
      if i = j then x.fst else 0 := by
  rw [matrixUnitizationMap_apply]
  by_cases h : i = j <;> simp [h]

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type with decidable
equality. For `x : Unitization ℂ (CStarMatrix ι ι A)` and `i` and `j : ι`. The ideal coordinate of
the image recovers the matrix entry.
-/
@[simp, nolint simpNF]
theorem matrixUnitizationMap_apply_snd
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Unitization ℂ (CStarMatrix ι ι A))
    (i j : ι) :
    (matrixUnitizationMap A x i j).snd = x.snd i j := by
  rw [matrixUnitizationMap_apply]
  by_cases h : i = j <;> simp [h]

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type with decidable
equality. For `M : CStarMatrix ι ι A`. On the ideal summand, the canonical map is entrywise
`Unitization.inr`.
-/
@[simp]
theorem matrixUnitizationMap_inr
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : CStarMatrix ι ι A) :
    matrixUnitizationMap A (Unitization.inr M) = matrixInr A M := by
  apply CStarMatrix.ext
  intro i j
  apply Unitization.ext <;> simp

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type with decidable
equality. For `z : ℂ`. On the scalar summand, the canonical map is the scalar matrix algebra map.
-/
@[simp]
theorem matrixUnitizationMap_inl
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ℂ) :
    matrixUnitizationMap A (Unitization.inl z) =
      algebraMap ℂ (CStarMatrix ι ι (Unitization ℂ A)) z := by
  change matrixUnitizationMap A
      (algebraMap ℂ (Unitization ℂ (CStarMatrix ι ι A)) z) = _
  exact (matrixUnitizationMap A).commutes z

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type. Entrywise
scalar-coordinate projection on matrices over a unitization.
-/
def matrixFst
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] :
    CStarMatrix ι ι (Unitization ℂ A) →⋆ₙₐ[ℂ]
      CStarMatrix ι ι ℂ :=
  CStarMatrix.mapₙₐ
    (Unitization.fstStarAlgHom A).toNonUnitalStarAlgHom

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type. For `M :
CStarMatrix ι ι (Unitization ℂ A)` and `i` and `j : ι`. Exact entry action of entrywise
scalar-coordinate projection.
-/
@[simp]
theorem matrixFst_apply
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι]
    (M : CStarMatrix ι ι (Unitization ℂ A)) (i j : ι) :
    matrixFst A M i j = (M i j).fst := by
  simp [matrixFst]

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type with decidable
equality. For `x : Unitization ℂ (CStarMatrix ι ι A)`. Applying scalar-coordinate projection to the
image gives the scalar matrix with scalar `x.fst`.
-/
@[simp]
theorem matrixFst_matrixUnitizationMap
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Unitization ℂ (CStarMatrix ι ι A)) :
    matrixFst A (matrixUnitizationMap A x) =
      algebraMap ℂ (CStarMatrix ι ι ℂ) x.fst := by
  apply CStarMatrix.ext
  intro i j
  by_cases h : i = j <;> simp [CStarMatrix.algebraMap_apply, h]

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type.
Scalar-coordinate projection out of the unitization of a matrix algebra: the
`Unitization.fstStarAlgHom` projection at the matrix coefficient algebra, bundled directly from
`Unitization.fstHom`. Stating `Unitization.fstStarAlgHom (CStarMatrix ι ι A)` requires a
`NonUnitalCStarAlgebra (CStarMatrix ..)` instance, whose Mathlib construction needs a `PartialOrder`
and `StarOrderedRing` on `A` (the canonical spectral order) together with nondefault transparency to
reconcile the projected instances with the direct matrix instances. Naming the bundled hom here pins
that elaboration once: the scalar squares in this file and on projection `K0` are stated against
this hom with plain `[NonUnitalCStarAlgebra A]`, and its action is first projection by
`matrixScalarFst_apply`.
-/
def matrixScalarFst
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] :
    Unitization ℂ (CStarMatrix ι ι A) →⋆ₐ[ℂ] ℂ where
  toAlgHom := Unitization.fstHom ℂ _
  map_star' := Unitization.fst_star

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type. For `x :
Unitization ℂ (CStarMatrix ι ι A)`. The matrix scalar-coordinate projection is first projection.
-/
@[simp]
theorem matrixScalarFst_apply
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι]
    (x : Unitization ℂ (CStarMatrix ι ι A)) :
    matrixScalarFst A x = x.fst :=
  rfl

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type with decidable
equality. The scalar-coordinate square for the canonical unitization-to-matrix map commutes.
-/
theorem matrixFst_comp_matrixUnitizationMap
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (matrixFst A (ι := ι)).comp
        (matrixUnitizationMap A (ι := ι)).toNonUnitalStarAlgHom =
      ((StarAlgHom.ofId ℂ
          (CStarMatrix ι ι ℂ)).toNonUnitalStarAlgHom).comp
        (matrixScalarFst A (ι := ι)).toNonUnitalStarAlgHom := by
  apply NonUnitalStarAlgHom.ext
  intro x
  exact matrixFst_matrixUnitizationMap A x

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `B` be a possibly nonunital complex
C*-algebra. Let `ι` be a finite index type with decidable equality. For `phi : A →⋆ₙₐ[ℂ] B`. The
canonical unitization-to-matrix map is natural for nonunital complex star-algebra homomorphisms.
-/
theorem matrixUnitizationMap_naturality
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (phi : A →⋆ₙₐ[ℂ] B) :
    (matrixUnitizationMap B (ι := ι)).toNonUnitalStarAlgHom.comp
        (Unitization.starMap (CStarMatrix.mapₙₐ phi)).toNonUnitalStarAlgHom =
      (CStarMatrix.mapₙₐ
        (Unitization.starMap phi).toNonUnitalStarAlgHom).comp
          (matrixUnitizationMap A (ι := ι)).toNonUnitalStarAlgHom := by
  apply NonUnitalStarAlgHom.ext
  intro x
  induction x using Unitization.ind with
  | inl_add_inr z M =>
      apply CStarMatrix.ext
      intro i j
      by_cases h : i = j <;> apply Unitization.ext <;>
        simp [matrixUnitizationMap_apply,
          Unitization.algebraMap_eq_inl, CStarMatrix.algebraMap_apply,
          CStarMatrix.zero_apply, h]

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite nonempty index type with
decidable equality. For a nonempty index type, the canonical unitization-to-matrix map is injective.
-/
theorem matrixUnitizationMap_injective
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Injective (matrixUnitizationMap A (ι := ι)) := by
  intro x y hxy
  apply Unitization.ext
  · obtain ⟨i₀⟩ := ‹Nonempty ι›
    have h := congrArg
      (fun M : CStarMatrix ι ι (Unitization ℂ A) ↦
        (M i₀ i₀).fst) hxy
    simpa using h
  · apply CStarMatrix.ext
    intro i j
    have h := congrArg
      (fun M : CStarMatrix ι ι (Unitization ℂ A) ↦
        (M i j).snd) hxy
    simpa only [matrixUnitizationMap_apply_snd] using h

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type with decidable
equality. For `M : CStarMatrix ι ι (Unitization ℂ A)`. A matrix over the unitization lies in the
scalar-plus-matrix range exactly when all scalar coordinates form one scalar multiple of the
identity.
-/
theorem mem_range_matrixUnitizationMap_iff
    (A : Type u) [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : CStarMatrix ι ι (Unitization ℂ A)) :
    M ∈ (matrixUnitizationMap A).range ↔
      ∃ z : ℂ, ∀ i j : ι,
        (M i j).fst = if i = j then z else 0 := by
  constructor
  · rintro ⟨(x : Unitization ℂ
        (CStarMatrix ι ι A)), rfl⟩
    exact ⟨x.fst, matrixUnitizationMap_apply_fst A x⟩
  · rintro ⟨z, hz⟩
    let X : CStarMatrix ι ι A := fun i j ↦ (M i j).snd
    let x : Unitization ℂ (CStarMatrix ι ι A) :=
      Unitization.inl z + Unitization.inr X
    refine ⟨x, ?_⟩
    have hxfst : x.fst = z := by
      simp only [x, Unitization.fst_add, Unitization.fst_inl,
        Unitization.fst_inr, add_zero]
    have hxsnd : x.snd = X := by
      simp only [x, Unitization.snd_add, Unitization.snd_inl,
        Unitization.snd_inr, zero_add]
    apply CStarMatrix.ext
    intro i j
    apply Unitization.ext
    · change (matrixUnitizationMap A x i j).fst = (M i j).fst
      simpa only [matrixUnitizationMap_apply_fst, hxfst] using (hz i j).symm
    · change (matrixUnitizationMap A x i j).snd = (M i j).snd
      simp only [matrixUnitizationMap_apply_snd, hxsnd]
      rfl

end

end CStarMatrix
