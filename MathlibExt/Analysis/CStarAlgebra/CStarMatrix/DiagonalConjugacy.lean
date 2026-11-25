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

public import MathlibExt.Analysis.CStarAlgebra.Extension.UnitaryHomClasses
public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.DiagonalPair
public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Actual block-diagonal conjugacy of paired star homomorphisms

The block unitary is constructed from the literal two diagonal entries.
Its two unitary equations use the existing diagonal-unitarity theorem.
The entrywise sandwich formula and paired-hom conjugacy require no norm,
commutativity, stable fold, group quotient or supplied block-unitarity law.
The generic construction uses the existing weak hom-class and diagonal maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix CStarAlgebra MultiplierAlgebra

universe uC uQ uP

namespace Unitary

variable {Q : Type uQ} [Semiring Q] [StarRing Q]

/-- Let `Q` be a semiring. The star on `Q` is an additive involution reversing products. For `u` and `v
: unitary Q`. The matrix unitary with u and v as its two diagonal entries.
-/
def blockDiagonalTwo (u v : unitary Q) :
    unitary (CStarMatrix (Fin 2) (Fin 2) Q) := by
  let entries : Fin 2 → Q := fun i => if i = 0 then (u : Q) else (v : Q)
  let M : Matrix (Fin 2) (Fin 2) Q := Matrix.diagonal entries
  have hentries : entries ∈ unitary (Fin 2 → Q) := by
    apply Pi.mem_unitary_iff.mpr
    intro i
    by_cases hi : i = 0
    · simpa only [entries, ite_eq_left hi] using u.prop
    · simpa only [entries, ite_eq_right hi] using v.prop
  have hM : M ∈ unitary (Matrix (Fin 2) (Fin 2) Q) :=
    Matrix.diagonal_mem_unitary.mpr hentries
  refine ⟨CStarMatrix.ofMatrix M, ?_⟩
  change Mᴴ * M = (1 : Matrix (Fin 2) (Fin 2) Q) ∧
    M * Mᴴ = (1 : Matrix (Fin 2) (Fin 2) Q)
  exact hM

/-- Let `Q` be a semiring. The star on `Q` is an additive involution reversing products. For `u` and `v
: unitary Q`. The block unitary's value is the diagonal `CStarMatrix` representation.
-/
theorem blockDiagonalTwo_val (u v : unitary Q) :
    (blockDiagonalTwo u v : CStarMatrix (Fin 2) (Fin 2) Q) =
      CStarMatrix.ofMatrix
        (Matrix.diagonal (fun i : Fin 2 => if i = 0 then (u : Q) else (v : Q))) := by
  rfl

/-- Let `Q` be a semiring. The star on `Q` is an additive involution reversing products. For `u` and `v
: unitary Q` and `i` and `j : Fin 2`. Exact entries, including both off-diagonal zeros, of the
computed unitary.
-/
theorem blockDiagonalTwo_apply (u v : unitary Q) (i j : Fin 2) :
    (blockDiagonalTwo u v : CStarMatrix (Fin 2) (Fin 2) Q) i j =
      if i = j then (if i = 0 then (u : Q) else (v : Q)) else 0 := by
  rfl

/-- Let `Q` be a semiring. The star on `Q` is an additive involution reversing products. For `u` and `v
: unitary Q`, `X : CStarMatrix (Fin 2) (Fin 2) Q` and `i` and `j : Fin 2`. Actual conjugation by the
block unitary multiplies each entry on the correct sides.
-/
theorem blockDiagonalTwo_conj_apply (u v : unitary Q)
    (X : CStarMatrix (Fin 2) (Fin 2) Q) (i j : Fin 2) :
    ((blockDiagonalTwo u v : CStarMatrix (Fin 2) (Fin 2) Q) * X *
        star (blockDiagonalTwo u v : CStarMatrix (Fin 2) (Fin 2) Q)) i j =
      (if i = 0 then (u : Q) else (v : Q)) * X i j *
        star (if j = 0 then (u : Q) else (v : Q)) := by
  simp only [blockDiagonalTwo_val]
  let diagonalEntries : Fin 2 → Q := fun k => if k = 0 then (u : Q) else (v : Q)
  let entries : Matrix (Fin 2) (Fin 2) Q := CStarMatrix.ofMatrix.symm X
  change ((Matrix.diagonal diagonalEntries * entries *
      (Matrix.diagonal diagonalEntries)ᴴ) i j) =
    diagonalEntries i * entries i j * star (diagonalEntries j)
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

end Unitary

namespace NonUnitalStarAlgHom

variable {C : Type uC} {Q : Type uQ}
variable [NonUnitalNonAssocSemiring C] [DistribMulAction ℂ C] [Star C]
variable [Semiring Q] [StarRing Q] [Algebra ℂ Q]

/-- Let `C` be a possibly nonunital, nonassociative semiring. Let `Q` be a semiring. `ℂ` acts on `C`
preserving addition and zero. `C` has a star operation. The star on `Q` is an additive involution
reversing products. `Q` has a complex algebra structure. For `phi₀`, `phi₁`, `psi₀` and `psi₁ : C
→⋆ₙₐ[ℂ] Q` and `u` and `v : unitary Q`. Assume `∀ a : C, psi₀ a = (u : Q) * phi₀ a * star (u : Q)`
and `∀ a : C, psi₁ a = (v : Q) * phi₁ a * star (v : Q)`. Two input conjugacies give conjugacy of
their diagonal hom maps.
-/
theorem diagonalPair_conjugate
    (phi₀ phi₁ psi₀ psi₁ : C →⋆ₙₐ[ℂ] Q) (u v : unitary Q)
    (h₀ : ∀ a : C, psi₀ a = (u : Q) * phi₀ a * star (u : Q))
    (h₁ : ∀ a : C, psi₁ a = (v : Q) * phi₁ a * star (v : Q)) :
    diagonalPair psi₀ psi₁ =
      (Unitary.conjStarAlgAut ℂ (CStarMatrix (Fin 2) (Fin 2) Q)
        (Unitary.blockDiagonalTwo u v)).toStarAlgHom.toNonUnitalStarAlgHom.comp
          (diagonalPair phi₀ phi₁) := by
  apply NonUnitalStarAlgHom.ext
  intro a
  change diagonalPair psi₀ psi₁ a =
    Unitary.conjStarAlgAut ℂ (CStarMatrix (Fin 2) (Fin 2) Q)
      (Unitary.blockDiagonalTwo u v) (diagonalPair phi₀ phi₁ a)
  rw [Unitary.conjStarAlgAut_apply]
  apply CStarMatrix.ext
  intro i j
  rw [Unitary.blockDiagonalTwo_conj_apply, diagonalPair_apply, diagonalPair_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    by_cases hi : i = 0
    · simpa only [ite_eq_left hi] using h₀ a
    · simpa only [ite_eq_right hi] using h₁ a
  · simp only [ite_eq_right hij, mul_zero, zero_mul]

end NonUnitalStarAlgHom

namespace CStarExtension

variable {C : Type uC} {P : Type uP}
variable [NonUnitalNonAssocSemiring C] [DistribMulAction ℂ C] [StarAddMonoid C]
variable [NonUnitalCStarAlgebra P]

attribute [local instance] CStarExtension.outerCStarAlgebra

/-- Let `C` be a possibly nonunital, nonassociative semiring. Let `P` be a possibly nonunital complex
C*-algebra. `ℂ` acts on `C` preserving addition and zero. `C` has an additive star involution. For
`tau₀`, `tau₁`, `sigma₀` and `sigma₁ : BusbyHom C P`, `h₀ : WeaklyUnitaryEquivalent tau₀ sigma₀` and
`h₁ : WeaklyUnitaryEquivalent tau₁ sigma₁`. Existing weak Busby conjugacies produce an block unitary
for the raw diagonal pair. This is not a statement of sum descent or liftability invariance.
-/
theorem diagonalPair_of_weakly_unitary_equivalent
    {tau₀ tau₁ sigma₀ sigma₁ : BusbyHom C P}
    (h₀ : WeaklyUnitaryEquivalent tau₀ sigma₀)
    (h₁ : WeaklyUnitaryEquivalent tau₁ sigma₁) :
    ∃ w : unitary (CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier P)),
      ∀ a : C,
        NonUnitalStarAlgHom.diagonalPair sigma₀ sigma₁ a =
          (w : CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier P)) *
            NonUnitalStarAlgHom.diagonalPair tau₀ tau₁ a *
            star (w : CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier P)) := by
  let _ : CStarAlgebra (OuterMultiplier P) := outerMultiplierCStarAlgebra P
  obtain ⟨u, hu⟩ := h₀
  obtain ⟨v, hv⟩ := h₁
  refine ⟨Unitary.blockDiagonalTwo u v, ?_⟩
  intro a
  have h := congrArg
    (fun eta : C →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier P) => eta a)
    (NonUnitalStarAlgHom.diagonalPair_conjugate tau₀ tau₁ sigma₀ sigma₁ u v hu hv)
  change NonUnitalStarAlgHom.diagonalPair sigma₀ sigma₁ a =
    Unitary.conjStarAlgAut ℂ (CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier P))
      (Unitary.blockDiagonalTwo u v)
      (NonUnitalStarAlgHom.diagonalPair tau₀ tau₁ a) at h
  simpa only [Unitary.conjStarAlgAut_apply] using h

end CStarExtension
