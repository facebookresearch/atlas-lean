/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.DGAlgebras
public import MathlibExt.CategoryTheory.MonoidalTensorWordModels
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Source-normalized cyclic bar models of actual DG algebras

A DG algebra is a native monoid object in coefficient cochain complexes.
Every bar term is its actual tensor power. Faces multiply consecutive
factors, the last face first performs Koszul cyclic rotation, and
degeneracies insert the actual unit. No internal differential, bar face
or cyclic operator is an unrelated supplied linear map.

The simplicial assembly is a construction output normalized on every
face and degeneracy. Its existence is separate from the Hodge-to-de Rham
degeneration theorem. Kaledin's nonnegative grading restriction is kept
as an explicit predicate on the actual cochain terms.

References: Kaledin, arXiv:math/0611623v4, §1.3 and equations 1.16--1.17;
Loday, Cyclic homology, §1.1. The cochain monoidal primitives are the
completed, Apache-attributed DGSource ports.
-/

@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.DGCyclicBarModels

open _root_.CategoryTheory MonoidalCategory Opposite Limits
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.MonoidalTensorWordModels

universe u

variable {k : Type u} [CommRing k]

/-- Actual right-associated tensor powers, with the native tensor unit. -/
def tensorPower (A : Cochains k) : ℕ → Cochains k
  | 0 => 𝟙_ (Cochains k)
  | n + 1 => A ⊗ tensorPower A n

/-- The power is the fixed tensor word used by the native braiding. -/
theorem tensorPower_eq_word (A : Cochains k) (n : ℕ) :
    tensorPower A n = word (List.replicate n A) := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [tensorPower, List.replicate_succ, word, hn]

/-- The unsigned cyclic operator, including the Koszul braiding. The
separate cyclic-complex sign (-1)^n is not inserted in this operator. -/
def cyclicRotation (A : Cochains k) (n : ℕ) :
    tensorPower A (n + 1) ≅ tensorPower A (n + 1) :=
  eqToIso (by
    rw [tensorPower_eq_word]
    congr 1
    induction n with
    | zero => rfl
    | succ n hn =>
      simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons A) hn) ≪≫
    rotateLast (List.replicate n A) A ≪≫
      eqToIso (by rw [tensorPower, tensorPower_eq_word]; rfl)

/-- Multiplication at an actual consecutive pair of factors. -/
def internalFace (A : DGAlgebra k) : (n : ℕ) →
    Fin (n + 1) → (tensorPower A.X (n + 2) ⟶ tensorPower A.X (n + 1))
  | 0, _ => (α_ A.X A.X (tensorPower A.X 0)).inv ≫
      (MonObj.mul (X := A.X) ⊗ₘ 𝟙 (tensorPower A.X 0))
  | n + 1, i => Fin.cases
      ((α_ A.X A.X (tensorPower A.X (n + 1))).inv ≫
        (MonObj.mul (X := A.X) ⊗ₘ 𝟙 (tensorPower A.X (n + 1))))
      (fun j => 𝟙 A.X ⊗ₘ internalFace A n j) i

/-- The Hochschild faces, including the last-first multiplication. -/
def barFace (A : DGAlgebra k) (n : ℕ) (i : Fin (n + 2)) :
    tensorPower A.X (n + 2) ⟶ tensorPower A.X (n + 1) :=
  Fin.lastCases ((cyclicRotation A.X (n + 1)).hom ≫ internalFace A n 0)
    (fun j => internalFace A n j) i

/-- Unit insertion after the indicated factor. -/
def barDegeneracy (A : DGAlgebra k) : (n : ℕ) →
    Fin (n + 1) → (tensorPower A.X (n + 1) ⟶ tensorPower A.X (n + 2))
  | 0, _ => 𝟙 A.X ⊗ₘ
      ((λ_ (tensorPower A.X 0)).inv ≫
        (MonObj.one (X := A.X) ⊗ₘ 𝟙 (tensorPower A.X 0)))
  | n + 1, i => Fin.cases
      (𝟙 A.X ⊗ₘ ((λ_ (tensorPower A.X (n + 1))).inv ≫
        (MonObj.one (X := A.X) ⊗ₘ 𝟙 (tensorPower A.X (n + 1)))))
      (fun j => 𝟙 A.X ⊗ₘ barDegeneracy A n j) i

/-- The actual simplicial cyclic-bar assembly. All its generators are
fixed, so the model cannot contain an unrelated cyclic invariant. -/
structure CyclicBarModel (A : DGAlgebra k) where
  simplicial : SimplicialObject (Cochains k)
  termIso : ∀ n : ℕ, simplicial.obj (op (SimplexCategory.mk n)) ≅ tensorPower A.X (n + 1)
  face_eq : ∀ (n : ℕ) (i : Fin (n + 2)),
    simplicial.δ i ≫ (termIso n).hom =
      (termIso (n + 1)).hom ≫ barFace A n i
  degeneracy_eq : ∀ (n : ℕ) (i : Fin (n + 1)),
    simplicial.σ i ≫ (termIso (n + 1)).hom =
      (termIso n).hom ≫ barDegeneracy A n i

/-- Rotation of a model is computed by conjugating the native tensor
rotation; it is not additional freely chosen data. -/
def modelRotation {A : DGAlgebra k} (B : CyclicBarModel A) (n : ℕ) :
    B.simplicial.obj (op (SimplexCategory.mk n)) ≅
      B.simplicial.obj (op (SimplexCategory.mk n)) :=
  B.termIso n ≪≫ cyclicRotation A.X n ≪≫ (B.termIso n).symm

/-- Kaledin's grading hypothesis on the actual DG algebra. -/
def IsNonnegativelyGraded (A : DGAlgebra k) : Prop :=
  ∀ i : ℤ, i < 0 → IsZero (A.X.X i)

end MathlibExt.Algebra.Homology.DGCyclicBarModels
