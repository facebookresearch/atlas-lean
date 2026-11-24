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

public import MathlibExt.Analysis.CStarAlgebra.Extension.StableSum.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases

/-!
# Strict calculus for supplied matrix sums

The sum respects strong unitary equivalence and takes two actual multiplier
lifts to an actual lift. The unitary/lift witnesses are constructed from the
given matrix identifications; source-standard associativity is not assumed
without an explicit hypothesis. The source algebra keeps the weak BusbyHom
telescope, and all quotient structures are the existing explicit factories.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra Matrix MultiplierAlgebra

namespace CStarExtension

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [StarAddMonoid A]
variable [NonUnitalCStarAlgebra B]

section Diagonal

variable (D : Type*) [CStarAlgebra D]

/-- The two entries of a product as a function on `Fin 2`. -/
@[no_expose]
private def pairToFinTwoStarAlgHom : D × D →⋆ₐ[ℂ] (Fin 2 → D) where
  toFun p := ![p.1, p.2]
  map_one' := by
    ext i
    fin_cases i <;> rfl
  map_mul' p q := by
    ext i
    fin_cases i <;> rfl
  map_zero' := by
    ext i
    fin_cases i <;> rfl
  map_add' p q := by
    ext i
    fin_cases i <;> rfl
  commutes' z := by
    ext i
    fin_cases i <;> rfl
  map_star' p := by
    ext i
    fin_cases i <;> rfl

/-- The existing matrix diagonal algebra map, with its star law. -/
@[no_expose]
private def diagonalStarAlgHom :
    (Fin 2 → D) →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) D :=
  (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin 2) (A := D)).toStarAlgHom.comp
    ({ Matrix.diagonalAlgHom ℂ with
      map_star' := fun x => (Matrix.diagonal_conjTranspose x).symm } :
      (Fin 2 → D) →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) D)

/-- The proof-private bundled two-entry diagonal map. -/
@[no_expose]
private def pairDiagonalStarAlgHom :
    D × D →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) D :=
  (diagonalStarAlgHom D).comp (pairToFinTwoStarAlgHom D)

/-- The literal generic two-entry diagonal matrix. -/
@[no_expose]
private def pairDiagonal (x y : D) : CStarMatrix (Fin 2) (Fin 2) D :=
  pairDiagonalStarAlgHom D (x, y)

@[simp]
private theorem pairDiagonal_apply (x y : D) :
    pairDiagonal D x y = CStarMatrix.ofMatrix (Matrix.diagonal ![x, y]) := by
  dsimp only [pairDiagonal, pairDiagonalStarAlgHom, diagonalStarAlgHom,
    pairToFinTwoStarAlgHom, StarAlgHom.comp_apply]
  change CStarMatrix.ofMatrixStarAlgEquiv (Matrix.diagonal ![x, y]) =
    CStarMatrix.ofMatrix (Matrix.diagonal ![x, y])
  exact (congrFun CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv
    (Matrix.diagonal ![x, y])).symm

private theorem pairDiagonal_map
    {E : Type*} [CStarAlgebra E] (f : D →⋆ₐ[ℂ] E) (x y : D) :
    (pairDiagonal D x y).map f = pairDiagonal E (f x) (f y) := by
  rw [pairDiagonal_apply, pairDiagonal_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply]

/-- The product unitary with the two prescribed components. -/
@[no_expose]
private def pairUnitary (u v : unitary D) : unitary (D × D) :=
  ⟨((u : D), (v : D)), Prod.mem_unitary_iff.2 ⟨u.property, v.property⟩⟩

/-- The actual diagonal matrix unitary. -/
@[no_expose]
private def pairDiagonalUnitary (u v : unitary D) :
    unitary (CStarMatrix (Fin 2) (Fin 2) D) :=
  Unitary.map (StarMonoidHom.ofClass (pairDiagonalStarAlgHom D)) (pairUnitary D u v)

@[simp]
private theorem pairDiagonalUnitary_coe (u v : unitary D) :
    (pairDiagonalUnitary D u v : CStarMatrix (Fin 2) (Fin 2) D) =
      pairDiagonal D (u : D) (v : D) :=
  rfl

private theorem pairDiagonal_conjugate (u v : unitary D) (x y : D) :
    (pairDiagonalUnitary D u v : CStarMatrix (Fin 2) (Fin 2) D) *
          pairDiagonal D x y *
          star (pairDiagonalUnitary D u v :
            CStarMatrix (Fin 2) (Fin 2) D) =
      pairDiagonal D ((u : D) * x * star (u : D))
        ((v : D) * y * star (v : D)) := by
  change pairDiagonalStarAlgHom D ((u : D), (v : D)) *
        pairDiagonalStarAlgHom D (x, y) *
        star (pairDiagonalStarAlgHom D ((u : D), (v : D))) =
      pairDiagonalStarAlgHom D
        (((u : D) * x * star (u : D)),
          ((v : D) * y * star (v : D)))
  rw [← map_star, ← map_mul, ← map_mul]
  rfl

end Diagonal

private theorem pairDiagonal_eq_twoDiagonal (x y : OuterMultiplier B) :
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    pairDiagonal (OuterMultiplier B) x y = twoDiagonal x y := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  change pairDiagonal (OuterMultiplier B) x y = twoDiagonal x y
  rw [pairDiagonal_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoDiagonal, CStarMatrix.ofMatrix_apply]

/-- The supplied stable sum respects strong unitary equivalence in both
variables. -/
theorem StableSumData.sum_congr_strong (S : StableSumData A B)
    {tau₁ tau₁' tau₂ tau₂' : BusbyHom A B}
    (h₁ : StronglyUnitaryEquivalent tau₁ tau₁')
    (h₂ : StronglyUnitaryEquivalent tau₂ tau₂') :
    StronglyUnitaryEquivalent (S.sum tau₁ tau₂) (S.sum tau₁' tau₂') := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨u₂, hu₂⟩ := h₂
  let q := outerQuotientMap (A := B)
  let qU₁ : unitary (OuterMultiplier B) := Unitary.map (StarMonoidHom.ofClass q) u₁
  let qU₂ : unitary (OuterMultiplier B) := Unitary.map (StarMonoidHom.ofClass q) u₂
  let diagonalU : unitary (CStarMatrix (Fin 2) (Fin 2) 𝓜(ℂ, B)) :=
    pairDiagonalUnitary 𝓜(ℂ, B) u₁ u₂
  let w : unitary 𝓜(ℂ, B) :=
    Unitary.map (StarMonoidHom.ofClass S.multiplierMatrixEquiv.toStarAlgHom) diagonalU
  have hw : q (w : 𝓜(ℂ, B)) =
      S.matrixEquiv
        (pairDiagonal (OuterMultiplier B) (q (u₁ : 𝓜(ℂ, B)))
          (q (u₂ : 𝓜(ℂ, B)))) := by
    calc
      q (w : 𝓜(ℂ, B)) =
          q (S.multiplierMatrixEquiv
            (pairDiagonal 𝓜(ℂ, B) (u₁ : 𝓜(ℂ, B)) (u₂ : 𝓜(ℂ, B)))) := by
        rfl
      _ = S.matrixEquiv
          ((pairDiagonal 𝓜(ℂ, B) (u₁ : 𝓜(ℂ, B))
            (u₂ : 𝓜(ℂ, B))).map q) :=
        (S.quotient_compatible _).symm
      _ = S.matrixEquiv
          (pairDiagonal (OuterMultiplier B) (q (u₁ : 𝓜(ℂ, B)))
            (q (u₂ : 𝓜(ℂ, B)))) := by
        rw [pairDiagonal_map]
  refine ⟨w, ?_⟩
  intro a
  calc
    S.sum tau₁' tau₂' a =
        S.matrixEquiv (twoDiagonal (tau₁' a) (tau₂' a)) :=
      S.sum_apply tau₁' tau₂' a
    _ = S.matrixEquiv
        (pairDiagonal (OuterMultiplier B) (tau₁' a) (tau₂' a)) := by
      rw [pairDiagonal_eq_twoDiagonal]
    _ = S.matrixEquiv
        (pairDiagonal (OuterMultiplier B)
          ((qU₁ : OuterMultiplier B) * tau₁ a * star (qU₁ : OuterMultiplier B))
          ((qU₂ : OuterMultiplier B) * tau₂ a * star (qU₂ : OuterMultiplier B))) := by
      rw [hu₁ a, hu₂ a]
      rfl
    _ = S.matrixEquiv
        ((pairDiagonalUnitary (OuterMultiplier B) qU₁ qU₂ :
            CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier B)) *
          pairDiagonal (OuterMultiplier B) (tau₁ a) (tau₂ a) *
          star (pairDiagonalUnitary (OuterMultiplier B) qU₁ qU₂ :
            CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier B))) := by
      rw [pairDiagonal_conjugate]
    _ = S.matrixEquiv
          (pairDiagonalUnitary (OuterMultiplier B) qU₁ qU₂ :
            CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier B)) *
        S.matrixEquiv (pairDiagonal (OuterMultiplier B) (tau₁ a) (tau₂ a)) *
        star (S.matrixEquiv
          (pairDiagonalUnitary (OuterMultiplier B) qU₁ qU₂ :
            CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier B))) := by
      rw [map_mul, map_mul, map_star]
    _ = q (w : 𝓜(ℂ, B)) * S.sum tau₁ tau₂ a *
        star (q (w : 𝓜(ℂ, B))) := by
      rw [hw, S.sum_apply, ← pairDiagonal_eq_twoDiagonal, pairDiagonalUnitary_coe]
      simp only [qU₁, qU₂, Unitary.coe_map, StarMonoidHom.ofClass_coe]

/-- The supplied stable sum of two trivial Busby maps is trivial. -/
theorem StableSumData.sum_trivial (S : StableSumData A B)
    {tau₁ tau₂ : BusbyHom A B}
    (h₁ : IsTrivial tau₁) (h₂ : IsTrivial tau₂) :
    IsTrivial (S.sum tau₁ tau₂) := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  obtain ⟨rho₁, hrho₁⟩ := h₁
  obtain ⟨rho₂, hrho₂⟩ := h₂
  let diagonalLift :
      A →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) 𝓜(ℂ, B) :=
    (pairDiagonalStarAlgHom 𝓜(ℂ, B)).toNonUnitalStarAlgHom.comp
      (rho₁.prod rho₂)
  let lift : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B) :=
    S.multiplierMatrixEquiv.toStarAlgHom.toNonUnitalStarAlgHom.comp diagonalLift
  refine ⟨lift, ?_⟩
  apply NonUnitalStarAlgHom.ext
  intro a
  let q := outerQuotientMap (A := B)
  have hrho₁a : q (rho₁ a) = tau₁ a := by
    exact DFunLike.congr_fun hrho₁ a
  have hrho₂a : q (rho₂ a) = tau₂ a := by
    exact DFunLike.congr_fun hrho₂ a
  change q (S.multiplierMatrixEquiv
      (pairDiagonal 𝓜(ℂ, B) (rho₁ a) (rho₂ a))) = S.sum tau₁ tau₂ a
  calc
    q (S.multiplierMatrixEquiv
        (pairDiagonal 𝓜(ℂ, B) (rho₁ a) (rho₂ a))) =
      S.matrixEquiv
        ((pairDiagonal 𝓜(ℂ, B) (rho₁ a) (rho₂ a)).map q) :=
      (S.quotient_compatible _).symm
    _ = S.matrixEquiv
        (pairDiagonal (OuterMultiplier B) (q (rho₁ a)) (q (rho₂ a))) := by
      rw [pairDiagonal_map]
    _ = S.matrixEquiv
        (pairDiagonal (OuterMultiplier B) (tau₁ a) (tau₂ a)) := by
      rw [hrho₁a, hrho₂a]
    _ = S.matrixEquiv (twoDiagonal (tau₁ a) (tau₂ a)) := by
      rw [pairDiagonal_eq_twoDiagonal]
    _ = S.sum tau₁ tau₂ a := (S.sum_apply tau₁ tau₂ a).symm

section Swap

variable (D : Type*) [CStarAlgebra D]

/-- The literal multiplier-matrix swap used only inside the strong-equivalence proof. -/
@[no_expose]
private def swapMatrix : CStarMatrix (Fin 2) (Fin 2) D :=
  fun i j => if i = j then 0 else 1

private theorem swapMatrix_star :
    star (swapMatrix D) = swapMatrix D := by
  ext i j
  simp only [CStarMatrix.star_eq_conjTranspose, CStarMatrix.conjTranspose_apply]
  unfold swapMatrix
  fin_cases i <;> fin_cases j <;> simp

private theorem swapMatrix_sq :
    swapMatrix D * swapMatrix D = 1 := by
  ext i j
  simp only [CStarMatrix.mul_apply, Fin.sum_univ_two, CStarMatrix.one_apply]
  unfold swapMatrix
  fin_cases i <;> fin_cases j <;> simp

/-- A genuinely unitary swap, with both unitary equations proved. -/
@[no_expose]
private def swapUnitary : unitary (CStarMatrix (Fin 2) (Fin 2) D) :=
  ⟨swapMatrix D, by
    change star (swapMatrix D) * swapMatrix D = 1 ∧
      swapMatrix D * star (swapMatrix D) = 1
    constructor
    · rw [swapMatrix_star]
      exact swapMatrix_sq D
    · rw [swapMatrix_star]
      exact swapMatrix_sq D⟩

private theorem swapMatrix_map {E : Type*} [CStarAlgebra E]
    (f : D →⋆ₐ[ℂ] E) :
    (swapMatrix D).map f = swapMatrix E := by
  ext i j
  simp only [CStarMatrix.map_apply]
  unfold swapMatrix
  fin_cases i <;> fin_cases j <;> simp

private theorem swapMatrix_conjugate (x y : D) :
    swapMatrix D * pairDiagonal D x y * star (swapMatrix D) =
      pairDiagonal D y x := by
  rw [swapMatrix_star, pairDiagonal_apply, pairDiagonal_apply]
  ext i j
  simp only [CStarMatrix.mul_apply, Fin.sum_univ_two, CStarMatrix.ofMatrix_apply]
  unfold swapMatrix
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

end Swap

/-- Any actual compatible matrix sum is strongly commutative via the finite multiplier swap.
No associativity, standard stabilization, source norm or nontriviality is assumed. -/
theorem StableSumData.sum_comm_strong (S : StableSumData A B)
    (tau₁ tau₂ : BusbyHom A B) :
    StronglyUnitaryEquivalent (S.sum tau₁ tau₂) (S.sum tau₂ tau₁) := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  let q := outerQuotientMap (A := B)
  let w : unitary 𝓜(ℂ, B) :=
    Unitary.map (StarMonoidHom.ofClass S.multiplierMatrixEquiv.toStarAlgHom)
      (swapUnitary 𝓜(ℂ, B))
  have hw : q (w : 𝓜(ℂ, B)) = S.matrixEquiv (swapMatrix (OuterMultiplier B)) := by
    calc
      q (w : 𝓜(ℂ, B)) =
          q (S.multiplierMatrixEquiv (swapMatrix 𝓜(ℂ, B))) := by rfl
      _ = S.matrixEquiv ((swapMatrix 𝓜(ℂ, B)).map q) :=
        (S.quotient_compatible _).symm
      _ = S.matrixEquiv (swapMatrix (OuterMultiplier B)) := by rw [swapMatrix_map]
  refine ⟨w, ?_⟩
  intro a
  calc
    S.sum tau₂ tau₁ a = S.matrixEquiv (twoDiagonal (tau₂ a) (tau₁ a)) :=
      S.sum_apply tau₂ tau₁ a
    _ = S.matrixEquiv
        (swapMatrix (OuterMultiplier B) *
          pairDiagonal (OuterMultiplier B) (tau₁ a) (tau₂ a) *
          star (swapMatrix (OuterMultiplier B))) := by
      rw [swapMatrix_conjugate, pairDiagonal_eq_twoDiagonal]
    _ = S.matrixEquiv (swapMatrix (OuterMultiplier B)) *
        S.matrixEquiv (pairDiagonal (OuterMultiplier B) (tau₁ a) (tau₂ a)) *
        star (S.matrixEquiv (swapMatrix (OuterMultiplier B))) := by
      rw [map_mul, map_mul, map_star]
    _ = q (w : 𝓜(ℂ, B)) * S.sum tau₁ tau₂ a *
        star (q (w : 𝓜(ℂ, B))) := by
      rw [hw, S.sum_apply, pairDiagonal_eq_twoDiagonal]

/-- The original coherence predicate needs only a supplied associativity law,
because strong commutativity follows from the actual matrix data. -/
theorem StableSumData.coherent_of_associative (S : StableSumData A B)
    (hAssoc : ∀ tau₁ tau₂ tau₃ : BusbyHom A B,
      StronglyUnitaryEquivalent (S.sum (S.sum tau₁ tau₂) tau₃)
        (S.sum tau₁ (S.sum tau₂ tau₃))) :
    S.IsCoherent :=
  ⟨hAssoc, S.sum_comm_strong⟩

end CStarExtension
