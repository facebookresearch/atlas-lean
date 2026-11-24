/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HarmonicChernWeilFormulas

/-!
# Low-degree evaluations of the Chern--Weil polynomial

`chernWeilValue` is `chernWeilPolynomial` of the curvature
(`chernWeilValue_eq_chernWeilPolynomial`).
For diagonal curvature `diag(ω₁, ω₂)` the total Chern form is `(1 + (i/2π) ω₁)(1 + (i/2π) ω₂)`, so
`c₁ = (i/2π)(ω₁ + ω₂)` and `c₂ = (i/2π)² ω₁ ∧ ω₂`; and every Chern form of degree above the rank
vanishes. The evaluations below check these signs and the `2^j j!` normalization on basis vectors.
-/

namespace MathlibExtTest.AlgebraicGeometry.HarmonicChernWeilFormulas

open MathlibExt.AlgebraicGeometry.HarmonicChernWeilFormulas

/-- Embeddings of `Fin 2` into itself are the permutations (used to evaluate the sums). -/
theorem sum_embedding_fin_two {R : Type*} [AddCommMonoid R] (F : (Fin 2 ↪ Fin 2) → R) :
    ∑ f, F f = ∑ e : Equiv.Perm (Fin 2), F e.toEmbedding :=
  (Fintype.sum_bijective (fun e : Equiv.Perm (Fin 2) => e.toEmbedding)
    ⟨fun a b h => Equiv.ext fun x => DFunLike.congr_fun h x,
      fun f => ⟨Equiv.ofBijective f f.injective.bijective_of_finite,
        Function.Embedding.ext fun _ => rfl⟩⟩ _ _ fun _ => rfl).symm

/-- Embeddings of `Fin 1` into `Fin 2` are the points of `Fin 2`. -/
theorem sum_embedding_fin_one {R : Type*} [AddCommMonoid R] (F : (Fin 1 ↪ Fin 2) → R) :
    ∑ f, F f = ∑ k : Fin 2, F ⟨fun _ => k, fun _ _ _ => Subsingleton.elim _ _⟩ :=
  (Fintype.sum_bijective (fun k : Fin 2 => (⟨fun _ => k, fun _ _ _ => Subsingleton.elim _ _⟩ :
      Fin 1 ↪ Fin 2))
    ⟨fun a b h => DFunLike.congr_fun h 0,
      fun f => ⟨f 0, Function.Embedding.ext fun x => by rw [Subsingleton.elim x 0]; rfl⟩⟩
    _ _ fun _ => rfl).symm

/-- The basis two-form `e^a ∧ e^b` on basis vectors, with values in `ℤ`. -/
def basisForm (a b : Fin 4) (x y : Fin 4) : ℤ :=
  if x = a ∧ y = b then 1 else if x = b ∧ y = a then -1 else 0

/-- Diagonal curvature `diag(e¹ ∧ e², e³ ∧ e⁴)` on basis vectors. -/
def diagonalCurvature (x y : Fin 4) : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.diagonal ![basisForm 0 1 x y, basisForm 2 3 x y]

/-- Degree two: the signed minor sum of `diag(e¹ ∧ e², e³ ∧ e⁴)` on `e₁, …, e₄` is
`2^2 · 2! = 8`. -/
theorem diagonal_degree_two_sum : chernWeilSum 2 2 diagonalCurvature id = 8 := by
  rw [chernWeilSum, sum_embedding_fin_two]
  decide

/-- Degree two: `c₂ = (i/2π)² (e¹ ∧ e² ∧ e³ ∧ e⁴)(e₁, …, e₄) = (i/2π)²`. -/
theorem diagonal_degree_two :
    chernWeilPolynomial 2 2 (fun x y => (diagonalCurvature x y).map (Int.castRingHom ℂ)) id =
      (Complex.I / (2 * (Real.pi : ℂ))) ^ 2 := by
  rw [chernWeilPolynomial, ← map_chernWeilSum, diagonal_degree_two_sum]
  norm_num [Nat.factorial]

/-- Diagonal curvature `diag(e¹ ∧ e², 2 e¹ ∧ e²)` on the first two basis vectors. -/
def diagonalCurvatureOne (x y : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.diagonal ![basisForm 0 1 x.castSucc.castSucc y.castSucc.castSucc,
    2 * basisForm 0 1 x.castSucc.castSucc y.castSucc.castSucc]

theorem diagonal_degree_one_sum : chernWeilSum 2 1 diagonalCurvatureOne id = 6 := by
  rw [chernWeilSum, sum_embedding_fin_one]
  decide

/-- Degree one: `c₁ = (i/2π) tr Ω(e₁, e₂) = 3 (i/2π)`. -/
theorem diagonal_degree_one :
    chernWeilPolynomial 2 1 (fun x y => (diagonalCurvatureOne x y).map (Int.castRingHom ℂ)) id =
      3 * (Complex.I / (2 * (Real.pi : ℂ))) := by
  rw [chernWeilPolynomial, ← map_chernWeilSum, diagonal_degree_one_sum]
  norm_num [Nat.factorial]
  ring

/-- Degree above the rank: every degree-two Chern--Weil polynomial of a line bundle vanishes. -/
theorem rank_one_degree_two {V : Type*} (Ω : V → V → Matrix (Fin 1) (Fin 1) ℂ)
    (v : Fin (2 * 2) → V) : chernWeilPolynomial 1 2 Ω v = 0 := by
  have : IsEmpty (Fin 2 ↪ Fin 1) := ⟨fun f => absurd (f.injective.eq_iff.1
    (Subsingleton.elim (f 0) (f 1))) (by decide)⟩
  simp [chernWeilPolynomial, chernWeilSum]

end MathlibExtTest.AlgebraicGeometry.HarmonicChernWeilFormulas
