/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Star.StarAlgHom
public import MathlibExt.Analysis.Normed.Operator.FiniteInflation
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual diagonal star amplification on finite full-H Hilbert coordinates

The bounded operator and its norm API come from the canonical finite
inflation of complex normed spaces. The coordinate inner product proves
the original adjoint law. The canonical linear-map factory bundles that
same operator as a unital star-algebra homomorphism; representation
inflation is composition with it. No second coordinate constructor,
Hilbert basis or model certificate is supplied. Zero coordinates and
zero Hilbert spaces are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

noncomputable section

universe u v

/-- **Adjoint of a finite diagonal amplification.** For a complete complex Hilbert space `H`, a natural
number `n`, and a bounded operator `T` on `H`, the coordinatewise amplification to the Hilbert sum
of `n` copies of `H` commutes with taking adjoints: amplification of `T*` is the adjoint of
amplification of `T`. -/
theorem ContinuousLinearMap.finiteInflation_star
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (n : ℕ) (T : H →L[ℂ] H) :
    ContinuousLinearMap.finiteInflation n (star T) =
      star (ContinuousLinearMap.finiteInflation n T) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.finiteInflation_apply, ContinuousLinearMap.finiteInflation_apply,
    ContinuousLinearMap.adjoint_inner_left]

namespace MathlibExt.Analysis.CStarAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Finite diagonal star homomorphism.** Let `H` be a complete complex Hilbert space and `n ∈ ℕ`. The
assignment `T ↦ diag(T,…,T)` is a unital complex star-algebra homomorphism from `B(H)` to the
bounded operators on the Hilbert sum of `n` copies of `H`. -/
def finiteCoordinateStarAlgHom (n : ℕ) :
    (H →L[ℂ] H) →⋆ₐ[ℂ]
      (PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) := by
  let L : (H →L[ℂ] H) →ₗ[ℂ]
      (PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :=
    { toFun := ContinuousLinearMap.finiteInflation n
      map_add' := ContinuousLinearMap.finiteInflation_add n
      map_smul' := by
        intro c A
        simpa only [RingHom.id_apply] using ContinuousLinearMap.finiteInflation_smul n c A }
  let f := NonUnitalStarAlgHom.ofLinearMap L
    (ContinuousLinearMap.finiteInflation_mul n) (ContinuousLinearMap.finiteInflation_star n)
  exact
    { toAlgHom := AlgHom.mk'
        { toFun := f
          map_zero' := map_zero f
          map_one' := ContinuousLinearMap.finiteInflation_one n
          map_add' := map_add f
          map_mul' := map_mul f }
        (fun c A => map_smul f c A)
      map_star' := map_star f }

/-- **Coordinates of diagonal amplification.** Let `H` be a complete complex Hilbert space and `n ∈ ℕ`.
For a bounded operator `T`, a tuple `x` in the Hilbert sum of `n` copies of `H`, and `i ∈ Fin n`,
the amplified operator has coordinate `T(xᵢ)`. -/
theorem finiteCoordinateStarAlgHom_apply (n : ℕ) (A : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    finiteCoordinateStarAlgHom (H := H) n A x i = A (x i) :=
  ContinuousLinearMap.finiteInflation_apply n A x i

end MathlibExt.Analysis.CStarAlgebra

namespace StarAlgHom

variable {A : Type u} [Semiring A] [Algebra ℂ A] [Star A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Finite amplification of a representation.** Let `A` be a complex algebra with a star operation,
let `H` be a complete complex Hilbert space, let `π : A → B(H)` be a unital complex star
homomorphism, and let `n ∈ ℕ`. Its amplification is the unital star representation on the Hilbert
sum of `n` copies of `H`, acting by `π(a)` on every coordinate. -/
def finiteInflation (n : ℕ) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₐ[ℂ] (PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :=
  (MathlibExt.Analysis.CStarAlgebra.finiteCoordinateStarAlgHom (H := H) n).comp π

/-- **Coordinates of an amplified representation.** Let `A` be a complex algebra with a star operation,
let `H` be a complete complex Hilbert space, let `π : A → B(H)` be a unital complex star
homomorphism, and let `n ∈ ℕ`. For `a ∈ A` and a tuple `x` in that Hilbert sum, the amplified
representation has `i` coordinate `π(a)(xᵢ)` for every `i ∈ Fin n`. -/
@[simp]
theorem finiteInflation_apply (n : ℕ) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A)
    (x : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    finiteInflation n π a x i = (π a) (x i) :=
  MathlibExt.Analysis.CStarAlgebra.finiteCoordinateStarAlgHom_apply n (π a) x i

end StarAlgHom

end
