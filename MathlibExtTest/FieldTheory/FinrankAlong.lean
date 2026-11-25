/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.FinrankAlong
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

@[expose] public section

open AlgebraicCurve Polynomial
open scoped RatFunc

namespace MathlibExtTest.FieldTheory.FinrankAlong

/-- Consumer with the source's binders: two homomorphisms given as
composites through a common homomorphism, with first factors of equal
degree. -/
example {K F M T : Type*} [Field K] [Field F] [Field M] [Field T]
    [Algebra K F] [Algebra K M] [Algebra K T]
    (incl subst : F →ₐ[K] T) (common : M →ₐ[K] T)
    (alpha beta : F →ₐ[K] M)
    (hincl : incl = common.comp alpha) (hsubst : subst = common.comp beta)
    (hab : finrankAlong alpha = finrankAlong beta) :
    finrankAlong incl = finrankAlong subst := by
  subst hincl hsubst
  exact finrankAlong_eq_of_comp_eq_of_finrankAlong_eq common alpha beta hab

/-- The degree along the identity is one. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] :
    finrankAlong (AlgHom.id K F) = Module.finrank F F :=
  rfl

/-- The identity is finite, so its degree is nonzero. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] :
    finrankAlong (AlgHom.id K F) ≠ 0 :=
  (finrankAlong_ne_zero_iff _).mpr (AlgHom.Finite.id K F)

/-- Infinite case: `t` is transcendental over `K`, so `K(t)` is
infinite-dimensional over `K` and the structure map `K → K(t)` has degree `0`. -/
example {K : Type*} [Field K] : finrankAlong (Algebra.ofId K K⟮X⟯) = 0 := by
  by_contra h
  have : Module.Finite K K⟮X⟯ :=
    RingHom.finite_algebraMap.mp ((finrankAlong_ne_zero_iff _).mp h)
  exact RatFunc.transcendental_X (IsAlgebraic.of_finite K _)

/-- A homomorphism of degree one is surjective. -/
private theorem surjective_of_finrankAlong_eq_one {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] {φ : F →ₐ[K] F'} (h : finrankAlong φ = 1) :
    Function.Surjective φ := by
  let := φ.toRingHom.toAlgebra
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2

variable (K : Type*) [Field K]

/-- The substitution `t ↦ t ^ 2` on `K(t)`. -/
private noncomputable def sqSubst : K⟮X⟯ →ₐ[K] K⟮X⟯ :=
  RatFunc.mapAlgHom (expand K 2)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (expand_injective two_pos))

/-- The substitution `t ↦ -t` on `K(t)`. -/
private noncomputable def negSubst : K⟮X⟯ →ₐ[K] K⟮X⟯ :=
  RatFunc.mapAlgHom (algEquivAevalNegX : K[X] ≃ₐ[K] K[X]).toAlgHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ algEquivAevalNegX.injective)

variable {K}

/-- A substitution induced by a polynomial map sends a polynomial to its image. -/
private theorem mapAlgHom_algebraMap (φ : K[X] →ₐ[K] K[X]) (hφ) (p : K[X]) :
    RatFunc.mapAlgHom φ hφ (algebraMap K[X] K⟮X⟯ p) = algebraMap K[X] K⟮X⟯ (φ p) := by
  simpa [RatFunc.coe_mapAlgHom_eq_coe_map] using RatFunc.map_apply_div φ hφ p 1

/-- `t ↦ -t` fixes every value of `t ↦ t ^ 2`. -/
private theorem negSubst_sqSubst (f : K⟮X⟯) : negSubst K (sqSubst K f) = sqSubst K f := by
  have key (r : K[X]) : algEquivAevalNegX (expand K 2 r) = expand K 2 r := by
    simp [expand_eq_comp_X_pow, ← comp_eq_aeval, comp_assoc]
  induction f using RatFunc.induction_on with
  | f p q _ =>
    simp only [map_div₀, negSubst, sqSubst, mapAlgHom_algebraMap, AlgEquiv.toAlgHom_apply, key]

/-- In characteristic zero, `t ↦ t ^ 2` does not have degree one: its image
is fixed by `t ↦ -t`, which moves `t`, so `t` is not in its image. -/
private theorem finrankAlong_sqSubst_ne_one [CharZero K] : finrankAlong (sqSubst K) ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := surjective_of_finrankAlong_eq_one h (algebraMap K[X] K⟮X⟯ X)
  have hneg : negSubst K (algebraMap K[X] K⟮X⟯ X) = algebraMap K[X] K⟮X⟯ X := by
    rw [← hc, negSubst_sqSubst]
  rw [negSubst, mapAlgHom_algebraMap] at hneg
  have := congrArg (fun p : K[X] => p.coeff 1) (RatFunc.algebraMap_injective K hneg)
  norm_num [AlgEquiv.toAlgHom_apply] at this

/-- Boundary case: the equal-degree hypothesis on the first factors cannot be
dropped. On `K(t)` in characteristic zero, the first factors `id` and
`t ↦ t ^ 2` have different degrees, and so do their composites with the
common factor `id`. -/
example [CharZero K] : finrankAlong (AlgHom.id K K⟮X⟯) ≠ finrankAlong (sqSubst K) ∧
    finrankAlong ((AlgHom.id K K⟮X⟯).comp (AlgHom.id K K⟮X⟯)) ≠
      finrankAlong ((AlgHom.id K K⟮X⟯).comp (sqSubst K)) := by
  have hid : finrankAlong (AlgHom.id K K⟮X⟯) = 1 := Module.finrank_self K⟮X⟯
  rw [finrankAlong_comp, finrankAlong_comp, hid, mul_one, mul_one]
  exact ⟨fun h => finrankAlong_sqSubst_ne_one h.symm,
    fun h => finrankAlong_sqSubst_ne_one h.symm⟩

end MathlibExtTest.FieldTheory.FinrankAlong
