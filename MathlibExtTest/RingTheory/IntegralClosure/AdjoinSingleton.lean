/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.IntegralClosure.AdjoinSingleton
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.RingTheory.PowerBasis

@[expose] public section

-- `exactSource` consumer with the original binders.
example {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (x : F)
    (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    Module.Finite (Algebra.adjoin k ({x} : Set F))
      (integralClosure (Algebra.adjoin k ({x} : Set F)) F) :=
  Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed x hx hfd

-- Higher-universe consumer: the statement is universe-polymorphic.
example {k F : Type 1} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (x : F)
    (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    Module.Finite (Algebra.adjoin k ({x} : Set F))
      (integralClosure (Algebra.adjoin k ({x} : Set F)) F) :=
  Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed x hx hfd

namespace AdjoinSingletonTest

open Polynomial

/-- A concrete instance with every hypothesis satisfied: `x = X` in `F = k(X)`, where
`k(x)` is all of `F`. -/
example (k : Type*) [Field k] [IsAlgClosed k] :
    Module.Finite (Algebra.adjoin k ({RatFunc.X} : Set (RatFunc k)))
      (integralClosure (Algebra.adjoin k ({RatFunc.X} : Set (RatFunc k))) (RatFunc k)) := by
  refine Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed _
    RatFunc.transcendental_X ?_
  rw [RatFunc.adjoin_X]
  exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top

/-- `X` is not a `p`-th power in `k(X)` for a prime `p`: comparing degrees would give
`p * d = 1`. -/
private theorem pow_ne_X (k : Type*) [Field k] {p : ℕ} (hp : p.Prime) (b : RatFunc k) :
    b ^ p ≠ RatFunc.X := by
  intro h
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at h
    exact RatFunc.X_ne_zero h.symm
  have hdeg : ∀ n : ℕ, (b ^ n).intDegree = n * b.intDegree := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hb) hb, ih]
      push_cast
      ring
  have h1 := congrArg RatFunc.intDegree h
  rw [hdeg, RatFunc.intDegree_X] at h1
  have h2 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) ⟨_, h1.symm⟩
  exact hp.one_lt.ne' (by exact_mod_cast h2)

/-- In an algebraically closed extension `L` of `k(X)`, the integral closure of `k[X]` is not
a finite `k[X]`-module: it contains a `p`-th root of `X` for every prime `p`, of degree `p`
over `k(X)`, while a finite `k[X]`-module spans a finite-dimensional `k(X)`-subspace. -/
private theorem not_finite_integralClosure {k L : Type*} [Field k] [Field L] [Algebra k L]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [IsAlgClosed L] :
    ¬ Module.Finite (Algebra.adjoin k ({algebraMap (RatFunc k) L RatFunc.X} : Set L))
      (integralClosure (Algebra.adjoin k ({algebraMap (RatFunc k) L RatFunc.X} : Set L)) L) := by
  intro hfin
  obtain ⟨S, hS⟩ := Module.finite_def.mp hfin
  -- Every element of `k[X]` comes from `k(X)`.
  have hA : ∀ a ∈ Algebra.adjoin k ({algebraMap (RatFunc k) L RatFunc.X} : Set L),
      ∃ c : RatFunc k, algebraMap (RatFunc k) L c = a := by
    intro a ha
    have hle : Algebra.adjoin k ({algebraMap (RatFunc k) L RatFunc.X} : Set L) ≤
        (IsScalarTower.toAlgHom k (RatFunc k) L).range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((AlgHom.mem_range _).mpr ⟨RatFunc.X, rfl⟩))
    exact (AlgHom.mem_range _).mp (hle ha)
  let T : Finset L := S.map (Function.Embedding.subtype _)
  -- So the integral closure lies in the `k(X)`-span of the finite set `T`.
  have hspan : ∀ r : integralClosure
      (Algebra.adjoin k ({algebraMap (RatFunc k) L RatFunc.X} : Set L)) L,
      (r : L) ∈ Submodule.span (RatFunc k) (T : Set L) := by
    intro r
    have hr : r ∈ Submodule.span _ (S : Set _) := hS ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_map_of_mem _ hs))
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      obtain ⟨c, hc⟩ := hA a a.2
      change (a : L) * (y : L) ∈ _
      rw [← hc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ c hy
  -- A `p`-th root `y` of `X` for a prime `p > |T|` is integral, and `T ^ p - X` is its
  -- minimal polynomial over `k(X)`, so its first `p` powers are independent in that span.
  obtain ⟨p, hpT, hp⟩ := Nat.exists_infinite_primes (T.card + 1)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap (RatFunc k) L RatFunc.X) hp.pos
  have hyint : IsIntegral (Algebra.adjoin k ({algebraMap (RatFunc k) L RatFunc.X} : Set L)) y :=
    IsIntegral.of_pow hp.pos (hy ▸ isIntegral_algebraMap (A := L)
      (x := (⟨_, Algebra.self_mem_adjoin_singleton k _⟩ :
        Algebra.adjoin k ({algebraMap (RatFunc k) L RatFunc.X} : Set L))))
  have hmin : minpoly (RatFunc k) y = X ^ p - C RatFunc.X := by
    refine (minpoly.eq_of_irreducible_of_monic
      (irreducible_X_pow_sub_C_of_prime hp (pow_ne_X k hp)) ?_
      (monic_X_pow_sub_C _ hp.ne_zero)).symm
    simp [hy]
  have hmem : ∀ i : ℕ, y ^ i ∈ Submodule.span (RatFunc k) (T : Set L) := fun i =>
    hspan ⟨y ^ i, Subalgebra.pow_mem _ hyint i⟩
  let g : Fin (minpoly (RatFunc k) y).natDegree → Submodule.span (RatFunc k) (T : Set L) :=
    fun i => ⟨y ^ (i : ℕ), hmem i⟩
  have hg : LinearIndependent (RatFunc k) g :=
    LinearIndependent.of_comp (Submodule.span (RatFunc k) (T : Set L)).subtype
      (linearIndependent_pow y)
  have hle := hg.fintype_card_le_finrank
  rw [Fintype.card_fin, hmin, natDegree_X_pow_sub_C] at hle
  have hT := finrank_span_finset_le_card (R := RatFunc k) T
  have : p ≤ T.card := hle.trans hT
  omega

/-- `X` stays transcendental over `k` in the algebraic closure of `k(X)`. -/
private theorem transcendental_X_algebraicClosure (k : Type*) [Field k] :
    Transcendental k (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) RatFunc.X) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc k) _).injective).mpr
    RatFunc.transcendental_X

/-- Boundary: finite-dimensionality over `k(x)` cannot be dropped. With `k` the algebraic
closure of `ℚ`, `F` the algebraic closure of `k(X)` and `x = X`, the field `k` is
algebraically closed and `x` is transcendental over `k`, yet the integral closure of `k[x]`
in `F` is not a finite `k[x]`-module. -/
example : ¬ ∀ (k F : Type) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (x : F),
    Transcendental k x →
      Module.Finite (Algebra.adjoin k ({x} : Set F))
        (integralClosure (Algebra.adjoin k ({x} : Set F)) F) := fun h =>
  not_finite_integralClosure (h (AlgebraicClosure ℚ)
    (AlgebraicClosure (RatFunc (AlgebraicClosure ℚ))) _ (transcendental_X_algebraicClosure _))

/-- In the boundary model `F` is indeed infinite-dimensional over `k(x)`: otherwise the
theorem would make the integral closure finite. -/
example (k : Type*) [Field k] [IsAlgClosed k] :
    ¬ FiniteDimensional
      (IntermediateField.adjoin k
        ({algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) RatFunc.X} : Set _))
      (AlgebraicClosure (RatFunc k)) := fun hfd =>
  not_finite_integralClosure (Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed _
    (transcendental_X_algebraicClosure k) hfd)

end AdjoinSingletonTest
