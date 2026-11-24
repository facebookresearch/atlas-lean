/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants along finite invariant filtrations

This file packages and iterates the determinant factorization for an
endomorphism preserving a submodule.  It is intended for finite filtrations
whose stages and successive quotients are finite free modules.

## Main declarations

* `LinearMap.InvariantExtension` records one inclusion of a filtration stage
  as an invariant submodule of the next stage.
* `LinearMap.InvariantExtension.quotientMap` is the induced endomorphism on
  the successive quotient.
* `LinearMap.InvariantExtension.det_eq_det_mul_det_quotientMap` is the
  one-step determinant factorization.
* `LinearMap.det_eq_det_mul_prod_graded` iterates the factorization through a
  finite tower.
* `LinearMap.det_eq_prod_graded_of_bottom_subsingleton` removes the bottom
  determinant when the initial stage is zero.

## Informal proof

For one step, let `f` act on the lower stage `V`, let `g` act on the next
stage `W`, and identify `V` with a `g`-invariant submodule `S` of `W`.
Mathlib's `LinearMap.det_eq_det_mul_det` chooses a basis of `S`, extends it by
a basis of `W/S`, and writes the matrix of `g` in block upper-triangular
form.  It gives

`det(g) = det(g|S) * det(g on W/S)`.

The stored intertwining equality says that `g|S` is conjugate to `f` through
the identification `V ~= S`.  Determinants are invariant under conjugation,
so the first factor is `det(f)`.

For a finite tower, apply this one-step identity at every adjacent pair.  A
plain induction over `Fin n` multiplies the successive quotient determinants:
if `d_(i+1) = d_i * q_i`, then

`d_n = d_0 * product_i q_i`.

When the bottom stage is a zero module, its determinant is one, leaving only
the product over the graded quotients.

The freeness of every successive quotient is explicit.  Over an arbitrary
commutative ring it does not follow merely from freeness of the two adjacent
stages; this hypothesis is therefore not hidden or weakened.
-/

@[expose] public section

open scoped BigOperators

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- One step of an invariant filtration.

The lower endomorphism `f` is identified with the restriction of the upper
endomorphism `g` to `submodule`.  The quotient endomorphism is consequently
the action of `g` on the corresponding successive graded piece. -/
structure InvariantExtension (f : V →ₗ[R] V) (g : W →ₗ[R] W) where
  /-- The lower filtration stage inside the next stage. -/
  submodule : Submodule R W
  /-- The next-stage endomorphism preserves the lower stage. -/
  stable : submodule ≤ submodule.comap g
  /-- Identification of the abstract lower stage with the invariant
  submodule. -/
  equiv : V ≃ₗ[R] submodule
  /-- Under `equiv`, the lower endomorphism intertwines with the restriction
  of the upper endomorphism. -/
  intertwines :
    (equiv : V →ₗ[R] submodule) ∘ₗ f =
      (g.restrict stable) ∘ₗ (equiv : V →ₗ[R] submodule)

namespace InvariantExtension

variable {f : V →ₗ[R] V} {g : W →ₗ[R] W}

/-- The intertwining square in an invariant extension, rewritten as a
conjugation identity. -/
theorem conjugate_eq (E : InvariantExtension f g) :
    (E.equiv : V →ₗ[R] E.submodule) ∘ₗ f ∘ₗ
        (E.equiv.symm : E.submodule →ₗ[R] V) =
      g.restrict E.stable := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun E.intertwines (E.equiv.symm x)
  simpa using h

/-- The endomorphism induced on the successive quotient of an invariant
extension. -/
def quotientMap (E : InvariantExtension f g) :
    (W ⧸ E.submodule) →ₗ[R] (W ⧸ E.submodule) :=
  E.submodule.mapQ E.submodule g E.stable

/-- The quotient endomorphism sends the class of a representative to the
class of its image under the upper-stage endomorphism. -/
@[simp]
theorem quotientMap_mk (E : InvariantExtension f g) (x : W) :
    E.quotientMap (Submodule.Quotient.mk x : W ⧸ E.submodule) =
      (Submodule.Quotient.mk (g x) : W ⧸ E.submodule) := by
  simpa only [quotientMap] using
    (Submodule.mapQ_apply E.submodule E.submodule g (h := E.stable) x)

/-- Determinant factorization for one invariant extension.

This is the reusable one-step block-triangular formula.  The lower stage and
the quotient are required to be finite free in exactly the places needed by
`LinearMap.det_eq_det_mul_det`. -/
theorem det_eq_det_mul_det_quotientMap (E : InvariantExtension f g)
    [Module.Free R V] [Module.Finite R V] [Module.Finite R W]
    [Module.Free R (W ⧸ E.submodule)] :
    g.det = f.det * E.quotientMap.det := by
  let _ : Module.Free R E.submodule := Module.Free.of_equiv E.equiv
  let _ : Module.Finite R E.submodule := Module.Finite.equiv E.equiv
  calc
    g.det = (g.restrict E.stable).det * E.quotientMap.det :=
      g.det_eq_det_mul_det E.submodule E.stable
    _ = f.det * E.quotientMap.det := by
      rw [← E.conjugate_eq, LinearMap.det_conj]

end InvariantExtension

private theorem last_eq_first_mul_prod {n : ℕ} (d : Fin (n + 1) → R)
    (q : Fin n → R) (h : ∀ i, d i.succ = d i.castSucc * q i) :
    d (Fin.last n) = d 0 * ∏ i, q i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprefix :
          d (Fin.castSucc (Fin.last n)) =
            d 0 * ∏ i : Fin n, q i.castSucc := by
        apply ih (d := fun i ↦ d i.castSucc) (q := fun i ↦ q i.castSucc)
        intro i
        simpa using h i.castSucc
      calc
        d (Fin.last (n + 1)) =
            d (Fin.castSucc (Fin.last n)) * q (Fin.last n) := by
          simpa using h (Fin.last n)
        _ = (d 0 * ∏ i : Fin n, q i.castSucc) * q (Fin.last n) := by
          rw [hprefix]
        _ = d 0 * ((∏ i : Fin n, q i.castSucc) * q (Fin.last n)) := by
          rw [mul_assoc]
        _ = d 0 * ∏ i, q i := by
          rw [Fin.prod_univ_castSucc]

section FiniteTower

variable {n : ℕ} {M : Fin (n + 1) → Type v}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- The determinant on the final stage of a finite invariant filtration is
the determinant on the initial stage times the product of the determinants
on all successive graded quotients.

The stages may be presented as different module types.  Each `step i`
identifies stage `i` with an invariant submodule of stage `i+1`; this avoids
choosing coercion-heavy nested subtypes and makes the theorem convenient for
filtrations transported through canonical linear equivalences. -/
theorem det_eq_det_mul_prod_graded (endomorphism : ∀ i, M i →ₗ[R] M i)
    (step : ∀ i : Fin n,
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ))
    (quotientFree : ∀ i, Module.Free R (M i.succ ⧸ (step i).submodule)) :
    (endomorphism (Fin.last n)).det =
      (endomorphism 0).det * ∏ i, (step i).quotientMap.det := by
  refine last_eq_first_mul_prod
    (d := fun i ↦ (endomorphism i).det)
    (q := fun i ↦ (step i).quotientMap.det) ?_
  intro i
  let _ : Module.Free R (M i.succ ⧸ (step i).submodule) := quotientFree i
  exact (step i).det_eq_det_mul_det_quotientMap

/-- Version of `LinearMap.det_eq_det_mul_prod_graded` for a filtration whose
bottom determinant has already been identified with one. -/
theorem det_eq_prod_graded_of_bottom_det_eq_one
    (endomorphism : ∀ i, M i →ₗ[R] M i)
    (step : ∀ i : Fin n,
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ))
    (quotientFree : ∀ i, Module.Free R (M i.succ ⧸ (step i).submodule))
    (hbottom : (endomorphism 0).det = 1) :
    (endomorphism (Fin.last n)).det = ∏ i, (step i).quotientMap.det := by
  rw [det_eq_det_mul_prod_graded endomorphism step quotientFree, hbottom, one_mul]

/-- Determinant product formula for a finite invariant filtration starting
at a zero module. -/
theorem det_eq_prod_graded_of_bottom_subsingleton
    (endomorphism : ∀ i, M i →ₗ[R] M i)
    (step : ∀ i : Fin n,
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ))
    (quotientFree : ∀ i, Module.Free R (M i.succ ⧸ (step i).submodule))
    [Subsingleton (M 0)] :
    (endomorphism (Fin.last n)).det = ∏ i, (step i).quotientMap.det :=
  det_eq_prod_graded_of_bottom_det_eq_one endomorphism step quotientFree
    (LinearMap.det_eq_one_of_subsingleton _)

end FiniteTower

end LinearMap
