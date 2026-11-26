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
# Determinants along invariant extensions and finite filtrations

Let R be a commutative ring and M_0,…,M_n finite free modules with invariant endomorphisms f_i
and invariant extensions between adjacent stages. Assume every quotient Q_i is free and write
q_i for its induced endomorphism. The final determinant satisfies
det(f_n)=det(f_0)∏_{i<n}det(q_i). If M_0=0 its determinant factor is1, leaving only the graded
factors.
-/

@[expose] public section

open scoped BigOperators

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- **One invariant extension of module endomorphisms.**

Let R be a commutative ring, V,W R-modules and f:V→V,g:W→W endomorphisms. An invariant
extension E consists of a g-invariant submodule U⊆W and a linear equivalence e:V≃U satisfying
e∘f=(g|U)∘e. These submodule, stability, identification and intertwining data form
InvariantExtension f g.
-/
structure InvariantExtension (f : V →ₗ[R] V) (g : W →ₗ[R] W) where
  /-- **Lower stage inside an invariant extension.**

Let R be a commutative ring, V,W R-modules and f:V→V,g:W→W endomorphisms. An invariant
extension E consists of a g-invariant submodule U⊆W and a linear equivalence e:V≃U satisfying
e∘f=(g|U)∘e. The field submodule is U⊆W, identified with V.
-/
  submodule : Submodule R W
  /-- **Invariant-extension submodule stability.**

Let R be a commutative ring, V,W R-modules and f:V→V,g:W→W endomorphisms. An invariant
extension E consists of a g-invariant submodule U⊆W and a linear equivalence e:V≃U satisfying
e∘f=(g|U)∘e. The field stable is g(U)⊆U.
-/
  stable : submodule ≤ submodule.comap g
  /-- **Identification with the invariant submodule.**

Let R be a commutative ring, V,W R-modules and f:V→V,g:W→W endomorphisms. An invariant
extension E consists of a g-invariant submodule U⊆W and a linear equivalence e:V≃U satisfying
e∘f=(g|U)∘e. The field equiv is e:V≃ₗ[R]U.
-/
  equiv : V ≃ₗ[R] submodule
  /-- **Intertwining of lower and restricted upper endomorphisms.**

Let R be a commutative ring, V,W R-modules and f:V→V,g:W→W endomorphisms. An invariant
extension E consists of a g-invariant submodule U⊆W and a linear equivalence e:V≃U satisfying
e∘f=(g|U)∘e. The field intertwines states e∘f=(g|U)∘e.
-/
  intertwines :
    (equiv : V →ₗ[R] submodule) ∘ₗ f =
      (g.restrict stable) ∘ₗ (equiv : V →ₗ[R] submodule)

namespace InvariantExtension

variable {f : V →ₗ[R] V} {g : W →ₗ[R] W}

/-- **Conjugation identity of an invariant extension.**

Let R be a commutative ring, V,W R-modules and f:V→V,g:W→W endomorphisms. An invariant
extension E consists of a g-invariant submodule U⊆W and a linear equivalence e:V≃U satisfying
e∘f=(g|U)∘e. The endomorphism identity e∘f∘e⁻¹=g|U holds on U.
-/
theorem conjugate_eq (E : InvariantExtension f g) :
    (E.equiv : V →ₗ[R] E.submodule) ∘ₗ f ∘ₗ
        (E.equiv.symm : E.submodule →ₗ[R] V) =
      g.restrict E.stable := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun E.intertwines (E.equiv.symm x)
  simpa using h

/-- **Endomorphism on the quotient of an invariant extension.**

Let R be a commutative ring, V,W R-modules and f:V→V,g:W→W endomorphisms. An invariant
extension E consists of a g-invariant submodule U⊆W and a linear equivalence e:V≃U satisfying
e∘f=(g|U)∘e. The map quotientMap E:W/U→W/U is [x]↦[g(x)].
-/
def quotientMap (E : InvariantExtension f g) :
    (W ⧸ E.submodule) →ₗ[R] (W ⧸ E.submodule) :=
  E.submodule.mapQ E.submodule g E.stable

/-- **Representative value of the invariant-extension quotient map.**

Let R be a commutative ring, V,W R-modules and f:V→V,g:W→W endomorphisms. An invariant
extension E consists of a g-invariant submodule U⊆W and a linear equivalence e:V≃U satisfying
e∘f=(g|U)∘e. For x∈W, quotientMap E ([x])=[g(x)].
-/
@[simp]
theorem quotientMap_mk (E : InvariantExtension f g) (x : W) :
    E.quotientMap (Submodule.Quotient.mk x : W ⧸ E.submodule) =
      (Submodule.Quotient.mk (g x) : W ⧸ E.submodule) := by
  simpa only [quotientMap] using
    (Submodule.mapQ_apply E.submodule E.submodule g (h := E.stable) x)

/-- **Determinant factorization for an invariant extension.**

Let R be a commutative ring, V,W R-modules and f:V→V,g:W→W endomorphisms. An invariant
extension E consists of a g-invariant submodule U⊆W and a linear equivalence e:V≃U satisfying
e∘f=(g|U)∘e. If V is finite free, W finite and W/U free, then det(g)=det(f)det(E.quotientMap).
-/
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

/-- **Determinant product across an invariant finite tower.**

Let R be a commutative ring and M_0,…,M_n finite free modules with invariant endomorphisms f_i
and invariant extensions between adjacent stages. Assume every quotient Q_i is free and write
q_i for its induced endomorphism. Then det(f_n)=det(f_0)∏_{i<n}det(q_i).
-/
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

/-- **Graded determinant product with unit bottom determinant.**

Let R be a commutative ring and M_0,…,M_n finite free modules with invariant endomorphisms f_i
and invariant extensions between adjacent stages. Assume every quotient Q_i is free and write
q_i for its induced endomorphism. If det(f_0)=1, then det(f_n)=∏_{i<n}det(q_i).
-/
theorem det_eq_prod_graded_of_bottom_det_eq_one
    (endomorphism : ∀ i, M i →ₗ[R] M i)
    (step : ∀ i : Fin n,
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ))
    (quotientFree : ∀ i, Module.Free R (M i.succ ⧸ (step i).submodule))
    (hbottom : (endomorphism 0).det = 1) :
    (endomorphism (Fin.last n)).det = ∏ i, (step i).quotientMap.det := by
  rw [det_eq_det_mul_prod_graded endomorphism step quotientFree, hbottom, one_mul]

/-- **Graded determinant product from a zero bottom module.**

Let R be a commutative ring and M_0,…,M_n finite free modules with invariant endomorphisms f_i
and invariant extensions between adjacent stages. Assume every quotient Q_i is free and write
q_i for its induced endomorphism. If M_0=0, then det(f_n)=∏_{i<n}det(q_i).
-/
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
