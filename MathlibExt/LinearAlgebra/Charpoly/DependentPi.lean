/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import MathlibExt.LinearAlgebra.Charpoly.FiniteFiltration

/-!
# Characteristic polynomial of a dependent componentwise endomorphism

Let R be a commutative ring, I finite, M_i finite free R-modules and f_i:M_i→M_i linear
endomorphisms. The componentwise map f on ∏iM_i has characteristic polynomial χ_f=∏iχ_(f_i) in
R[X]. The component modules may have different ranks, and the empty product has χ=1. For
finite free R-algebras, left multiplication on a product also factors componentwise;
characteristic polynomials of left multiplication are invariant under R-algebra equivalences.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Polynomial

universe uR uI uM uK

namespace LinearMap

variable {R : Type uR} [CommRing R]

/-- **Head-tail linear equivalence of a dependent product.**

Let R be a commutative ring and M_i R-modules for i∈Fin(n+1). The linear equivalence
piFinSuccLinearEquiv sends x to (x_0,(x_(i+1))_(i<n)), identifying ∏i M_i with
M_0×∏_{i<n}M_(i+1).
-/
private def piFinSuccLinearEquiv {n : ℕ} (M : Fin (n + 1) → Type uM)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    (∀ i, M i) ≃ₗ[R] M 0 × (∀ i : Fin n, M (Fin.succ i)) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    ext
    · exact Fin.cons_zero p.1 p.2
    · exact Fin.cons_succ p.1 p.2 _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Head-tail conjugation of a componentwise map.**

For R-modules M_i over a commutative ring and endomorphisms f_i, the head-tail equivalence
over Fin(n+1) conjugates the componentwise map to f_0×(componentwise tail map).
-/
private theorem piFinSuccLinearEquiv_conj_pi {n : ℕ}
    {M : Fin (n + 1) → Type uM} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (f : ∀ i, M i →ₗ[R] M i) :
    (piFinSuccLinearEquiv (R := R) M).conj
        (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
      (f 0).prodMap
        (LinearMap.pi (fun i : Fin n => (f i.succ).comp
          (LinearMap.proj i))) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · rfl
  · funext i
    rfl

/-- **Characteristic polynomial on a finite ordinal product.**

Let R be a commutative ring, I finite, M_i finite free R-modules and f_i:M_i→M_i linear
endomorphisms. The componentwise map f on ∏iM_i has characteristic polynomial χ_f=∏iχ_(f_i) in
R[X]. For I=Fin n, the componentwise map has χ_f=∏_{i<n}χ_(f_i).
-/
private theorem charpoly_pi_dependent_fin {n : ℕ} {M : Fin n → Type uM}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) :
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).charpoly =
      ∏ i, (f i).charpoly := by
  induction n with
  | zero =>
    have : Subsingleton (∀ i, M i) :=
      ⟨fun _ _ => funext fun i => i.elim0⟩
    rw [LinearMap.charpoly_eq_one_of_subsingleton]
    simp
  | succ n ih =>
    calc
      (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).charpoly =
          ((piFinSuccLinearEquiv (R := R) M).conj
            (LinearMap.pi (fun i => (f i).comp
              (LinearMap.proj i)))).charpoly :=
        (LinearEquiv.charpoly_conj _ _).symm
      _ = (f 0).charpoly *
            (LinearMap.pi (fun i : Fin n => (f i.succ).comp
              (LinearMap.proj i))).charpoly := by
        rw [piFinSuccLinearEquiv_conj_pi, LinearMap.charpoly_prodMap]
      _ = (f 0).charpoly * ∏ i : Fin n, (f i.succ).charpoly := by
        rw [ih (fun i => f i.succ)]
      _ = ∏ i, (f i).charpoly := by
        rw [Fin.prod_univ_succ]

variable {ι : Type uI} [Fintype ι]
variable {M : ι → Type uM}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- **Characteristic polynomial of a finite dependent product.**

Let R be a commutative ring, I finite, M_i finite free R-modules and f_i:M_i→M_i linear
endomorphisms. The componentwise map f on ∏iM_i has characteristic polynomial χ_f=∏iχ_(f_i) in
R[X]. This is the identity charpoly_pi_dependent for the componentwise endomorphism.
-/
theorem charpoly_pi_dependent (f : ∀ i, M i →ₗ[R] M i) :
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).charpoly =
      ∏ i, (f i).charpoly := by
  classical
  let e := Fintype.equivFin ι
  have hconj : (LinearEquiv.piCongrLeft' R M e).conj
        (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
      LinearMap.pi (fun j => (f (e.symm j)).comp (LinearMap.proj j)) := by
    apply LinearMap.ext
    intro g
    obtain ⟨x, rfl⟩ := (LinearEquiv.piCongrLeft' R M e).surjective g
    funext j
    simp [e]
  calc
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).charpoly =
        ((LinearEquiv.piCongrLeft' R M e).conj
          (LinearMap.pi (fun i => (f i).comp
            (LinearMap.proj i)))).charpoly :=
      (LinearEquiv.charpoly_conj _ _).symm
    _ = ∏ j, (f (e.symm j)).charpoly := by
      rw [hconj, charpoly_pi_dependent_fin]
    _ = ∏ i, (f i).charpoly :=
      Fintype.prod_equiv e.symm _ _ (fun _ => rfl)

end LinearMap

namespace Algebra

variable {R : Type uR} [CommRing R]
variable {S : Type uM} {T : Type uK} [Ring S] [Ring T]
variable [Algebra R S] [Algebra R T]
variable [Module.Free R S] [Module.Finite R S]
variable [Module.Free R T] [Module.Finite R T]

/-- **Left-multiplication characteristic polynomial under algebra equivalence.**

Let R be a commutative ring, S,T R-algebras finite free over R, e:S≃ₐ[R]T and x∈S. Then
χ_(L_(e(x)) on T)=χ_(L_x on S). The algebras need not be commutative.
-/
theorem lmul_charpoly_eq_of_algEquiv (e : S ≃ₐ[R] T) (x : S) :
    (Algebra.lmul R T (e x)).charpoly =
      (Algebra.lmul R S x).charpoly := by
  rw [← LinearEquiv.charpoly_conj e.toLinearEquiv (Algebra.lmul R S x)]
  congr 1
  ext y
  simp [Algebra.coe_lmul_eq_mul]

variable {ι : Type uI} [Fintype ι] {A : ι → Type uM}
variable [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
variable [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]

/-- **Left-multiplication characteristic polynomial on a dependent product.**

Let R be a commutative ring, I finite and A_i R-algebras finite free over R. For
q=(q_i)∈∏iA_i, χ_(L_q)=∏iχ_(L_(q_i)), with left multiplication on each algebra.
-/
theorem lmul_charpoly_pi_apply (q : ∀ i, A i) :
    (Algebra.lmul R (∀ i, A i) q).charpoly =
      ∏ i, (Algebra.lmul R (A i) (q i)).charpoly := by
  classical
  have hmul : Algebra.lmul R (∀ i, A i) q =
      LinearMap.pi (fun i => (Algebra.lmul R (A i) (q i)).comp
        (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro y
    funext i
    rfl
  rw [hmul, LinearMap.charpoly_pi_dependent]

end Algebra

end
