/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Triangularization over a splitting field

This file proves that a finite-dimensional endomorphism with split characteristic polynomial has
an upper-triangular matrix in a suitable ordered basis, and derives the corresponding similarity
statement for square matrices.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.TriangularizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open Polynomial

omit [FiniteDimensional K V] in
private theorem triangularization_aeval_mapQ
    (W : Submodule K V) (f : Module.End K V) (hf : W ≤ W.comap f) (p : K[X]) :
    aeval (W.mapQ W f hf) p =
      W.mapQ W (aeval f p)
        (fun _x hx => aeval_apply_smul_mem_of_le_comap hx p f hf) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      apply W.quot_hom_ext
      intro x
      simp only [map_add, LinearMap.add_apply, hp, hq, Submodule.mapQ_apply]
      rfl
  | monomial n a =>
      apply W.quot_hom_ext
      intro x
      simp only [Polynomial.aeval_monomial, Module.algebraMap_end_apply,
        Module.End.mul_apply, Submodule.mapQ_apply]
      rw [← W.mapQ_pow hf n]
      rfl

omit [FiniteDimensional K V] in
private theorem triangularization_minpoly_mapQ_dvd
    (W : Submodule K V) (f : Module.End K V) (hf : W ≤ W.comap f) :
    minpoly K (W.mapQ W f hf) ∣ minpoly K f := by
  apply minpoly.dvd
  rw [triangularization_aeval_mapQ]
  apply W.quot_hom_ext
  intro x
  simp only [Submodule.mapQ_apply, LinearMap.zero_apply]
  rw [minpoly.aeval]
  rfl

private theorem triangularization_exists_eigenvalue_of_minpoly_splits
    [Nontrivial V] (f : Module.End K V) (h : (minpoly K f).Splits) :
    ∃ μ : K, f.HasEigenvalue μ := by
  have hint : IsIntegral K f := LinearMap.isIntegral f
  obtain ⟨μ, hμ⟩ := h.exists_eval_eq_zero (ne_of_gt (minpoly.degree_pos hint))
  exact ⟨μ, Module.End.hasEigenvalue_of_isRoot hμ⟩

private theorem triangularization_exists_basis_fin
    {n : ℕ} (f : Module.End K V) (h : (minpoly K f).Splits)
    (hdim : Module.finrank K V = n) :
    ∃ b : Module.Basis (Fin n) K V,
      (LinearMap.toMatrix b b f).IsUpperTriangular := by
  induction n generalizing V with
  | zero =>
      let b := Module.finBasisOfFinrankEq K V hdim
      refine ⟨b, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      have hfin : 0 < Module.finrank K V := by omega
      let nontrivialV : Nontrivial V := Module.finrank_pos_iff.mp hfin
      obtain ⟨μ, hμ⟩ :=
        @triangularization_exists_eigenvalue_of_minpoly_splits K V _ _ _ _ nontrivialV f h
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hμ
      have hfv : f v = μ • v := Module.End.mem_eigenspace_iff.mp hv
      let W : Submodule K V := K ∙ v
      have hfW : W ≤ W.comap f := by
        change K ∙ v ≤ (K ∙ v).comap f
        rw [Submodule.span_singleton_le_iff_mem]
        change f v ∈ K ∙ v
        rw [hfv]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
      let fQ : Module.End K (V ⧸ W) := W.mapQ W f hfW
      have hQsplit : (minpoly K fQ).Splits := by
        apply h.of_dvd (minpoly.ne_zero (LinearMap.isIntegral f))
        exact triangularization_minpoly_mapQ_dvd W f hfW
      have hWdim : Module.finrank K W = 1 := by
        simpa only [W] using finrank_span_singleton hv0
      have hQdim : Module.finrank K (V ⧸ W) = n := by
        have hrank := W.finrank_quotient_add_finrank
        omega
      obtain ⟨bQ, hbQ⟩ := ih fQ hQsplit hQdim
      let bW : Module.Basis (Fin 1) K W := Module.finBasisOfFinrankEq K W hWdim
      let bS : Module.Basis (Fin 1 ⊕ Fin n) K V := bW.sumQuot bQ
      let e : (Fin 1 ⊕ Fin n) ≃ Fin (n + 1) :=
        finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
      refine ⟨bS.reindex e, ?_⟩
      intro i j hji
      obtain ⟨i | i, rfl⟩ := e.surjective i
      · obtain ⟨j | j, rfl⟩ := e.surjective j
        · have : i = j := Subsingleton.elim _ _
          subst j
          exact (lt_irrefl _ hji).elim
        · change 1 + j.val < i.val at hji
          omega
      · obtain ⟨j | j, rfl⟩ := e.surjective j
        · simp only [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
            Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply]
          dsimp only [bS]
          rw [Module.Basis.sumQuot_inl]
          exact bW.sumQuot_repr_inr_of_mem bQ _ (hfW (bW j).property) i
        · have hji' : j < i := by
            change 1 + j.val < 1 + i.val at hji
            omega
          simp only [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
            Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply]
          dsimp only [bS]
          rw [Module.Basis.sumQuot_repr_inr, Submodule.mkQ_apply]
          have hmap :
              Submodule.Quotient.mk (f ((bW.sumQuot bQ) (Sum.inr j))) =
                fQ (Submodule.Quotient.mk ((bW.sumQuot bQ) (Sum.inr j))) := by
            simpa only [fQ] using
              (Submodule.mapQ_apply W W f ((bW.sumQuot bQ) (Sum.inr j))).symm
          rw [hmap, Module.Basis.sumQuot_inr]
          simpa only [LinearMap.toMatrix_apply] using hbQ hji'

/--
**Triangularization of an endomorphism with split characteristic polynomial.** Let $V$ be a
finite-dimensional vector space over a field $K$, let $f$ be an endomorphism of $V$ whose
characteristic polynomial splits over $K$, and let $\iota$ be a finite linearly ordered set with
exactly $\dim_K V$ elements. Then there is a basis $(b_i)_{i \in \iota}$ of $V$ in which the matrix
of $f$ is upper triangular: its $(i, j)$ entry is $0$ whenever $j < i$.

Proof: induction on dimension. An eigenvector spans an invariant line, the induced map on the
quotient has split minimal polynomial (it divides that of $f$), and a triangularizing basis of the
quotient lifts, together with the eigenvector, to one of $V$. This is the eigenvector-deflation
induction of the proof of Schur's theorem in R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd
ed., Cambridge University Press (2013), Theorem 2.3.1, without unitarity.

Proves `Wanted` entry `exists_basis_upperTriangular_toMatrix`.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
triangularization; S. Axler, Linear Algebra Done Right, 4th ed., Springer (2024), Theorem 5.41.
-/
theorem exists_basis_upperTriangular_toMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (f : Module.End K V) (h : f.charpoly.Splits)
    (hdim : Module.finrank K V = Fintype.card ι) :
    ∃ b : Module.Basis ι K V, (LinearMap.toMatrix b b f).IsUpperTriangular := by
  have hmin : (minpoly K f).Splits :=
    h.of_dvd (LinearMap.charpoly_monic f).ne_zero (LinearMap.minpoly_dvd_charpoly f)
  obtain ⟨b, hb⟩ := triangularization_exists_basis_fin f hmin hdim
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  refine ⟨b.reindex e.toEquiv, ?_⟩
  intro i j hji
  rw [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply]
  rw [← LinearMap.toMatrix_apply]
  exact hb (e.symm.lt_iff_lt.mpr hji)

/--
**Triangularization of a matrix with split characteristic polynomial.** Let $K$ be a field, let
$n$ be a finite linearly ordered index set, and let $A$ be a square matrix over $K$ with rows and
columns indexed by $n$ whose characteristic polynomial splits over $K$. Then there are an
invertible matrix $P$ and a matrix $T$, both over $K$ and indexed by $n$, such that $T$ is upper
triangular ($T_{ij} = 0$ whenever $j < i$) and $A = P T P^{-1}$.

Proof: triangularize the endomorphism of $K^n$ given by $A$ in the standard basis, and conjugate
by the change-of-basis matrix from the standard basis to the triangularizing basis.

Proves `Wanted` entry `exists_upperTriangular_similar_of_splits`.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
triangularization; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University
Press (2013), Theorem 2.3.1.
-/
theorem exists_upperTriangular_similar_of_splits
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix n n K) (h : A.charpoly.Splits) :
    ∃ P T : Matrix n n K, IsUnit P ∧ T.IsUpperTriangular ∧ A = P * T * P⁻¹ := by
  let e : Module.Basis n K (n → K) := Pi.basisFun K n
  let f : Module.End K (n → K) := Matrix.toLin e e A
  have hfchar : f.charpoly.Splits := by
    dsimp only [f]
    rw [Matrix.charpoly_toLin A e]
    exact h
  obtain ⟨b, hb⟩ := exists_basis_upperTriangular_toMatrix (ι := n) f hfchar (by simp)
  let P : Matrix n n K := e.toMatrix b
  let T : Matrix n n K := LinearMap.toMatrix b b f
  have hP : IsUnit P := by
    apply IsUnit.of_mul_eq_one (b.toMatrix e)
    dsimp only [P]
    exact Module.Basis.toMatrix_mul_toMatrix_flip e b
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPinv : b.toMatrix e = P⁻¹ := by
    calc
      b.toMatrix e = b.toMatrix e * 1 := (mul_one _).symm
      _ = b.toMatrix e * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv P hPdet]
      _ = (b.toMatrix e * P) * P⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = P⁻¹ := by
        rw [show b.toMatrix e * P = 1 by
          dsimp only [P]
          exact Module.Basis.toMatrix_mul_toMatrix_flip b e, one_mul]
  have hchange : P * T * b.toMatrix e = A := by
    calc
      P * T * b.toMatrix e = LinearMap.toMatrix e e f := by
        dsimp only [P, T]
        exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b f
      _ = A := by
        dsimp only [f]
        exact LinearMap.toMatrix_toLin e e A
  refine ⟨P, T, hP, ?_, ?_⟩
  · exact hb
  · rw [← hPinv]
    exact hchange.symm

end MathlibExt.LinearAlgebra.TriangularizationWanted
