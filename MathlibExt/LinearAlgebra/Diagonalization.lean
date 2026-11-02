/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Diagonalization over a splitting field

This file proves that a semisimple endomorphism with split characteristic polynomial has an
eigenbasis, and deduces that a matrix with split characteristic polynomial and squarefree minimal
polynomial is similar to a diagonal matrix.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.DiagonalizationWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
private theorem diagonalization_iSup_ker_aeval_eq_ker_prod
    (f : Module.End K V) (s : Finset K) :
    (⨆ μ ∈ s, LinearMap.ker (Polynomial.aeval f (Polynomial.X - Polynomial.C μ))) =
      LinearMap.ker (Polynomial.aeval f (∏ μ ∈ s, (Polynomial.X - Polynomial.C μ))) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, not_false_eq_true, iSup_neg, iSup_bot, Finset.prod_empty, map_one]
    rw [show (1 : Module.End K V) = LinearMap.id from rfl, LinearMap.ker_id]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.iSup_insert, ih]
    apply Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime
    refine IsCoprime.prod_right fun b hb ↦ ?_
    exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id
      (ne_of_mem_of_not_mem hb ha).symm

private theorem diagonalization_roots_nodup_of_squarefree
    (p : Polynomial K) (hp : Squarefree p) : p.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [p.count_roots]
  by_contra h
  have htwo : 2 ≤ p.rootMultiplicity a := by omega
  have hdvd : (Polynomial.X - Polynomial.C a) ^ 2 ∣ p :=
    (Polynomial.le_rootMultiplicity_iff hp.ne_zero).mp htwo
  exact Polynomial.not_isUnit_X_sub_C a (hp _ (by simpa [pow_two] using hdvd))

private theorem diagonalization_iSup_eigenspace_eq_top
    (f : Module.End K V) (hs : f.IsSemisimple) (h : f.charpoly.Splits) :
    ⨆ μ : K, f.eigenspace μ = ⊤ := by
  classical
  let p := minpoly K f
  have hpmonic : p.Monic := minpoly.monic (LinearMap.isIntegral f)
  have hpsplit : p.Splits := h.of_dvd (LinearMap.charpoly_monic f).ne_zero
    (LinearMap.minpoly_dvd_charpoly f)
  have hpnodup : p.roots.Nodup :=
    diagonalization_roots_nodup_of_squarefree p hs.minpoly_squarefree
  have hprod : (∏ μ ∈ p.roots.toFinset, (Polynomial.X - Polynomial.C μ)) = p := by
    rw [← Multiset.toFinset_eq hpnodup, Finset.prod_mk]
    exact (hpsplit.eq_prod_roots_of_monic hpmonic).symm
  have hkernels := diagonalization_iSup_ker_aeval_eq_ker_prod f p.roots.toFinset
  rw [hprod, minpoly.aeval K f, LinearMap.ker_zero] at hkernels
  have heigenspaces : (⨆ μ ∈ p.roots.toFinset, f.eigenspace μ) = ⊤ := by
    simpa only [Module.End.eigenspace_def, Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] using hkernels
  apply top_unique
  calc
    ⊤ = ⨆ μ ∈ p.roots.toFinset, f.eigenspace μ := heigenspaces.symm
    _ ≤ ⨆ μ : K, f.eigenspace μ := iSup_le fun μ ↦ iSup_le fun _ ↦ le_iSup _ μ

private theorem diagonalization_eigenbasis
    {ι : Type*} [Fintype ι]
    (f : Module.End K V) (hs : f.IsSemisimple) (h : f.charpoly.Splits)
    (hdim : Module.finrank K V = Fintype.card ι) :
    ∃ (b : Module.Basis ι K V) (μ : ι → K), ∀ i, f.HasEigenvector (μ i) (b i) := by
  classical
  let hInternal : DirectSum.IsInternal f.eigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Module.End.eigenspaces_iSupIndep f)
      (diagonalization_iSup_eigenspace_eq_top f hs h)
  let v := fun μ : K ↦ Module.Free.chooseBasis K (f.eigenspace μ)
  let b₀ := hInternal.collectedBasis v
  let _ : Finite (Σ μ, Module.Free.ChooseBasisIndex K (f.eigenspace μ)) :=
    Module.Finite.finite_basis b₀
  let _ : Fintype (Σ μ, Module.Free.ChooseBasisIndex K (f.eigenspace μ)) :=
    Fintype.ofFinite _
  let e : (Σ μ, Module.Free.ChooseBasisIndex K (f.eigenspace μ)) ≃ ι :=
    Fintype.equivOfCardEq (by rw [← Module.finrank_eq_card_basis b₀, hdim])
  refine ⟨b₀.reindex e, fun i ↦ (e.symm i).1, fun i ↦ ?_⟩
  rw [Module.End.hasEigenvector_iff, Module.Basis.reindex_apply]
  exact ⟨hInternal.collectedBasis_mem v (e.symm i), b₀.ne_zero _⟩

/--
**Eigenbasis of a semisimple endomorphism with split characteristic polynomial.** Let $V$ be a
finite-dimensional vector space over a field $K$ and let $f$ be a semisimple endomorphism of $V$
(every $f$-invariant subspace has an $f$-invariant complement) whose characteristic polynomial
splits over $K$. Then for every finite type $\iota$ with exactly $\dim_K V$ elements there are a
basis $(b_i)_{i \in \iota}$ of $V$ and scalars $(\mu_i)_{i \in \iota}$ in $K$ such that each $b_i$
is an eigenvector of $f$ with eigenvalue $\mu_i$.

Proof: The minimal polynomial is squarefree and splits, so it is a product of distinct factors
$X - \mu$. The kernels lemma for these factors, proved by induction from the two-factor case,
shows that the eigenspaces span $V$, and bases of the eigenspaces are collected and reindexed.
This is the diagonalizability criterion derived from the kernels lemma in the French Wikipedia
article *Lemme des noyaux*, <https://fr.wikipedia.org/wiki/Lemme_des_noyaux>.

Proves `Wanted` entry `exists_eigenbasis_of_isSemisimple_of_splits`.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
diagonalization; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University
Press (2013), Theorem 1.3.12.
-/
theorem exists_eigenbasis_of_isSemisimple_of_splits
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Module.End K V) (hs : f.IsSemisimple) (h : f.charpoly.Splits)
    (hdim : Module.finrank K V = Fintype.card ι) :
    ∃ (b : Module.Basis ι K V) (μ : ι → K), ∀ i, f.HasEigenvector (μ i) (b i) := by
  exact diagonalization_eigenbasis f hs h hdim

omit [FiniteDimensional K V] in
private theorem diagonalization_toMatrix_eq_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Module.End K V) (b : Module.Basis ι K V) (μ : ι → K)
    (heigen : ∀ i, f.HasEigenvector (μ i) (b i)) :
    LinearMap.toMatrix b b f = Matrix.diagonal μ := by
  ext i j
  rw [LinearMap.toMatrix_apply, (heigen j).apply_eq_smul, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one]
  by_cases hij : i = j
  · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
  · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]

private theorem diagonalization_exists_diagonal_similar
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hsplit : A.charpoly.Splits)
    (hsf : Squarefree (minpoly K (Matrix.toLin' A : Module.End K (n → K)))) :
    ∃ P D : Matrix n n K, D.IsDiag ∧ IsUnit P ∧ A = P * D * P⁻¹ := by
  let f : Module.End K (n → K) := Matrix.toLin' A
  have hsf' : Squarefree (minpoly K f) := by simpa [f] using hsf
  have hfss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsf' (minpoly.aeval K f)
  have hfsplit : f.charpoly.Splits := by simpa [f] using hsplit
  obtain ⟨b, μ, heigen⟩ :=
    diagonalization_eigenbasis f hfss hfsplit (Module.finrank_pi (R := K))
  let e := Pi.basisFun K n
  have hPunit : IsUnit (e.toMatrix b) := by
    let _ := Module.Basis.invertibleToMatrix e b
    exact isUnit_of_invertible _
  refine ⟨e.toMatrix b, Matrix.diagonal μ, Matrix.isDiag_diagonal μ, hPunit, ?_⟩
  rw [Matrix.inv_eq_right_inv (Module.Basis.toMatrix_mul_toMatrix_flip e b)]
  rw [← diagonalization_toMatrix_eq_diagonal f b μ heigen]
  rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  simp [e, f]

/--
**Diagonalizability from a split characteristic polynomial and a squarefree minimal polynomial.**
Let $K$ be a field and let $A$ be a square matrix over $K$ with rows and columns indexed by a
finite type $n$. If the characteristic polynomial of $A$ splits over $K$ and the minimal
polynomial of $A$ (that is, of the linear map $x \mapsto Ax$ on $K^n$) is squarefree, then there
are matrices $P$ and $D$ over $K$ indexed by $n$, with $D$ diagonal and $P$ invertible, such that
$A = P D P^{-1}$.

Proof: A squarefree minimal polynomial makes the linear map $x \mapsto Ax$ semisimple, so it has a
basis of eigenvectors by the eigenbasis theorem for semisimple endomorphisms; conjugating by the
change-of-basis matrix from the standard basis gives the diagonal form.

Proves `Wanted` entry `exists_diagonal_similar_of_splits_of_squarefree_minpoly`.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
diagonalization; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University
Press (2013), Theorem 1.3.12.
-/
theorem exists_diagonal_similar_of_splits_of_squarefree_minpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hsplit : A.charpoly.Splits)
    (hsf : Squarefree (minpoly K (Matrix.toLin' A : Module.End K (n → K)))) :
    ∃ P D : Matrix n n K, D.IsDiag ∧ IsUnit P ∧ A = P * D * P⁻¹ := by
  exact diagonalization_exists_diagonal_similar A hsplit hsf

end MathlibExt.LinearAlgebra.DiagonalizationWanted
