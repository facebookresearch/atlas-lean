/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Kernels lemma

This file proves the finite-family kernels lemma for pairwise coprime polynomials evaluated at a
module endomorphism.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace MathlibExt.LinearAlgebra.KernelsLemmaWanted

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The supremum of the kernels over a finite set is the kernel of the polynomial product. -/
theorem iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime {ι : Type*}
    (f : Module.End R M) (p : ι → R[X])
    (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) (s : Finset ι) :
    (⨆ i ∈ s, LinearMap.ker (aeval f (p i))) =
      LinearMap.ker (aeval f (∏ i ∈ s, p i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext x
      simp [LinearMap.mem_ker]
  | @insert a s ha ih =>
      have hcop_prod : IsCoprime (p a) (∏ i ∈ s, p i) := by
        apply IsCoprime.prod_right
        intro i hi
        exact hcop (ne_of_mem_of_not_mem hi ha).symm
      rw [Finset.prod_insert ha, Finset.iSup_insert,
        ← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop_prod, ← ih]

/-- Kernels of a finite set of pairwise coprime polynomials are supremum-independent. -/
theorem supIndep_ker_aeval_of_pairwise_isCoprime {ι : Type*}
    (f : Module.End R M) (p : ι → R[X])
    (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) (s : Finset ι) :
    s.SupIndep fun i => LinearMap.ker (aeval f (p i)) := by
  classical
  intro t _ i _ hit
  rw [Finset.sup_eq_iSup,
    iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime f p hcop t]
  apply Polynomial.disjoint_ker_aeval_of_isCoprime f
  apply IsCoprime.prod_right
  intro j hj
  exact hcop (ne_of_mem_of_not_mem hj hit).symm

/-- Pairwise coprime polynomial kernels form an independent family whose supremum is the kernel
of their product. -/
theorem iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime {ι : Type*} [Fintype ι]
    (f : Module.End R M) (p : ι → R[X])
    (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
    iSupIndep (fun i => LinearMap.ker (aeval f (p i))) ∧
      (⨆ i, LinearMap.ker (aeval f (p i))) = LinearMap.ker (aeval f (∏ i, p i)) := by
  classical
  constructor
  · apply iSupIndep_iff_supIndep_univ.mpr
    exact supIndep_ker_aeval_of_pairwise_isCoprime f p hcop Finset.univ
  · simpa using
      iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime f p hcop Finset.univ

/--
Kernels lemma, finite-family version (primary decomposition machinery): for pairwise coprime
polynomials, the individual kernels are independent and their supremum is the kernel of the
product. The decomposition is internal to the product kernel; it need not span all of `M`.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
kernels lemma; https://fr.wikipedia.org/wiki/Lemme_des_noyaux; S. Axler, Linear Algebra Done
Right, 4th ed., Springer (2024), Section 8C.

Proves `Wanted` entry `kernels_lemma_pairwise_isCoprime`.

Proof: induction on the number of polynomials from the two-polynomial case, as in the cited French
Wikipedia article. Mathlib's `Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime` is the
two-polynomial step, and independence follows from `Polynomial.disjoint_ker_aeval_of_isCoprime`
applied to each polynomial and the product of the others.
-/
theorem kernels_lemma_pairwise_isCoprime {ι : Type*} [Fintype ι]
    (f : Module.End R M) (p : ι → R[X])
    (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
    iSupIndep (fun i => LinearMap.ker (aeval f (p i))) ∧
      (⨆ i, LinearMap.ker (aeval f (p i))) = LinearMap.ker (aeval f (∏ i, p i)) := by
  exact iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime f p hcop

end MathlibExt.LinearAlgebra.KernelsLemmaWanted
