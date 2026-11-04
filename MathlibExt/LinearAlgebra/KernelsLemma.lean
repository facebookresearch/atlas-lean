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

/-- **Kernel of a product of pairwise coprime polynomials.** Let $R$ be a commutative ring, $M$
an $R$-module, $f$ an $R$-linear endomorphism of $M$, and $(p_i)_{i \in \iota}$ a family of
polynomials in $R[X]$ that are pairwise coprime, meaning that for all $i \ne j$ there are
$a, b \in R[X]$ with $a p_i + b p_j = 1$. Then for every finite set $s \subseteq \iota$, the sum
of the submodules $\ker p_i(f)$ over $i \in s$ equals $\ker \bigl(\prod_{i \in s} p_i\bigr)(f)$.
-/
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

/-- **Kernels of pairwise coprime polynomials are independent over a finite set.** Let $R$ be a
commutative ring, $M$ an $R$-module, $f$ an $R$-linear endomorphism of $M$, and
$(p_i)_{i \in \iota}$ a family of polynomials in $R[X]$ that are pairwise coprime, meaning that
for all $i \ne j$ there are $a, b \in R[X]$ with $a p_i + b p_j = 1$. Then for every finite set
$s \subseteq \iota$, every $i \in s$ and every $t \subseteq s$ with $i \notin t$, the submodule
$\ker p_i(f)$ meets the sum of the submodules $\ker p_j(f)$ over $j \in t$ only in $0$. -/
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

/-- **Independence and sum of kernels of pairwise coprime polynomials.** Let $R$ be a commutative
ring, $M$ an $R$-module, $f$ an $R$-linear endomorphism of $M$, and $(p_i)_{i \in \iota}$ a
family of polynomials in $R[X]$, indexed by a finite type $\iota$, that are pairwise coprime,
meaning that for all $i \ne j$ there are $a, b \in R[X]$ with $a p_i + b p_j = 1$. Then the
submodules $\ker p_i(f)$ are independent (each meets the sum of the others only in $0$), and
their sum is $\ker \bigl(\prod_{i \in \iota} p_i\bigr)(f)$. -/
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
**Kernels lemma.** Let $R$ be a commutative ring, $M$ an $R$-module, $f$ an $R$-linear
endomorphism of $M$, and $(p_i)_{i \in \iota}$ a family of polynomials in $R[X]$, indexed by a
finite type $\iota$, that are pairwise coprime, meaning that for all $i \ne j$ there are
$a, b \in R[X]$ with $a p_i + b p_j = 1$. Then the submodules $\ker p_i(f)$ are independent
(each meets the sum of the others only in $0$), and their sum is
$\ker \bigl(\prod_{i \in \iota} p_i\bigr)(f)$.

The decomposition is internal to $\ker \bigl(\prod_{i \in \iota} p_i\bigr)(f)$; it need not span
all of $M$.

Proof: induction on the number of polynomials from the two-polynomial case, as in the cited French
Wikipedia article. For coprime $p$ and $q$ one has $\ker p(f) + \ker q(f) = \ker (pq)(f)$, which
gives the inductive step, and independence follows because $\ker p_i(f) \cap \ker q(f) = 0$ when
$q$ is the product of the other polynomials.

Proves `Wanted` entry `kernels_lemma_pairwise_isCoprime`.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
kernels lemma; https://fr.wikipedia.org/wiki/Lemme_des_noyaux; S. Axler, Linear Algebra Done
Right, 4th ed., Springer (2024), Section 8C.
-/
theorem kernels_lemma_pairwise_isCoprime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Module.End R M) (p : ι → R[X])
    (hcop : Pairwise fun i j => IsCoprime (p i) (p j)) :
    iSupIndep (fun i => LinearMap.ker (aeval f (p i))) ∧
      (⨆ i, LinearMap.ker (aeval f (p i))) = LinearMap.ker (aeval f (∏ i, p i)) := by
  exact iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime f p hcop

end MathlibExt.LinearAlgebra.KernelsLemmaWanted
