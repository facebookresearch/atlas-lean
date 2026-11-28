/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.ReducedTraceSets

/-!
# Tests for the reduced-trace sets $S_{a,b}$ and reduced characteristic polynomials
-/

set_option autoImplicit false

@[expose] public section

open scoped Quaternion

open Polynomial QuaternionAlgebra

namespace ReducedTraceSetsTest

/-- $2 \in S_{a,b}$: the element $1$ has reduced norm $1$ and reduced trace $2$. -/
example (a b : ℚ) : (2 : ℚ) ∈ reducedTraceSet ℚ a b :=
  ⟨1, 0, 0, 0, by ring, by ring⟩

/-- So $-2 \in S_{a,b}$ too. -/
example (a b : ℚ) : (-2 : ℚ) ∈ reducedTraceSet ℚ a b :=
  neg_mem_reducedTraceSet_iff.2 ⟨1, 0, 0, 0, by ring, by ring⟩

/-- $0 \in S_{-1,-1}$: $i$ has reduced norm $(-(-1)) \cdot 1 = 1$ and reduced trace $0$. -/
example : (0 : ℚ) ∈ reducedTraceSet ℚ (-1) (-1) :=
  ⟨0, 1, 0, 0, by norm_num, by norm_num⟩

/-- $i \in H_{-1,-1}$ is a root of its reduced characteristic polynomial $x^2 + 1$. -/
example : (⟨0, 1, 0, 0⟩ : ℍ[ℚ,-1,-1]) ^ 2 + 1 = 0 := by
  have h := sq_sub_two_mul_re_mul_add_normForm (⟨0, 1, 0, 0⟩ : ℍ[ℚ,-1,-1])
  norm_num at h
  exact h

/-- The reduced characteristic polynomial of $i \in H_{-1,-1}$ is the only monic quadratic
vanishing at $i$. -/
example {g : ℚ[X]} (hg : g.Monic) (hdeg : g.natDegree = 2)
    (h : aeval (⟨0, 1, 0, 0⟩ : ℍ[ℚ,-1,-1]) g = 0) : g = X ^ 2 + 1 := by
  have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ,-1,-1]) ∉ Set.range (algebraMap ℚ ℍ[ℚ,-1,-1]) := by
    rintro ⟨k, hk⟩
    have := congrArg QuaternionAlgebra.imI hk
    simp at this
  rw [eq_reducedCharpoly_of_aeval_eq_zero hi hg hdeg h]
  norm_num

/-- $0 \in S_{-1,-1}$ by reduced characteristic polynomials: $x^2 + 1$ is that of $i$. -/
example : (0 : ℚ) ∈ reducedTraceSet ℚ (-1) (-1) :=
  mem_reducedTraceSet_iff_exists_reducedCharpoly.2 ⟨⟨0, 1, 0, 0⟩, by norm_num⟩

/-- For $b \ne 0$, $H_{1,b} \otimes \mathbb{Q}_p$ is split, so
$S_{1,b}(\mathbb{Q}_p) = \mathbb{Q}_p$. -/
example (p : ℕ) [Fact p.Prime] (b : ℚ) (hb : b ≠ 0) :
    reducedTraceSet ℚ_[p] ((1 : ℚ) : ℚ_[p]) (b : ℚ_[p]) = Set.univ := by
  apply Rat.reducedTraceSet_padic_eq_univ_of_not_mem_quaternionRamifiedPrimes
  intro hp
  obtain ⟨φ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero ℚ_[p] two_ne_zero
    ((1 : ℚ) : ℚ_[p]) (b : ℚ_[p]) (by simp) (by exact_mod_cast hb) 1 1 0 0 (by simp) (by simp)
  exact hp.false φ

/-- In the split algebra $H_{1,1}$ over $\mathbb{Q}$, the monic quadratic $x^2 - 5x + 7$ is a
reduced characteristic polynomial. -/
example : ∃ α : ℍ[ℚ,1,1], (X ^ 2 - C 5 * X + C 7 : ℚ[X]) = X ^ 2 - C (2 * α.re) * X +
    C (α.re ^ 2 - 1 * α.imI ^ 2 - 1 * α.imJ ^ 2 + 1 * 1 * α.imK ^ 2) :=
  exists_reducedCharpoly_eq_of_nonempty_algEquiv
    (QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero ℚ two_ne_zero 1 1 one_ne_zero
      one_ne_zero 1 1 0 0 (by simp) (by norm_num))
    (by monicity!) (by compute_degree!)

#check @QuaternionAlgebra.reducedTraceSet
#check @QuaternionAlgebra.neg_mem_reducedTraceSet_iff
#check @QuaternionAlgebra.sq_sub_two_mul_re_mul_add_normForm
#check @QuaternionAlgebra.eq_reducedCharpoly_of_aeval_eq_zero
#check @QuaternionAlgebra.mem_reducedTraceSet_iff_exists_reducedCharpoly
#check @QuaternionAlgebra.exists_reducedCharpoly_eq_of_nonempty_algEquiv
#check @QuaternionAlgebra.reducedTraceSet_eq_univ_of_nonempty_algEquiv
#check @Rat.exists_reducedCharpoly_eq_of_not_mem_quaternionRamifiedPrimes
#check @Rat.reducedTraceSet_padic_eq_univ_of_not_mem_quaternionRamifiedPrimes

end ReducedTraceSetsTest
