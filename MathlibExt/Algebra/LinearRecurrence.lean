/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.LinearRecurrence
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Linear recurrences: closed forms and annihilators

Over any field, a linear recurrence of order `d` with `d` distinct characteristic roots has
exactly one expression for each solution as a linear combination of their geometric sequences.
The order may be zero, and one of the roots may be zero. No characteristic assumption is needed.
The closed form makes no completeness claim for repeated roots.

For any linear recurrence over a field, its characteristic polynomial annihilates its solutions
when applied as a polynomial in the shift operator.
-/

@[expose] public section

namespace LinearRecurrence

/-- Linear combinations of geometric sequences at roots of the characteristic polynomial are
solutions. -/
theorem isSolution_sum_mul_pow {R : Type*} [CommRing R] (E : LinearRecurrence R) {ι : Type*}
    (s : Finset ι) (c r : ι → R) (hroot : ∀ i ∈ s, E.charPoly.IsRoot (r i)) :
    E.IsSolution fun n ↦ ∑ i ∈ s, c i * r i ^ n := by
  apply (E.is_sol_iff_mem_solSpace _).2
  have hsum : (fun n ↦ ∑ i ∈ s, c i * r i ^ n) =
      ∑ i ∈ s, c i • (fun n : ℕ ↦ r i ^ n) := by
    ext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  exact E.solSpace.sum_mem fun i hi ↦ E.solSpace.smul_mem _
    ((E.is_sol_iff_mem_solSpace _).1 ((E.geom_sol_iff_root_charPoly _).2 (hroot i hi)))

/-- Over a field, if the characteristic polynomial has `E.order` pairwise distinct roots, every
solution is a unique linear combination of the corresponding geometric sequences. -/
theorem exists_unique_eq_sum_pow_of_injective {K : Type*} [Field K] (E : LinearRecurrence K)
    {r : Fin E.order → K} (hr : Function.Injective r) (hroot : ∀ i, E.charPoly.IsRoot (r i))
    {u : ℕ → K} (hu : E.IsSolution u) :
    ∃! c : Fin E.order → K, ∀ n, u n = ∑ i, c i * r i ^ n := by
  have hunit : IsUnit (Matrix.vandermonde r) :=
    (Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hr))
  -- Row-vector multiplication lists the geometric sum's first `E.order` values.
  obtain ⟨c, hc⟩ := (Matrix.vecMul_surjective_iff_isUnit.2 hunit)
    (fun i : Fin E.order ↦ u i)
  have hsol : E.IsSolution (fun n ↦ ∑ i, c i * r i ^ n) :=
    E.isSolution_sum_mul_pow Finset.univ c r (fun i _ ↦ hroot i)
  have heq : u = (fun n ↦ ∑ i, c i * r i ^ n) := by
    apply (E.eq_iff_eqOn_range_order _ _ hu hsol).2
    intro n hn
    have hinit : (∑ i, c i * r i ^ n) = u n :=
      congrFun hc ⟨n, Finset.mem_range.mp hn⟩
    exact hinit.symm
  refine ⟨c, fun n ↦ congrFun heq n, ?_⟩
  intro d hd
  apply Matrix.vecMul_injective_iff_isUnit.2 hunit
  funext n
  change (∑ i, d i * r i ^ (n : ℕ)) = ∑ i, c i * r i ^ (n : ℕ)
  exact (hd n).symm.trans (congrFun heq n)

end LinearRecurrence

/-! ## Annihilators of recurrence solutions -/

namespace MetaMathlibExt

open Polynomial

/-- **Annihilator of a sequence.** Let $K$ be a semiring, $p = \sum_i a_i X^i \in K[X]$ and
$G \colon \mathbb{N} \to K$ a sequence, and let $E$ be the translation operator
$E(G_s) = G_{s+1}$. The operator $p(E)$ annihilates $G$ when $\sum_i a_i G_{s+i} = 0$ for every
$s \ge 0$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 3 (definitions of the translation operator and of an annihilator). -/
def AnnihilatesSeq {K : Type*} [Semiring K] (p : K[X]) (G : ℕ → K) : Prop :=
  ∀ s : ℕ, p.sum (fun i a => a * G (s + i)) = 0

/-- **Every operator annihilates the zero sequence.** For every semiring $K$ and every polynomial
$p \in K[X]$, the operator $p(E)$ annihilates the zero sequence, where $E$ is the translation
operator $E(G_s) = G_{s+1}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 3 (definition of an annihilator). -/
theorem annihilatesSeq_zero {K : Type*} [Semiring K] (p : K[X]) : AnnihilatesSeq p (0 : ℕ → K) := by
  intro s
  simp [Polynomial.sum]

/-- **The characteristic polynomial annihilates the solutions of its recurrence.** Let $K$ be a
field, $d \ge 0$ and $a_0, \dots, a_{d-1} \in K$. If a sequence $G \colon \mathbb{N} \to K$
satisfies $G_{n+d} = \sum_{i=0}^{d-1} a_i G_{n+i}$ for every $n \ge 0$, then the characteristic
polynomial $X^d - \sum_{i=0}^{d-1} a_i X^i$ of this recurrence annihilates $G$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.4 (`fq-2024-hendel08232024rev2-lem-3.4`). -/
theorem annihilatesSeq_charPoly_of_isSolution {K : Type*} [Field K]
    (E : LinearRecurrence K) (G : ℕ → K) (hG : E.IsSolution G) :
    AnnihilatesSeq E.charPoly G := by
  intro s
  let evalShift : K[X] →ₗ[K] K :=
    (Finsupp.linearCombination K (fun i : ℕ => G (s + i))).comp
      (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap
  change evalShift E.charPoly = 0
  have hmonomial (i : ℕ) (a : K) : evalShift (monomial i a) = a * G (s + i) :=
    Finsupp.linearCombination_single K a i
  rw [LinearRecurrence.charPoly, map_sub, map_sum]
  simpa only [hmonomial, one_mul, sub_eq_zero] using hG s

end MetaMathlibExt
