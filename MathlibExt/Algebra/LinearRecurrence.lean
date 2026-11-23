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
# Closed forms for linear recurrences with distinct characteristic roots

Over any field, a linear recurrence of order `d` with `d` distinct characteristic roots has
exactly one expression for each solution as a linear combination of their geometric sequences.
The order may be zero, and one of the roots may be zero. No characteristic assumption is needed.

This is a distinct-root theorem only; it makes no completeness claim for repeated roots.
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
