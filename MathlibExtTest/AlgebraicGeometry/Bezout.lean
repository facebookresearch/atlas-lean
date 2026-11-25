/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.Bezout
import Mathlib.Data.Set.Card

/-! # Tests for Bézout's theorem with multiplicity -/

namespace MathlibExtTest.AlgebraicGeometry.Bezout

open MvPolynomial MathlibExt.AlgebraicGeometry.BezoutWanted.AlgebraicGeometry

variable {K : Type*} [Field K]

/-! ### The local data at a point -/

-- The affine coordinates of a point have entry `1` at its chart index.
example {n : ℕ} (p : ProjSpace K n) : affineConeCoord p (chartIndex p) = 1 :=
  div_self (chartIndex_rep_ne_zero p)

-- The zero polynomial vanishes on all of projective space.
example {n : ℕ} : vanishingSet (0 : MvPolynomial (Fin (n + 1)) K) = Set.univ := by
  ext p
  simp [vanishingSet]

/-- At a common zero of homogeneous polynomials the local quotient is nonzero, so the
intersection multiplicity is at least `1`. -/
theorem one_le_intersectionMultiplicity {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ) (hd : ∀ k, (f k).IsHomogeneous (d k)) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k)) : 1 ≤ intersectionMultiplicity f p := by
  have hp' : ∀ k, eval p.rep (f k) = 0 := by
    simpa [vanishingSet, Set.mem_iInter] using hp
  have hq : affineConeCoord p = (p.rep (chartIndex p))⁻¹ • p.rep := by
    funext j
    simp [affineConeCoord, div_eq_inv_mul]
  have hmem : ∀ g, eval (affineConeCoord p) g = 0 →
      algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt (affineConeCoord p)) g ∈
        IsLocalRing.maximalIdeal (localRingAt (affineConeCoord p)) := by
    intro g hg
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (maxIdealAt (affineConeCoord p))]
    simpa [maxIdealAt, evalAt, RingHom.mem_ker] using hg
  simp only [intersectionMultiplicity]
  rw [Order.one_le_iff_pos, Module.length_pos_iff]
  apply Ideal.Quotient.nontrivial_iff.mpr
  refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top ?_
  rw [Ideal.span_le]
  rintro _ (⟨k, rfl⟩ | h)
  · apply hmem
    rw [hq, (hd k).eval_smul, hp' k, mul_zero]
  · rw [Set.mem_singleton_iff] at h
    rw [h]
    apply hmem
    simp [affineConeCoord, div_self (chartIndex_rep_ne_zero p)]

/-! ### Applying Bézout's theorem -/

/-- **Bézout's bound.** `n` homogeneous polynomials of degrees `d_k ≥ 1` in `n + 1` variables over
an algebraically closed field with finitely many common projective zeros have at most `∏ d_k`
common zeros: every multiplicity in Bézout's sum is at least `1`. -/
theorem ncard_le_prod [IsAlgClosed K] {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ) (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hdeg : ∀ k, (f k).totalDegree = d k) (hd_pos : ∀ k, 1 ≤ d k)
    (hfin : (⋂ k, vanishingSet (f k)).Finite) :
    (⋂ k, vanishingSet (f k)).ncard ≤ ∏ k, d k := by
  have h := bezout_multiplicity f d hd hdeg hd_pos hfin
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h
  have hle : (((⋂ k, vanishingSet (f k)).ncard : ℕ) : ℕ∞) ≤ ((∏ k, d k : ℕ) : ℕ∞) := by
    rw [Set.ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_prod,
      ← h]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Nat.cast_one]
    exact one_le_intersectionMultiplicity f d hd p (hfin.mem_toFinset.mp hp)
  exact_mod_cast hle

/-- The projective space `ℙ⁰(K)` has a single point. -/
theorem projSpace_zero_subsingleton : Subsingleton (ProjSpace K 0) := by
  constructor
  intro p q
  induction p using Projectivization.ind with | h v hv => ?_
  induction q using Projectivization.ind with | h w hw => ?_
  have hj : ∀ j : Fin 1, j = 0 := fun j => Fin.fin_one_eq_zero j
  have hv0 : v 0 ≠ 0 := fun h => hv (funext fun j => by rw [hj j, h]; rfl)
  have hw0 : w 0 ≠ 0 := fun h => hw (funext fun j => by rw [hj j, h]; rfl)
  refine (Projectivization.mk_eq_mk_iff' K v w hv hw).mpr ⟨v 0 / w 0, funext fun j => ?_⟩
  rw [hj j, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hw0]

/-- For `n = 0` there are no polynomials, the common zero set is the single point of `ℙ⁰(K)`, and
Bézout's theorem says that its intersection multiplicity is the empty product `1`. -/
theorem intersectionMultiplicity_projSpace_zero [IsAlgClosed K] (p : ProjSpace K 0) :
    intersectionMultiplicity (![] : Fin 0 → MvPolynomial (Fin 1) K) p = 1 := by
  have := projSpace_zero_subsingleton (K := K)
  have h := bezout_multiplicity (![] : Fin 0 → MvPolynomial (Fin 1) K) ![]
    (fun k => k.elim0) (fun k => k.elim0) (fun k => k.elim0) (Set.toFinite _)
  rw [Set.iInter_of_empty, Finset.univ_eq_empty, Finset.prod_empty,
    show (Set.univ : Set (ProjSpace K 0)) = {p} from
      Set.eq_singleton_iff_unique_mem.mpr ⟨Set.mem_univ _, fun q _ => Subsingleton.elim q p⟩,
    finsum_mem_singleton] at h
  exact h

end MathlibExtTest.AlgebraicGeometry.Bezout
