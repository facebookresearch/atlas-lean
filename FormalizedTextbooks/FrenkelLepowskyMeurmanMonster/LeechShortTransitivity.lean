/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityOctad
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! Constructive transitivity on actual norm-four Leech vectors and short labels.
Only the proved Golay permutation/sign action and the actual ξ matrix are used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An even vector of square sum 32 has a zero coordinate. -/
theorem leechShort_even_zero (u : Fin 24 → ℤ) (hs : leechSquareSum u = 32)
    (heven : ∀ i, Even (u i)) : ∃ i, u i = 0 := by
  by_contra! hn
  have hl (i : Fin 24) : 4 ≤ u i ^ 2 := by
    obtain ⟨k, hk⟩ := heven i
    have hb : u i ≤ -2 ∨ 2 ≤ u i := by have h := hn i; omega
    rcases hb with hb | hb <;> nlinarith [sq_nonneg (u i + 2), sq_nonneg (u i - 2)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
  change (∑ _ : Fin 24, (4 : ℤ)) ≤ leechSquareSum u at hh
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  omega

/-- A zero coordinate reduces the actual short vector through its even pair/octad shape. -/
theorem leechShort_reduction_of_zero (u : leechIntegral) (hs : leechSquareSum u.val = 32)
    (z : Fin 24) (hz : u.val z = 0) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  rcases leechShort_even_shapes u hs z hz with ⟨i, j, hij, hi, hj⟩ | ⟨c, hc, hw, hcoord⟩
  · exact leechShort_pair_reduction u hs i j hij hi hj
  · exact leechShort_octad_reduction u hs c hc hw hcoord

/-- The actual ξ action makes a normalized odd short vector even. -/
theorem leechShort_odd_reduction (u : leechIntegral) (hs : leechSquareSum u.val = 32)
    (ho : ∀ i, Odd (u.val i)) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  obtain ⟨e, he, hrow⟩ := leechShort_odd_preparation u hs ho
  let w := leechIntegralAction e u
  let x := leechIntegralAction co1XiIsometry w
  have h0 : w.val 0 = 3 := hrow 0
  have h1 : w.val 1 = 1 := hrow 1
  have h2 : w.val 2 = 1 := hrow 2
  have h3 : w.val 3 = 1 := hrow 3
  have hx0 : x.val 0 = 0 := by
    have hh := congrFun (co1Xi_integral_double w) 0
    rw [(co1Xi_first_four_numerator w.val).1, h0, h1, h2, h3] at hh
    change 2 * x.val 0 = -3 + 1 + 1 + 1 at hh
    omega
  have hxs : leechSquareSum x.val = 32 := by
    dsimp [x, w]
    rw [leechIntegralAction_squareSum, leechIntegralAction_squareSum, hs]
  obtain ⟨f, hf, hpair⟩ := leechShort_reduction_of_zero x hxs 0 hx0
  refine ⟨f * co1XiIsometry * e,
    leechConcreteGeneratorSubgroup.mul_mem
      (leechConcreteGeneratorSubgroup.mul_mem hf co1XiIsometry_mem_concrete) he, ?_⟩
  simpa only [map_mul, LinearEquiv.mul_apply] using hpair

/-- Every actual norm-four lattice vector is sent to the positive pair vector
by an element of the concrete Golay and ξ generator subgroup. -/
theorem leechShort_concrete_transitive (u : leechIntegral)
    (hs : leechSquareSum u.val = 32) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  obtain ⟨m, hm, c, _, hr, _⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  rcases hm with hm | hm <;> subst m
  · have heven (i : Fin 24) : Even (u.val i) := by
      have hd := leechResidue_dvd u.val 0 c hr i
      obtain ⟨k, hk⟩ := hd
      exact ⟨(c i).val + 2 * k, by omega⟩
    obtain ⟨z, hz⟩ := leechShort_even_zero u.val hs heven
    exact leechShort_reduction_of_zero u hs z hz
  · have ho (i : Fin 24) : Odd (u.val i) := by
      have hd := leechResidue_dvd u.val 1 c hr i
      obtain ⟨k, hk⟩ := hd
      exact ⟨(c i).val + 2 * k, by omega⟩
    exact leechShort_odd_reduction u hs ho

/-- Actual short representatives lie in one orbit of the concrete generators,
as signed real vectors. -/
theorem leechShort_concrete_vector_transitive (r s : GriessShortIndex) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      e.val (griessShortVector r) = griessShortVector s := by
  obtain ⟨a, ha, har⟩ := leechShort_concrete_transitive (griessShortLatticeVector r)
    (griessShortIntegral_squareSum r)
  obtain ⟨b, hb, hbs⟩ := leechShort_concrete_transitive (griessShortLatticeVector s)
    (griessShortIntegral_squareSum s)
  have hv : leechIntegralAction a (griessShortLatticeVector r) =
      leechIntegralAction b (griessShortLatticeVector s) := Subtype.ext (har.trans hbs.symm)
  have he : a.val (griessShortVector r) = b.val (griessShortVector s) := by
    have h := congrArg (fun u : leechIntegral => leechCoordinateEmbedding u.val) hv
    change leechCoordinateEmbedding (leechIntegralAction a (griessShortLatticeVector r)).val =
      leechCoordinateEmbedding (leechIntegralAction b (griessShortLatticeVector s)).val at h
    rw [leechIntegralAction_embedding, leechIntegralAction_embedding] at h
    exact h
  refine ⟨b⁻¹ * a, leechConcreteGeneratorSubgroup.mul_mem
    (leechConcreteGeneratorSubgroup.inv_mem hb) ha, ?_⟩
  change b.val.symm (a.val (griessShortVector r)) = griessShortVector s
  rw [he, b.val.symm_apply_apply]

/-- The actual 98280-label permutation action is transitive, without a model
recognition or externally supplied transitivity theorem. -/
theorem leechShort_concrete_label_transitive (r s : GriessShortIndex) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      griessShortPermutation e r = s := by
  obtain ⟨e, he, hv⟩ := leechShort_concrete_vector_transitive r s
  refine ⟨e, he, ?_⟩
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector e r with h | h
  · exact Or.inl (h.symm.trans hv)
  · exact Or.inr (by
      rw [hv] at h
      have he := congrArg Neg.neg h
      simpa only [neg_neg] using he.symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
