/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountSeries
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountData

/-! Soundness of the bounded convolution certificates.
The tables compute exact coefficients of the full generating series: discarding
square sums above64 cannot affect a coefficient at or below64. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem leechNormEightSeries_shift (f : LeechNormEightSeries)
    (a q : ℕ) (b h : ZMod 8) :
    (AddMonoidAlgebra.single (a, b) 1 * f).coeff (q, h) =
      if a ≤ q then f.coeff (q - a, h - b) else 0 := by
  by_cases ha : a ≤ q
  · rw [ite_eq_left ha]
    have hs : ∀ p ∈ f.coeff.support, (a, b) + p = (q, h) ↔ p = (q - a, h - b) := by
      rintro ⟨r, g⟩ _
      simp only [Prod.mk_add_mk, Prod.mk.injEq]
      constructor
      · rintro ⟨hr, hg⟩
        exact ⟨by omega, by linear_combination hg⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨by omega, by abel⟩
    simpa only [one_mul] using AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff
      (r := 1) (q - a, h - b) hs
  · rw [ite_eq_right ha]
    apply AddMonoidAlgebra.coeff_single_mul_of_forall_add_ne
    rintro ⟨r, g⟩ hp
    have he := congrArg Prod.fst hp
    dsimp at he
    omega

/-- Multiplication by a coordinate series is exactly the finite counting recurrence. -/
theorem leechNormEightCoordinateSeries_step (m : Bool) (b : ZMod 2)
    (f : LeechNormEightSeries) (q : ℕ) (h : ZMod 8) :
    (leechNormEightCoordinateSeries m b * f).coeff (q, h) =
      leechNormEightCountStep m b (fun q h => f.coeff (q, h)) q h := by
  unfold leechNormEightCoordinateSeries leechNormEightCountStep
  rw [Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : (leechNormEightCoordinate a : ZMod 4) =
      (m.toNat : ZMod 4) + 2 * (b.val : ZMod 4)
  · simp only [ha, ite_true, true_and]
    exact leechNormEightSeries_shift f _ _ _ _
  · simp only [ha, ite_false, false_and, zero_mul,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- The finite tables are exact coefficients of coordinate-series powers. -/
theorem leechNormEightCountTable_sound (m : Bool) (b : ZMod 2)
    (n : ℕ) (hn : n < 25) (q : ℕ) (hq : q < 65) (h : ZMod 8) :
    (leechNormEightCoordinateSeries m b ^ n).coeff (q, h) =
      leechNormEightCountTable m b ⟨n, hn⟩ ⟨q, hq⟩ h := by
  induction n generalizing q h with
  | zero =>
      rw [pow_zero]
      change (AddMonoidAlgebra.coeff (1 : LeechNormEightSeries)) (q, h) =
        leechNormEightCountTable m b 0 ⟨q, hq⟩ h
      rw [leechNormEightCountTable_zero]
      change (Finsupp.single (0, 0) 1 : (ℕ × ZMod 8) →₀ ℕ) (q, h) = _
      simp only [Finsupp.single_apply, Prod.mk.injEq]
      simp only [eq_comm]
  | succ n ih =>
      rw [pow_succ', leechNormEightCoordinateSeries_step]
      rw [leechNormEightCountTable_step m b ⟨n, by omega⟩]
      unfold leechNormEightCountStep
      apply Finset.sum_congr rfl
      intro a _
      split_ifs with ha
      · rw [leechNormEightCountTableNat, dite_eq_left (by omega)]
        exact ih (by omega) _ (by omega) _
      · rfl

/-- The coefficient of a product is the finite square/height convolution. -/
theorem leechNormEightSeries_product (f g : LeechNormEightSeries) (h : ZMod 8) :
    (f * g).coeff (64, h) =
      ∑ q : Fin 65, ∑ r : ZMod 8,
        f.coeff (q.val, r) * g.coeff (64 - q.val, h - r) := by
  let idx : (Fin 65 × ZMod 8) → (ℕ × ZMod 8) × (ℕ × ZMod 8) :=
    fun p => ((p.1.val, p.2), (64 - p.1.val, h - p.2))
  have hi : Function.Injective idx := by
    rintro ⟨q, r⟩ ⟨s, t⟩ he
    have he' := congrArg Prod.fst he
    simp only [idx, Prod.mk.injEq] at he'
    exact Prod.ext (Fin.ext he'.1) he'.2
  have hs : ∀ {p}, p ∈ Finset.univ.image idx ↔ p.1 + p.2 = (64, h) := by
    rintro ⟨⟨q, r⟩, ⟨s, t⟩⟩
    constructor
    · intro hp
      obtain ⟨⟨a, b⟩, _, he⟩ := Finset.mem_image.mp hp
      cases he
      dsimp [idx]
      exact Prod.ext (by omega) (by abel_nf)
    · intro hp
      have hp' : q + s = 64 ∧ r + t = h := by
        simpa only [Prod.mk_add_mk, Prod.mk.injEq] using hp
      refine Finset.mem_image.mpr ⟨(⟨q, by omega⟩, r), Finset.mem_univ _, ?_⟩
      dsimp [idx]
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · change 64 - q = s
          omega
        · change h - r = t
          linear_combination -hp'.2
  rw [AddMonoidAlgebra.coeff_mul_antidiag f g (64, h) _ hs]
  rw [Finset.sum_image (fun _ _ _ _ he => hi he)]
  exact Fintype.sum_prod_type _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
