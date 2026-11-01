/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountCoefficients

/-! Reuse of the verified original coordinate histograms at all bounded square sums. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The coefficient of a product is the finite square/height convolution. -/
theorem leechNormSixPairSeries_product (f g : LeechNormEightSeries) (N : ℕ) (h : ZMod 8) :
    (f * g).coeff (N, h) =
      ∑ q : Fin (N + 1), ∑ r : ZMod 8,
        f.coeff (q.val, r) * g.coeff (N - q.val, h - r) := by
  let idx : (Fin (N + 1) × ZMod 8) → (ℕ × ZMod 8) × (ℕ × ZMod 8) :=
    fun p => ((p.1.val, p.2), (N - p.1.val, h - p.2))
  have hi : Function.Injective idx := by
    rintro ⟨q, r⟩ ⟨s, t⟩ he
    have he' := congrArg Prod.fst he
    simp only [idx, Prod.mk.injEq] at he'
    exact Prod.ext (Fin.ext he'.1) he'.2
  have hs : ∀ {p}, p ∈ Finset.univ.image idx ↔ p.1 + p.2 = (N, h) := by
    rintro ⟨⟨q, r⟩, ⟨s, t⟩⟩
    constructor
    · intro hp
      obtain ⟨⟨a, b⟩, _, he⟩ := Finset.mem_image.mp hp
      cases he
      dsimp [idx]
      exact Prod.ext (by omega) (by abel_nf)
    · intro hp
      have hp' : q + s = N ∧ r + t = h := by
        simpa only [Prod.mk_add_mk, Prod.mk.injEq] using hp
      refine Finset.mem_image.mpr ⟨(⟨q, by omega⟩, r), Finset.mem_univ _, ?_⟩
      dsimp [idx]
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · change N - q = s
          omega
        · change h - r = t
          linear_combination -hp'.2
  rw [AddMonoidAlgebra.coeff_mul_antidiag f g (N, h) _ hs]
  rw [Finset.sum_image (fun _ _ _ _ he => hi he)]
  exact Fintype.sum_prod_type _


/-- Exact convolution of the already verified source histograms for the 22 remaining coordinates. -/
theorem leechNormSixPair_tail_table (m : Bool) (w : Fin 23)
    (q : Fin 65) (h : ZMod 8) :
    (leechNormEightCoordinateSeries m 0 ^ (22 - w.val) *
      leechNormEightCoordinateSeries m 1 ^ w.val).coeff (q.val, h) =
      ∑ r : Fin (q.val + 1), ∑ b : ZMod 8,
        leechNormEightCountTable m 0 ⟨22 - w.val, by omega⟩ ⟨r.val, by omega⟩ b *
        leechNormEightCountTable m 1 ⟨w.val, by omega⟩ ⟨q.val - r.val, by omega⟩ (h - b) := by
  rw [leechNormSixPairSeries_product]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro b _
  rw [leechNormEightCountTable_sound m 0 _ (by omega) _ (by omega),
    leechNormEightCountTable_sound m 1 _ (by omega) _ (by omega)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
