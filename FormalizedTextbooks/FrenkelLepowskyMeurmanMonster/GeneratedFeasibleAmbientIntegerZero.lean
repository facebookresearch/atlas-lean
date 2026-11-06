/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientZeroTools
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortIntegral
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortInputData

/-! A finite integer certificate scheme for orthogonal signed-short axes.

If the matrix and short coordinates of a vector are given by integer numerators, and the
matrix numerator dominates a multiple `λ` of the identity by an explicit nonnegative
rank-one decomposition, then a short numerator of small absolute value never yields
orthogonality. Every remaining address is checked exactly against an explicit finite
catalogue, which bounds the number of orthogonal actual signed-short axes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The integer quadratic value of a matrix numerator on an integral vector. -/
def generatedFeasibleAmbientQuad (N : Fin 24 → Fin 24 → ℤ) (u : Fin 24 → ℤ) : ℤ :=
  ∑ i, ∑ j, u i * N i j * u j

/-- The integer sign of an actual sign label. -/
def generatedFeasibleAmbientSign (c : ZMod 2) : ℤ := if c = 0 then 1 else -1

/-- A nonnegative rank-one decomposition of `D (N - λ I)` gives `λ |u|² ≤ uᵀ N u`. -/
theorem generatedFeasibleAmbient_quad_ge_of_decomp {K : ℕ} (N : Fin 24 → Fin 24 → ℤ)
    (lam D : ℤ) (c : Fin K → ℤ) (w : Fin K → Fin 24 → ℤ) (hD : 0 < D) (hc : ∀ k, 0 ≤ c k)
    (hdec : ∀ i j, D * N i j =
      D * lam * (if i = j then 1 else 0) + ∑ k, c k * (w k i * w k j))
    (u : Fin 24 → ℤ) :
    lam * ∑ i, u i ^ 2 ≤ generatedFeasibleAmbientQuad N u := by
  have hterm (i j : Fin 24) : D * (u i * N i j * u j) =
      D * lam * (if i = j then u i * u j else 0) +
        ∑ k, c k * ((w k i * u i) * (w k j * u j)) := by
    calc D * (u i * N i j * u j) = u i * (D * N i j) * u j := by ring
      _ = u i * (D * lam * (if i = j then 1 else 0) + ∑ k, c k * (w k i * w k j)) * u j := by
          rw [hdec i j]
      _ = D * lam * (if i = j then u i * u j else 0) +
          ∑ k, u i * (c k * (w k i * w k j)) * u j := by
          rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
          congr 1
          split_ifs <;> ring
      _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          ring
  have hexp : D * generatedFeasibleAmbientQuad N u =
      D * lam * ∑ i, u i ^ 2 + ∑ k, c k * (∑ i, w k i * u i) ^ 2 := by
    unfold generatedFeasibleAmbientQuad
    simp_rw [Finset.mul_sum, hterm, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, Finset.sum_ite_eq]
      simp [sq]
    · calc ∑ i, ∑ j, ∑ k, c k * ((w k i * u i) * (w k j * u j))
          = ∑ i, ∑ k, ∑ j, c k * ((w k i * u i) * (w k j * u j)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_comm
        _ = ∑ k, ∑ i, ∑ j, c k * ((w k i * u i) * (w k j * u j)) := Finset.sum_comm
        _ = _ := by
            apply Finset.sum_congr rfl
            intro k _
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
  have hnn : 0 ≤ ∑ k, c k * (∑ i, w k i * u i) ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (sq_nonneg _)
  have h2 : D * (lam * ∑ i, u i ^ 2) ≤ D * generatedFeasibleAmbientQuad N u := by
    rw [hexp]
    linarith
  exact le_of_mul_le_mul_left h2 hD

/-- A finite catalogue containing every orthogonal address bounds the orthogonal axis count. -/
theorem generatedFeasibleAmbientAxisZeroCount_le_of_subset (x : GriessSpace)
    (Z : Finset (GriessShortIndex × ZMod 2))
    (h : ∀ r c, griessForm (conwayShortAxis r c) x = 0 → (r, c) ∈ Z) :
    generatedFeasibleAmbientAxisZeroCount x ≤ Z.card := by
  unfold generatedFeasibleAmbientAxisZeroCount
  change Nat.card ↥{p : GriessShortIndex × ZMod 2 |
    griessForm (conwayShortAxis p.1 p.2) x = 0} ≤ Z.card
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (Finset.finite_toSet Z)
  rintro ⟨r, c⟩ hp
  exact h r c hp

/-- The integer certificate scheme. Short numerators of absolute value below `B` cannot give
orthogonality because `DM · B ≤ DS · λ`; every other address satisfies the explicit check. -/
theorem generatedFeasibleAmbient_zero_mem_of_check (x : GriessSpace)
    (N : Fin 24 → Fin 24 → ℤ) (n : GriessShortIndex → ℤ) (DM DS : ℕ) (hDM : 0 < DM)
    (hDS : 0 < DS) (hM : ∀ i j, (griessConwayEncode x).1 i j = (N i j : ℝ) / DM)
    (hS : ∀ r, (griessConwayEncode x).2.1 r = (n r : ℝ) / DS) (lam B : ℤ)
    (hpd : ∀ u : Fin 24 → ℤ, lam * ∑ i, u i ^ 2 ≤ generatedFeasibleAmbientQuad N u)
    (hB : (DM : ℤ) * B ≤ DS * lam) (Z : Finset (GriessShortIndex × ZMod 2))
    (hcheck : ∀ r, |n r| < B ∨ ∀ c : ZMod 2,
      (DS : ℤ) * generatedFeasibleAmbientQuad N (generatedAxisGlobalShortIntegral r) =
        32 * DM * generatedFeasibleAmbientSign c * n r → (r, c) ∈ Z)
    (r : GriessShortIndex) (c : ZMod 2) (h : griessForm (conwayShortAxis r c) x = 0) :
    (r, c) ∈ Z := by
  rw [generatedFeasibleAmbient_axis_form_eq_zero_iff_int r c x N (n r) DM DS hDM hDS hM
    (hS r)] at h
  have hq : (DS : ℤ) * generatedFeasibleAmbientQuad N (generatedAxisGlobalShortIntegral r) =
      32 * DM * generatedFeasibleAmbientSign c * n r := by
    rw [generatedAxisGlobalShortIntegral_actual]
    exact h
  rcases hcheck r with hs | hz
  · exfalso
    have hp := hpd (griessShortIntegral r)
    have hsq := griessShortIntegral_squareSum r
    unfold leechSquareSum at hsq
    rw [hsq] at hp
    rw [generatedAxisGlobalShortIntegral_actual] at hq
    unfold generatedFeasibleAmbientQuad at hp hq
    have habs := abs_lt.mp hs
    have hDS' : (0 : ℤ) < DS := by exact_mod_cast hDS
    have hDM' : (0 : ℤ) < DM := by exact_mod_cast hDM
    unfold generatedFeasibleAmbientSign at hq
    split_ifs at hq <;> nlinarith
  · exact hz c hq

/-- A property of all actual short labels follows from 96 packets of 1024 finite addresses. -/
theorem generatedFeasibleAmbient_address_join (P : GriessShortIndex → Prop)
    (h : ∀ b : Fin 96, ∀ u : Fin 1024,
      if hb : b.val * 1024 + u.val < 98280 then
        P (generatedNinthLowerSpinShortIndex ⟨b.val * 1024 + u.val, hb⟩) else True)
    (r : GriessShortIndex) : P r := by
  rw [← generatedNinth_lower_spin_short_index_address r]
  set a := generatedNinthLowerSpinShortAddress r
  let b : Fin 96 := ⟨a.val / 1024, by have ha := a.isLt; omega⟩
  let u : Fin 1024 := ⟨a.val % 1024, Nat.mod_lt _ (by decide)⟩
  have hb : b.val * 1024 + u.val < 98280 := by have ha := a.isLt; dsimp [b, u]; omega
  have hh := h b u
  rw [dite_eq_left hb] at hh
  have he : (⟨b.val * 1024 + u.val, hb⟩ : Fin 98280) = a := by
    apply Fin.ext
    dsimp [b, u]
    omega
  rw [he] at hh
  exact hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
