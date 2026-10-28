/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Commutativity of the concrete Conway product, including its Q-dependent signs.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortProductCovariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinOrthogonalLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortSumCovariance

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Multiplicative

theorem qCentral_square (c : ZMod 2) : qCentral c * qCentral c = 1 := by
  rw [qCentral_mul]
  have hc : c + c = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [hc]
  rfl

private theorem involutions_commute_of_product_square {M : Type*} [Group M]
    (g h : M) (hg : g * g = 1) (hh : h * h = 1) (hp : (g * h) * (g * h) = 1) :
    g * h = h * g := by
  have hgi : g = g⁻¹ := eq_inv_iff_mul_eq_one.mpr hg
  have hhi : h = h⁻¹ := eq_inv_iff_mul_eq_one.mpr hh
  calc
    g * h = (g * h)⁻¹ := eq_inv_iff_mul_eq_one.mpr hp
    _ = h⁻¹ * g⁻¹ := mul_inv_rev _ _
    _ = h * g := by rw [← hgi, ← hhi]

theorem griessShortQ_product_commute (r s u : GriessShortIndex)
    (h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) :
    griessShortQ r * griessShortQ s = griessShortQ s * griessShortQ r := by
  apply involutions_commute_of_product_square _ _
    (griessShortQ_square r) (griessShortQ_square s)
  rw [q_eq_central_short_of_base _ u h, qCentral_mul_products,
    griessShortQ_square]
  have hc : toAdd (griessShortQ r * griessShortQ s).coeff +
      toAdd (griessShortQ r * griessShortQ s).coeff = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [hc, mul_one]
  rfl

theorem q_product_base_comm (g h : Q) : (g * h).base = (h * g).base := by
  change g.base * h.base = h.base * g.base
  exact mul_comm _ _

theorem griessShortQ_base_faithful :
    Function.Injective (fun r : GriessShortIndex => (griessShortQ r).base) := by
  intro r s h
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact congrArg toAdd h

theorem griessShortQ_central_product_iff_same_label (r s : GriessShortIndex) :
    (griessShortQ r * griessShortQ s).base = 1 ↔ r = s := by
  constructor
  · intro h
    apply griessShortQ_base_faithful
    apply mul_left_cancel (a := (griessShortQ r).base)
    have hsq := congrArg (fun q : Q => q.base) (griessShortQ_square r)
    exact hsq.trans h.symm
  · rintro rfl
    rw [griessShortQ_square]
    rfl

theorem spinShortOperator_selfAdjoint (r : GriessShortIndex) (x y : SpinSpace) :
    spinPairing (spinOperator (griessShortQ r) x) y =
      spinPairing x (spinOperator (griessShortQ r) y) := by
  have hi : (griessShortQ r)⁻¹ = griessShortQ r :=
    (eq_inv_iff_mul_eq_one.mpr (griessShortQ_square r)).symm
  exact (spinRepresentation_pairing_move (griessShortQ r) x y).trans
    (by rw [hi]; rfl)

theorem conwayShortShortProduct_comm (x y : GriessShortIndex → ℝ) :
    conwayShortShortProduct x y = conwayShortShortProduct y x := by
  funext u
  unfold conwayShortShortProduct
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [q_product_base_comm (griessShortQ s) (griessShortQ r)]
  by_cases h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base
  · simp only [h, ite_true]
    rw [← griessShortQ_product_commute r s u h]
    ring
  · simp [h]

theorem conwayShortShortMatrix_comm (x y : GriessShortIndex → ℝ) :
    conwayShortShortMatrix x y = conwayShortShortMatrix y x := by
  ext i j
  rw [conwayShortShortMatrix_apply, conwayShortShortMatrix_apply]
  simp_rw [griessShortQ_central_product_iff_same_label]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem conwayTensorCoefficient_comm (r : GriessShortIndex) (i j : Fin 24) :
    conwayTensorCoefficient r i j = conwayTensorCoefficient r j i := by
  unfold conwayTensorCoefficient
  by_cases h : i = j
  · subst j
    rfl
  · simp only [h, Ne.symm h, ite_false]
    ring

set_option maxHeartbeats 1000000 in
-- Reindexing the three finite sums unfolds the concrete spin action.
theorem conwayTensorTensorShort_pairing (x y : SpinIndex → Fin 24 → ℝ)
    (r : GriessShortIndex) :
    conwayTensorTensorShort x y r =
      (∑ i, ∑ j, spinPairing (spinOperator (griessShortQ r) (fun t => x t i))
        (fun t => y t j) * conwayTensorCoefficient r i j) / 8 := by
  rw [conwayTensorTensorShort_apply]
  simp only [spinPairing, Finset.sum_mul]
  apply congrArg (fun z : ℝ => z / 8)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem conwayTensorTensorShort_comm (x y : SpinIndex → Fin 24 → ℝ) :
    conwayTensorTensorShort x y = conwayTensorTensorShort y x := by
  funext r
  rw [conwayTensorTensorShort_pairing, conwayTensorTensorShort_pairing]
  apply congrArg (fun z : ℝ => z / 8)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [spinShortOperator_selfAdjoint, spinPairing_swap,
    conwayTensorCoefficient_comm]

theorem conwayTensorTensorMatrix_comm (x y : SpinIndex → Fin 24 → ℝ) :
    conwayTensorTensorMatrix x y = conwayTensorTensorMatrix y x := by
  ext i j
  rw [conwayTensorTensorMatrix_apply, conwayTensorTensorMatrix_apply]
  have hd (t : SpinIndex) : (∑ k, x t k * y t k) = ∑ k, y t k * x t k := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hd]
  apply congrArg (fun z : ℝ => z / 8)
  apply Finset.sum_congr rfl
  intro t _
  ring

set_option maxHeartbeats 1000000 in
-- The raw product comparison traverses its three explicitly defined output blocks.
theorem conwayRawProduct_comm (x y : ConwayRawSpace) :
    conwayRawProduct x y = conwayRawProduct y x := by
  apply Prod.ext
  · ext i j
    have hxx := congrFun (congrFun
      (conwayShortShortMatrix_comm x.2.1 y.2.1) i) j
    rw [conwayShortShortMatrix_apply, conwayShortShortMatrix_apply] at hxx
    have htt := congrFun (congrFun
      (conwayTensorTensorMatrix_comm x.2.2 y.2.2) i) j
    rw [conwayTensorTensorMatrix_apply, conwayTensorTensorMatrix_apply] at htt
    change 2 * (∑ k, (x.1 i k * y.1 k j + y.1 i k * x.1 k j)) + _ + _ = _
    rw [hxx, htt]
    have haa : (∑ k, (x.1 i k * y.1 k j + y.1 i k * x.1 k j)) =
        ∑ k, (y.1 i k * x.1 k j + x.1 i k * y.1 k j) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [haa]
    rfl
  · apply Prod.ext
    · funext u
      have hxx := congrFun (conwayShortShortProduct_comm x.2.1 y.2.1) u
      change (∑ r, ∑ s, if (griessShortQ r * griessShortQ s).base =
          (griessShortQ u).base then qSign (toAdd (griessShortQ r * griessShortQ s).coeff) *
          x.2.1 r * y.2.1 s else 0) = _ at hxx
      have htt := congrFun (conwayTensorTensorShort_comm x.2.2 y.2.2) u
      rw [conwayTensorTensorShort_apply, conwayTensorTensorShort_apply] at htt
      change conwayShortPairing x.1 u * y.2.1 u + conwayShortPairing y.1 u * x.2.1 u +
        _ + _ = _
      rw [hxx, htt]
      unfold conwayRawProduct conwayShortShortProduct
      ring
    · funext t i
      change (∑ j, (x.1 j i * y.2.2 t j + y.1 j i * x.2.2 t j)) +
        Matrix.trace x.1 / 8 * y.2.2 t i + Matrix.trace y.1 / 8 * x.2.2 t i +
        (∑ r, ∑ j, (x.2.1 r * spinOperator (griessShortQ r) (fun v => y.2.2 v j) t +
          y.2.1 r * spinOperator (griessShortQ r) (fun v => x.2.2 v j) t) *
          conwayTensorCoefficient r j i) / 8 = _
      have hmat : (∑ j, (x.1 j i * y.2.2 t j + y.1 j i * x.2.2 t j)) =
          ∑ j, (y.1 j i * x.2.2 t j + x.1 j i * y.2.2 t j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hshort : (∑ r, ∑ j, (x.2.1 r *
          spinOperator (griessShortQ r) (fun v => y.2.2 v j) t + y.2.1 r *
          spinOperator (griessShortQ r) (fun v => x.2.2 v j) t) *
          conwayTensorCoefficient r j i) =
          ∑ r, ∑ j, (y.2.1 r * spinOperator (griessShortQ r) (fun v => x.2.2 v j) t +
            x.2.1 r * spinOperator (griessShortQ r) (fun v => y.2.2 v j) t) *
            conwayTensorCoefficient r j i := by
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hmat, hshort]
      unfold conwayRawProduct
      ring

/-- Commutativity for the actual dictionary algebra on all vectors. -/
theorem griessProd_comm (x y : GriessSpace) : griessProd x y = griessProd y x := by
  rw [griessProd_eq_conwayRawProduct, griessProd_eq_conwayRawProduct,
    conwayRawProduct_comm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
