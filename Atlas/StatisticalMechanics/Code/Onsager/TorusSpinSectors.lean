/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CoeffMatch
import Code.Onsager.Torus

namespace StatMech.Onsager

open StatMech.Ising


def ons_xSeamEdge (L : ℕ) (e : Sym2 (ZMod L × ZMod L)) : Prop :=
  ∃ y : ZMod L, e = s(((0 : ZMod L), y), (-1, y))


def ons_ySeamEdge (L : ℕ) (e : Sym2 (ZMod L × ZMod L)) : Prop :=
  ∃ x : ZMod L, e = s((x, (0 : ZMod L)), (x, -1))

noncomputable def ons_evenHomology (L : ℕ)
    (F : Finset (Sym2 (ZMod L × ZMod L))) : Fin 2 × Fin 2 :=
  by
    classical
    exact (⟨(F.filter (ons_xSeamEdge L)).card % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨(F.filter (ons_ySeamEdge L)).card % 2, Nat.mod_lt _ (by decide)⟩)

theorem ons_evenHomology_union (L : ℕ)
    (F G : Finset (Sym2 (ZMod L × ZMod L))) (hdisj : Disjoint F G) :
    ons_evenHomology L (F ∪ G) =
      ons_evenHomology L F + ons_evenHomology L G := by
  classical
  apply Prod.ext
  · apply Fin.ext
    change ((F ∪ G).filter (ons_xSeamEdge L)).card % 2 =
      (((F.filter (ons_xSeamEdge L)).card % 2) +
        ((G.filter (ons_xSeamEdge L)).card % 2)) % 2
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      Nat.add_mod]
  · apply Fin.ext
    change ((F ∪ G).filter (ons_ySeamEdge L)).card % 2 =
      (((F.filter (ons_ySeamEdge L)).card % 2) +
        ((G.filter (ons_ySeamEdge L)).card % 2)) % 2
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      Nat.add_mod]

theorem ons_evenHomology_biUnion
    {L : ℕ} {iota : Type*} [DecidableEq iota]
    (S : Finset iota)
    (piece : iota → Finset (Sym2 (ZMod L × ZMod L)))
    (hdisj : (S : Set iota).PairwiseDisjoint piece) :
    ons_evenHomology L (S.biUnion piece) =
      ∑ i ∈ S, ons_evenHomology L (piece i) := by
  induction S using Finset.induction_on with
  | empty =>
      simp [ons_evenHomology]
  | @insert a S ha ih =>
      have hdisjS : (S : Set iota).PairwiseDisjoint piece := by
        intro i hi j hj hij
        exact hdisj (by simp [hi]) (by simp [hj]) hij
      have haS : Disjoint (piece a) (S.biUnion piece) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj (by simp) (by simp [hj]) (by
          intro haj
          subst j
          exact ha hj)
      rw [Finset.biUnion_insert, ons_evenHomology_union L _ _ haS,
        Finset.sum_insert ha, ih hdisjS]

noncomputable def ons_sectorWeight (L : ℕ) [Fact (2 < L)] (x : ℝ) (h : Fin 2 × Fin 2) : ℝ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L) with ons_evenHomology L F = h, x ^ F.card

theorem ons_X_eq_sum_sectorWeight (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_X (onsTorusGraph L) x = ∑ h : Fin 2 × Fin 2, ons_sectorWeight L x h := by
  rw [ons_X_eq_sum_evenSubgraphs]
  exact (Finset.sum_fiberwise (evenSubgraphs (onsTorusGraph L))
    (ons_evenHomology L) (fun F => x ^ F.card)).symm

noncomputable def ons_sector00 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sectorWeight L x (0, 0)

noncomputable def ons_sector10 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sectorWeight L x (1, 0)

noncomputable def ons_sector01 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sectorWeight L x (0, 1)

noncomputable def ons_sector11 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sectorWeight L x (1, 1)


noncomputable def ons_spin00 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sector00 L x + ons_sector10 L x + ons_sector01 L x - ons_sector11 L x

noncomputable def ons_spin10 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sector00 L x - ons_sector10 L x + ons_sector01 L x + ons_sector11 L x

noncomputable def ons_spin01 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sector00 L x + ons_sector10 L x - ons_sector01 L x + ons_sector11 L x

noncomputable def ons_spin11 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sector00 L x - ons_sector10 L x - ons_sector01 L x - ons_sector11 L x

theorem ons_X_eq_sector_sum (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_X (onsTorusGraph L) x =
      ons_sector00 L x + ons_sector10 L x + ons_sector01 L x + ons_sector11 L x := by
  rw [ons_X_eq_sum_sectorWeight]
  simp [ons_sector00, ons_sector10, ons_sector01, ons_sector11, Fin.sum_univ_two,
    Fintype.sum_prod_type]
  ring


theorem ons_two_mul_X_eq_spin_sum (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    2 * ons_X (onsTorusGraph L) x =
      ons_spin00 L x + ons_spin10 L x + ons_spin01 L x - ons_spin11 L x := by
  rw [ons_X_eq_sector_sum]
  unfold ons_spin00 ons_spin10 ons_spin01 ons_spin11
  ring

theorem ons_sectorWeight_nonneg (L : ℕ) [Fact (2 < L)] {x : ℝ} (hx : 0 ≤ x)
    (h : Fin 2 × Fin 2) : 0 ≤ ons_sectorWeight L x h := by
  unfold ons_sectorWeight
  positivity

theorem ons_sectorWeight_zero (L : ℕ) [Fact (2 < L)] (h : Fin 2 × Fin 2) :
    ons_sectorWeight L 0 h = if h = (0, 0) then 1 else 0 := by
  classical
  unfold ons_sectorWeight
  by_cases hh : h = (0, 0)
  · subst h
    rw [if_pos rfl]
    rw [Finset.sum_eq_single (∅ : Finset (Sym2 (ZMod L × ZMod L)))]
    · simp
    · intro F hF hFne
      have hcard : F.card ≠ 0 := by simpa [Finset.card_eq_zero] using hFne
      simp [hcard]
    · simp [evenSubgraphs, IsEvenSubgraph, incCount, ons_evenHomology]
  · rw [if_neg hh]
    apply Finset.sum_eq_zero
    intro F hF
    by_cases hFe : F = ∅
    · subst F
      simp [ons_evenHomology] at hF
      exact absurd hF.2.symm hh
    · have hcard : F.card ≠ 0 := by simpa [Finset.card_eq_zero] using hFe
      simp [hcard]


theorem ons_abs_spin_le_X (L : ℕ) [Fact (2 < L)] {x : ℝ} (hx : 0 ≤ x) :
    |ons_spin00 L x| ≤ ons_X (onsTorusGraph L) x ∧
    |ons_spin10 L x| ≤ ons_X (onsTorusGraph L) x ∧
    |ons_spin01 L x| ≤ ons_X (onsTorusGraph L) x ∧
    |ons_spin11 L x| ≤ ons_X (onsTorusGraph L) x := by
  have h00 := ons_sectorWeight_nonneg L hx ((0, 0) : Fin 2 × Fin 2)
  have h10 := ons_sectorWeight_nonneg L hx ((1, 0) : Fin 2 × Fin 2)
  have h01 := ons_sectorWeight_nonneg L hx ((0, 1) : Fin 2 × Fin 2)
  have h11 := ons_sectorWeight_nonneg L hx ((1, 1) : Fin 2 × Fin 2)
  rw [ons_X_eq_sector_sum]
  unfold ons_spin00 ons_spin10 ons_spin01 ons_spin11
  unfold ons_sector00 ons_sector10 ons_sector01 ons_sector11 at *
  constructor
  · rw [abs_le]
    constructor <;> linarith
  constructor
  · rw [abs_le]
    constructor <;> linarith
  constructor <;> rw [abs_le] <;> constructor <;> linarith


theorem ons_two_mul_X_le_sum_abs_spin (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    2 * ons_X (onsTorusGraph L) x ≤
      |ons_spin00 L x| + |ons_spin10 L x| + |ons_spin01 L x| + |ons_spin11 L x| := by
  rw [ons_two_mul_X_eq_spin_sum]
  linarith [le_abs_self (ons_spin00 L x), le_abs_self (ons_spin10 L x),
    le_abs_self (ons_spin01 L x), neg_le_abs (ons_spin11 L x)]

end StatMech.Onsager
