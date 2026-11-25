/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.CharP.Basic
public import MathlibExt.Combinatorics.Additive.GDifferenceBases
import Mathlib.Tactic.Ring

/-!
# Difference bases of finite-field squares

Differences of points on the parabola cover every pair with nonzero first coordinate.
A minimum difference basis on the vertical axis supplies the remaining pairs.
-/

namespace MetaMathlibExt

private theorem one_le_subRepCount_iff {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} {x : G} : 1 ≤ subRepCount A x ↔ ∃ a ∈ A, ∃ b ∈ A, a - b = x := by
  change 0 < ((A ×ˢ A).filter fun p => p.1 - p.2 = x).card ↔ _
  rw [Finset.card_pos]
  simp only [Finset.Nonempty, Prod.exists, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, h⟩
    exact ⟨a, ha, b, hb, h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, b, ⟨ha, hb⟩, h⟩

private theorem exists_min_groupDiffBasis_one (G : Type*)
    [AddCommGroup G] [Fintype G] [DecidableEq G] :
    ∃ B : Finset G, B.card = groupDiffBasisNumber 1 G ∧ ∀ x, 1 ≤ subRepCount B x := by
  apply Nat.sInf_mem (s := {k | ∃ B : Finset G, B.card = k ∧ ∀ x, 1 ≤ subRepCount B x})
  refine ⟨Finset.univ.card, Finset.univ, rfl, fun x => one_le_subRepCount_iff.mpr ?_⟩
  exact ⟨x, Finset.mem_univ _, 0, Finset.mem_univ _, sub_zero _⟩

/-- **Difference bases of the square of a finite field.** For an abelian group $G$ let
$\eta_1(G)$ be the least size of a set $A \subseteq G$ such that every element of $G$ is a
difference $a - a'$ of two elements of $A$. If $K$ is a finite field with $q$ elements whose
characteristic is not $2$, then $\eta_1(K \times K) \le q + \eta_1(K)$, where $K$ and
$K \times K$ are taken as additive groups.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 6 (`integers-2025-A77-lem-6`). -/
public theorem groupDiffBasisNumber_prod_self_le {K : Type*} [Field K] [Finite K]
    [DecidableEq K] (hK : ringChar K ≠ 2) :
    groupDiffBasisNumber 1 (K × K) ≤ Nat.card K + groupDiffBasisNumber 1 K := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨B, hBcard, hB⟩ := exists_min_groupDiffBasis_one K
  let parabola (x : K) : K × K := (x, x ^ 2)
  let vertical (x : K) : K × K := (0, x)
  let P := Finset.univ.image parabola
  let V := B.image vertical
  have hP (x : K) : parabola x ∈ P ∪ V :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem parabola (Finset.mem_univ x))
  have hV {x : K} (hx : x ∈ B) : vertical x ∈ P ∪ V :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem vertical hx)
  calc
    groupDiffBasisNumber 1 (K × K) ≤ (P ∪ V).card := by
      apply Nat.sInf_le
      refine ⟨P ∪ V, rfl, ?_⟩
      rintro ⟨a, b⟩
      apply one_le_subRepCount_iff.mpr
      by_cases ha : a = 0
      · subst a
        obtain ⟨u, hu, v, hv, huv⟩ := one_le_subRepCount_iff.mp (hB b)
        exact ⟨vertical u, hV hu, vertical v, hV hv, Prod.ext (sub_self _) huv⟩
      · let x := (a + b / a) / 2
        have hx : 2 * x = a + b / a :=
          (mul_comm _ _).trans (div_mul_cancel₀ _ (Ring.two_ne_zero hK))
        have hsq : x ^ 2 - (x - a) ^ 2 = b := by
          calc
            _ = (2 * x - a) * a := by ring
            _ = (b / a) * a := by rw [hx, add_sub_cancel_left]
            _ = b := div_mul_cancel₀ _ ha
        exact ⟨parabola x, hP x, parabola (x - a), hP (x - a),
          Prod.ext (show x - (x - a) = a by simp) hsq⟩
    _ ≤ P.card + V.card := Finset.card_union_le _ _
    _ ≤ (Finset.univ : Finset K).card + B.card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = Nat.card K + groupDiffBasisNumber 1 K := by
      rw [Finset.card_univ, Nat.card_eq_fintype_card, hBcard]

end MetaMathlibExt
