/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.ThomsonPrinciple

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The Nash-Williams inequality

If vertices `a ≠ z` of a finite network are separated by pairwise disjoint edge cutsets
`Π₁, …, Πₙ`, then `R_eff(a, z) ≥ ∑_k (∑_{e ∈ Π_k} c(e))⁻¹` (R. Lyons and Y. Peres, *Probability on
Trees and Networks*, Cambridge University Press 2016, corrected online version of
19 August 2026, Section 2.5, the Nash-Williams Inequality (2.13)). The proof is the source's: the
unit current carries at least one unit across every cutset (`one_le_sum_abs_of_separates`), so by
Cauchy-Schwarz its energy on `Π_k` is at least `(∑_{e ∈ Π_k} c(e))⁻¹`, and the effective
resistance is that energy by Thomson's principle.
-/

@[expose] public section

namespace EndpointMapMultigraph

open Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] [Fintype V]
  (end₁ end₂ : E → V)

/-- **Separating edge set (cutset).** The edge set `P` separates `a` from `z`: `z` cannot be
reached from `a` along edges outside `P`, so every path from `a` to `z` uses an edge of `P`
(R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016,
corrected online version of 19 August 2026, Section 2.5: a set `Π` of edges separates `A` and `Z`
if every path with one endpoint in `A` and the other in `Z` includes an edge in `Π`). -/
def Separates (P : Finset E) (a z : V) : Prop :=
  ¬ Relation.ReflTransGen (AdjacentUsing end₁ end₂ (Finset.univ \ P)) a z

omit [DecidableEq V] [Fintype V] in
/-- An edge outside `P` keeps both of its ends on the same side of `Π`. -/
private theorem reach_iff_of_not_mem {P : Finset E} {a : V} {e : E} (he : e ∉ P) :
    Relation.ReflTransGen (AdjacentUsing end₁ end₂ (Finset.univ \ P)) a (end₁ e) ↔
      Relation.ReflTransGen (AdjacentUsing end₁ end₂ (Finset.univ \ P)) a (end₂ e) := by
  have hadj : AdjacentUsing end₁ end₂ (Finset.univ \ P) (end₁ e) (end₂ e) := by
    classical
    exact ⟨e, by simp [he], Or.inl ⟨rfl, rfl⟩⟩
  have hadj' : AdjacentUsing end₁ end₂ (Finset.univ \ P) (end₂ e) (end₁ e) := by
    classical
    exact ⟨e, by simp [he], Or.inr ⟨rfl, rfl⟩⟩
  exact ⟨fun h => h.tail hadj, fun h => h.tail hadj'⟩

omit [Fintype V] in
/-- **A unit flow crosses every cutset.** If `P` separates `a` from `z` and `θ` is a unit flow
from `a` to `z`, then `∑_{e ∈ P} |θ_e| ≥ 1` (R. Lyons and Y. Peres, *Probability on Trees and
Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, proof of
the Nash-Williams Inequality, Section 2.5, via flow conservation, Lemma 2.8). -/
theorem one_le_sum_abs_of_separates [Finite V] {P : Finset E} {a z : V}
    (hsep : Separates end₁ end₂ P a z) {θ : E → ℝ} (hθ : IsUnitFlow end₁ end₂ a z θ) :
    1 ≤ ∑ e ∈ P, |θ e| := by
  have := Fintype.ofFinite V
  classical
  set R := Relation.ReflTransGen (AdjacentUsing end₁ end₂ (Finset.univ \ P)) a with hR
  set K : Finset V := Finset.univ.filter fun x => R x with hK
  have haK : a ∈ K := by simp [hK, R, Relation.ReflTransGen.refl]
  have hzK : z ∉ K := fun h => hsep (by simpa [hK, R] using h)
  have haz : a ≠ z := fun h => hzK (h ▸ haK)
  -- net outflow of `K`
  have hout : ∑ x ∈ K, (orientedIncidence end₁ end₂ *ᵥ θ) x = 1 := by
    rw [hθ]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply, Finset.sum_ite_eq',
      haK, hzK, ↓reduceIte, sub_zero]
  have hswap : ∑ x ∈ K, (orientedIncidence end₁ end₂ *ᵥ θ) x =
      ∑ e, θ e * ((if end₁ e ∈ K then 1 else 0) - if end₂ e ∈ K then 1 else 0) := by
    simp only [Matrix.mulVec, dotProduct, orientedIncidence_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_mul, mul_comm, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq]
  have hoff : ∀ e ∉ P, θ e * ((if end₁ e ∈ K then 1 else 0) - if end₂ e ∈ K then 1 else 0) =
      0 := by
    intro e he
    have := reach_iff_of_not_mem end₁ end₂ (a := a) he
    have hiff : end₁ e ∈ K ↔ end₂ e ∈ K := by simpa [hK, R] using this
    by_cases h₁ : end₁ e ∈ K
    · simp [h₁, hiff.1 h₁]
    · simp [h₁, (not_congr hiff).1 h₁]
  have hsplit : ∑ e, θ e * ((if end₁ e ∈ K then 1 else 0) - if end₂ e ∈ K then 1 else 0) =
      ∑ e ∈ P, θ e * ((if end₁ e ∈ K then 1 else 0) - if end₂ e ∈ K then 1 else 0) := by
    rw [← Finset.sum_subset (Finset.subset_univ P) fun e _ he => hoff e he]
  rw [← hout, hswap, hsplit]
  refine (Finset.abs_sum_le_sum_abs _ _).trans' (le_abs_self _) |>.trans ?_
  refine Finset.sum_le_sum fun e _ => ?_
  rw [abs_mul]
  have : |((if end₁ e ∈ K then (1 : ℝ) else 0) - if end₂ e ∈ K then 1 else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  nlinarith [abs_nonneg (θ e)]

/-- **The Nash-Williams inequality.** In a finite loopless multigraph with positive conductances
`w`, let `a ≠ z` be in the same connected component and let `C k` (`k ∈ s`) be pairwise disjoint
edge sets, each separating `a` from `z`. Then
`R_eff(a, z) ≥ ∑_{k ∈ s} (∑_{e ∈ C k} w_e)⁻¹` (R. Lyons and Y. Peres, *Probability on Trees and
Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
Section 2.5, the Nash-Williams Inequality (2.13)). -/
theorem sum_inv_le_effectiveResistance {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) {a z : V} (haz : a ≠ z)
    (hreach : (underlyingGraph end₁ end₂).Reachable a z) {ι : Type*} (s : Finset ι)
    (C : ι → Finset E) (hdisj : (s : Set ι).PairwiseDisjoint C)
    (hsep : ∀ k ∈ s, Separates end₁ end₂ (C k) a z) :
    ∑ k ∈ s, (∑ e ∈ C k, w e)⁻¹ ≤ effectiveResistance end₁ end₂ w a z := by
  classical
  obtain ⟨⟨θ, hθ, hR⟩, -⟩ := isLeast_flowEnergy end₁ end₂ hw hloop haz hreach
  rw [hR, flowEnergy]
  have hpos : ∀ e, 0 ≤ θ e ^ 2 / w e := fun e => div_nonneg (sq_nonneg _) (hw e).le
  calc ∑ k ∈ s, (∑ e ∈ C k, w e)⁻¹
      ≤ ∑ k ∈ s, ∑ e ∈ C k, θ e ^ 2 / w e := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hcross := one_le_sum_abs_of_separates end₁ end₂ (hsep k hk) hθ
        have hsed := Finset.sq_sum_div_le_sum_sq_div (C k) (fun e => |θ e|)
          (g := w) fun e _ => hw e
        simp only [sq_abs] at hsed
        have hW : 0 ≤ ∑ e ∈ C k, w e := Finset.sum_nonneg fun e _ => (hw e).le
        refine le_trans ?_ hsed
        rw [inv_eq_one_div]
        exact div_le_div_of_nonneg_right (by nlinarith) hW
    _ = ∑ e ∈ s.biUnion C, θ e ^ 2 / w e := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ e, θ e ^ 2 / w e :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun e _ _ => hpos e

end EndpointMapMultigraph
