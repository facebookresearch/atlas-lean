/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Compactness.DeltaGeneratedSpace
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Order
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Data.Fin.SuccPred
public import MathlibExt.Analysis.Convex.StdSimplex
/-!
# Delta-generated topology on standard simplices

Proves that the real standard simplex with `n + 1` vertices is
delta-generated. Establishes this property using a continuous retraction from
finite real coordinate space onto the simplex, obtained by normalizing
positive coordinates.
-/

@[expose] public section

open Set Topology

namespace DeltaGeneratedSpace

variable {n : ℕ}

private def posPart (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  max (x i) 0

private def sumPos (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), posPart (n := n) x i

private def denom (x : Fin (n + 1) → ℝ) : ℝ :=
  max (sumPos x) 1

private noncomputable def retractFun (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => posPart x i / denom x + if i = (0 : Fin (n + 1)) then (1 - sumPos x / denom x) else 0

private lemma posPart_nonneg (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    0 ≤ posPart x i :=
  le_max_right _ _

private lemma sumPos_nonneg (x : Fin (n + 1) → ℝ) : 0 ≤ sumPos x :=
  Finset.sum_nonneg fun i _ => posPart_nonneg x i

private lemma denom_pos (x : Fin (n + 1) → ℝ) : 0 < denom x := by
  unfold denom
  exact lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) (le_max_right _ _)

private lemma denom_ne_zero (x : Fin (n + 1) → ℝ) : denom x ≠ 0 :=
  ne_of_gt (denom_pos x)

private lemma denom_ge_sumPos (x : Fin (n + 1) → ℝ) : sumPos x ≤ denom x := by
  unfold denom
  exact le_max_left _ _

private lemma denom_ge_one (x : Fin (n + 1) → ℝ) : 1 ≤ denom x := by
  unfold denom
  exact le_max_right _ _

private lemma slack_nonneg (x : Fin (n + 1) → ℝ) : 0 ≤ 1 - sumPos x / denom x := by
  have hpos := denom_pos x
  have hle := denom_ge_sumPos x
  have hdiv_le_one : sumPos x / denom x ≤ 1 := by
    rw [div_le_one hpos]
    exact hle
  linarith

private lemma retractFun_nonneg (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    0 ≤ retractFun x i := by
  unfold retractFun
  by_cases hi : i = (0 : Fin (n + 1))
  · simp only [hi, ite_true]
    exact add_nonneg (div_nonneg (posPart_nonneg x 0) (le_of_lt (denom_pos x))) (slack_nonneg x)
  · simp only [hi, ite_false, add_zero]
    exact div_nonneg (posPart_nonneg x i) (le_of_lt (denom_pos x))

private lemma sum_retractFun (x : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), retractFun x i = 1 := by
  unfold retractFun
  calc ∑ i : Fin (n + 1),
    (posPart x i / denom x + if i = (0 : Fin (n + 1)) then (1 - sumPos x / denom x) else 0)
      = (∑ i : Fin (n + 1), posPart x i / denom x) +
        (∑ i : Fin (n + 1), if i = (0 : Fin (n + 1)) then (1 - sumPos x / denom x) else
        (0 : ℝ)) := by
        rw [← Finset.sum_add_distrib]
      _ = (∑ i : Fin (n + 1), posPart x i) / denom x + (1 - sumPos x / denom x) := by
        have h1 : (∑ i : Fin (n + 1), posPart x i / denom x) = (∑ i : Fin (n + 1), posPart x i) /
          denom x := by
          rw [← Finset.sum_div]
        have h2 :
          (∑ i : Fin (n + 1), if i = (0 : Fin (n + 1)) then (1 - sumPos x / denom x) else (0 : ℝ)) =
          1 - sumPos x / denom x := by
          rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1))]
          simp
        rw [h1, h2]
      _ = sumPos x / denom x + (1 - sumPos x / denom x) := by
        rfl
      _ = 1 := by
        ring

private lemma continuous_posPart (i : Fin (n + 1)) :
    Continuous (fun x : Fin (n + 1) → ℝ => posPart (n := n) x i) := by
  unfold posPart
  exact ((continuous_apply i).max continuous_const)

private lemma continuous_sumPos :
    Continuous (fun x : Fin (n + 1) → ℝ => sumPos (n := n) x) := by
  unfold sumPos
  exact continuous_finsetSum Finset.univ fun i _ => continuous_posPart i

private lemma continuous_denom :
    Continuous (fun x : Fin (n + 1) → ℝ => denom (n := n) x) := by
  unfold denom
  exact (continuous_sumPos (n := n)).max continuous_const

private lemma continuous_retractFun_coord (i : Fin (n + 1)) :
    Continuous (fun x : Fin (n + 1) → ℝ => retractFun (n := n) x i) := by
  have hpos : Continuous (fun x : Fin (n + 1) → ℝ => posPart (n := n) x i / denom (n := n) x) := by
    apply Continuous.div (continuous_posPart i) continuous_denom
    intro x
    exact denom_ne_zero x
  have hslack : Continuous
    (fun x : Fin (n + 1) → ℝ => (1 - sumPos (n := n) x / denom (n := n) x)) := by
    apply Continuous.sub continuous_const
    apply Continuous.div continuous_sumPos continuous_denom
    intro x
    exact denom_ne_zero x
  have h_if : Continuous (fun x : Fin (n + 1) → ℝ =>
      if i = (0 : Fin (n + 1)) then (1 - sumPos (n := n) x / denom (n := n) x) else (0 : ℝ)) := by
    by_cases hi : i = (0 : Fin (n + 1))
    · simp only [hi, ite_true]
      exact hslack
    · simp only [hi, ite_false]
      exact continuous_const
  have h_add : Continuous (fun x : Fin (n + 1) → ℝ =>
      posPart (n := n) x i / denom (n := n) x +
        if i = (0 : Fin (n + 1)) then (1 - sumPos (n := n) x / denom (n := n) x) else 0) :=
    hpos.add h_if
  have h_eq : (fun x : Fin (n + 1) → ℝ => retractFun (n := n) x i) =
      (fun x => posPart (n := n) x i / denom (n := n) x +
        if i = (0 : Fin (n + 1)) then (1 - sumPos (n := n) x / denom (n := n) x) else 0) := by
    funext x
    unfold retractFun
    rfl
  rw [h_eq]
  exact h_add

private lemma continuous_retractFun :
    Continuous (fun x : Fin (n + 1) → ℝ => retractFun (n := n) x) := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_retractFun_coord i

private lemma retractFun_fix_of_nonneg_sum (x : Fin (n + 1) → ℝ)
    (h_nonneg : ∀ i, 0 ≤ x i) (h_sum : ∑ i : Fin (n + 1), x i = 1) :
    retractFun (n := n) x = x := by
  have h_posPart_eq : ∀ i, posPart (n := n) x i = x i := by
    intro i
    unfold posPart
    rw [max_eq_left (h_nonneg i)]
  have h_sumPos_eq : sumPos (n := n) x = 1 := by
    unfold sumPos
    have : ∀ i : Fin (n + 1), posPart (n := n) x i = x i := h_posPart_eq
    simp_rw [this, h_sum]
  have h_denom_eq : denom (n := n) x = 1 := by
    unfold denom
    rw [h_sumPos_eq]
    exact max_eq_right (le_refl (1 : ℝ))
  have h_slack_zero : 1 - sumPos (n := n) x / denom (n := n) x = 0 := by
    rw [h_sumPos_eq, h_denom_eq, div_one, sub_self]
  funext i
  simp only [retractFun, h_posPart_eq i, h_denom_eq, h_sumPos_eq, div_one, sub_self]
  simp

/-- Direct `DeltaGeneratedSpace` instance for the new finite simplex
`Convexity.StdSimplex ℝ (Fin (n + 1))`, as a retract of Euclidean space.

Proved directly from the existing `retractFun` retraction via
`Topology.IsQuotientMap.isGeneratedBy`. Finite-index (`ℝ`, `Fin (n + 1)`) only;
do not generalize. -/
noncomputable instance convexStdSimplex_finSucc :
    DeltaGeneratedSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) := by
  let incl : Convexity.StdSimplex ℝ (Fin (n + 1)) → (Fin (n + 1) → ℝ) :=
    fun t => (t.weights : Fin (n + 1) → ℝ)
  let retr : (Fin (n + 1) → ℝ) → Convexity.StdSimplex ℝ (Fin (n + 1)) :=
    fun x =>
      { weights := Finsupp.equivFunOnFinite.symm (retractFun x)
        nonneg m := by simpa using retractFun_nonneg x m
        total := by simpa [Finsupp.sum_fintype] using sum_retractFun x }
  have hEmb := Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))
  have hcont_incl : Continuous incl := hEmb.continuous
  have hcont_retr : Continuous retr := by
    apply hEmb.continuous_iff.mpr
    have hsim :
        ((fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
            (t.weights : Fin (n + 1) → ℝ)) ∘ retr) =
          (fun x : Fin (n + 1) → ℝ => retractFun x) := by
      funext x i
      rfl
    rw [hsim]
    exact continuous_retractFun
  have hleft : Function.LeftInverse retr incl := by
    intro t
    have hfix : retractFun (incl t) = incl t :=
      retractFun_fix_of_nonneg_sum _ (fun i => t.weights_nonneg i) t.total_of_fintype
    apply Convexity.StdSimplex.ext
    change Finsupp.equivFunOnFinite.symm (retractFun (incl t)) = t.weights
    rw [hfix]
    have hincl : incl t = (t.weights : Fin (n + 1) → ℝ) := rfl
    rw [hincl]
    simp
  have hquot : IsQuotientMap retr :=
    IsQuotientMap.of_inverse hcont_incl hcont_retr hleft
  exact hquot.isGeneratedBy

end DeltaGeneratedSpace
