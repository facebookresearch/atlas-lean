/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.GenericGroup.Symbolic
public import CSLibExt.Crypto.Framework.Advantage
public import Mathlib.Algebra.Field.ZMod

/-!
# Shoup's generic-group lower bound, counting form

Counting and probability bounds for discrete logarithm in the generic group
model of `CSLibExt.Crypto.Framework.GenericGroup.Symbolic`, following Shoup's
proof (Victor Shoup, *Lower Bounds for Discrete Logarithms and Related
Problems*, revised version, Section 2, Theorem 1 and Lemma 1 in degree 1).
Distinct affine forms over `ZMod q` agree at at most one point; a union bound
over the forms a decision tree mentions bounds its success set by
`(m + 3).choose 2 + 1` secrets for every fixed encoding, and averaging the
encoding gives the game bound `(((m + 3).choose 2 + 1 : ℕ) : ℝ) / q`, hence
the `O(m²/q)` shape `((m : ℝ) + 3) ^ 2 / q`. The explicit constant is derived
from Shoup's proof game; Shoup states the bound as `O(m²/p)` with no explicit
constant.

The model is the Nechaev-style symbolic one of the imported module: prime
order `q`, labels `ZMod q`, encodings are permutations of the labels, the
adversary is a deterministic decision tree, group-operation queries are
counted and equality tests are free. This is not Shoup's bitstring encoding
model, and composite orders and randomized adversaries are out of scope.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup

open Finset

/-- Distinct affine forms agree at no more than one point of `ZMod q`, `q` prime (Shoup, Lemma 1,
degree 1). -/
theorem affEval_eq_card_le_one {q : ℕ} [Fact q.Prime] {u v : Aff q} (huv : u ≠ v) :
    (univ.filter fun x : ZMod q => affEval x u = affEval x v).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun x hx y hy => ?_
  rw [Finset.mem_filter] at hx hy
  have hx' : u.1 + u.2 * x = v.1 + v.2 * x := hx.2
  have hy' : u.1 + u.2 * y = v.1 + v.2 * y := hy.2
  by_cases h2 : u.2 = v.2
  · exfalso
    apply huv
    rw [h2] at hx'
    exact Prod.ext (add_right_cancel hx') h2
  · have hne : u.2 - v.2 ≠ 0 := sub_ne_zero.mpr h2
    have hxy : (u.2 - v.2) * x = (u.2 - v.2) * y := by linear_combination hx' - hy'
    exact mul_left_cancel₀ hne hxy

/-- Two distinct affine forms agree at a uniform point with probability at most `1/q`. -/
theorem affEval_agree_winProb_le {q : ℕ} [Fact q.Prime] {u v : Aff q} (huv : u ≠ v) :
    winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod q)).map fun x =>
      decide (affEval x u = affEval x v)) ≤ 1 / q := by
  rw [winProb_map_uniform, ZMod.card]
  simp only [decide_eq_true_eq]
  gcongr
  exact_mod_cast affEval_eq_card_le_one huv

/-- Union bound: points where two distinct forms of `l` agree number at most `C(|l|, 2)`. -/
theorem collision_card_le {q : ℕ} [Fact q.Prime] (l : List (Aff q)) :
    (univ.filter fun x : ZMod q =>
      ∃ u ∈ l, ∃ v ∈ l, u ≠ v ∧ affEval x u = affEval x v).card ≤ l.length.choose 2 := by
  induction l with
  | nil => simp
  | cons w t ih =>
    classical
    have hsub : (univ.filter fun x : ZMod q =>
        ∃ u ∈ w :: t, ∃ v ∈ w :: t, u ≠ v ∧ affEval x u = affEval x v) ⊆
        (univ.filter fun x : ZMod q =>
          ∃ u ∈ t, ∃ v ∈ t, u ≠ v ∧ affEval x u = affEval x v) ∪
        t.toFinset.biUnion (fun v => univ.filter fun x : ZMod q =>
          w ≠ v ∧ affEval x w = affEval x v) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at hx
      obtain ⟨u, hu, v, hv, hne, heq⟩ := hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, List.mem_toFinset]
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact absurd rfl hne
      · exact Or.inr ⟨v, hv, hne, heq⟩
      · exact Or.inr ⟨u, hu, Ne.symm hne, heq.symm⟩
      · exact Or.inl ⟨u, hu, v, hv, hne, heq⟩
    have hpair : ∀ v ∈ t.toFinset, (univ.filter fun x : ZMod q =>
        w ≠ v ∧ affEval x w = affEval x v).card ≤ 1 := by
      intro v _
      by_cases hwv : w = v
      · simp [hwv]
      · simpa [hwv] using affEval_eq_card_le_one hwv
    have hbu : (t.toFinset.biUnion (fun v => univ.filter fun x : ZMod q =>
        w ≠ v ∧ affEval x w = affEval x v)).card ≤ t.length := by
      calc _ ≤ ∑ v ∈ t.toFinset, (univ.filter fun x : ZMod q =>
              w ≠ v ∧ affEval x w = affEval x v).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ t.toFinset, 1 := Finset.sum_le_sum hpair
        _ = t.toFinset.card := by simp
        _ ≤ t.length := List.toFinset_card_le t
    have key : (t.length + 1).choose 2 = t.length.choose 1 + t.length.choose 2 :=
      Nat.choose_succ_succ' t.length 1
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ t.length.choose 2 + t.length := Nat.add_le_add ih hbu
      _ = (w :: t).length.choose 2 := by
          rw [List.length_cons, key, Nat.choose_one_right]
          omega

/-- Counting form, every fixed encoding: secrets on which an `m`-query tree succeeds. -/
theorem dlog_success_card_le {q : ℕ} [Fact q.Prime] (enc : Equiv.Perm (ZMod q))
    (A : GTree (ZMod q) 3) {m : ℕ} (hm : GTree.numQueries A ≤ m) :
    (univ.filter fun x : ZMod q =>
      GTree.eval (oracleOf enc) (dlogInputs enc x) A = x).card ≤ (m + 3).choose 2 + 1 := by
  classical
  have hsub : (univ.filter fun x : ZMod q =>
      GTree.eval (oracleOf enc) (dlogInputs enc x) A = x) ⊆
      {GTree.eval affOracle (dlogForms q) A} ∪
        (univ.filter fun x : ZMod q => ∃ u ∈ symLabels (q := q) A,
          ∃ v ∈ symLabels (q := q) A, u ≠ v ∧ affEval x u = affEval x v) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases dlog_success_imp enc x A hx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr h.symm)
    · exact Finset.mem_union_right _ (by simpa using h)
  have hlen : (symLabels (q := q) A).length ≤ m + 3 := by
    have := length_symLabels_le (q := q) A
    omega
  have hch := Nat.choose_le_choose 2 hlen
  have hcol := collision_card_le (symLabels (q := q) A)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ (m + 3).choose 2 + 1 := by
        rw [Finset.card_singleton]
        omega

/-- Uniform secret, every fixed encoding. -/
theorem dlog_winProb_le {q : ℕ} [Fact q.Prime] (enc : Equiv.Perm (ZMod q))
    (A : GTree (ZMod q) 3) {m : ℕ} (hm : GTree.numQueries A ≤ m) :
    winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod q)).map fun x =>
      decide (GTree.eval (oracleOf enc) (dlogInputs enc x) A = x)) ≤
      (((m + 3).choose 2 + 1 : ℕ) : ℝ) / q := by
  rw [winProb_map_uniform, ZMod.card]
  simp only [decide_eq_true_eq]
  gcongr
  exact_mod_cast dlog_success_card_le enc A hm

/-- Shoup's probability space: uniform encoding (a permutation of the labels) and uniform
secret; outcome `true` iff the tree outputs the secret. -/
noncomputable def genericDlogGame (q : ℕ) [Fact (1 < q)] (A : GTree (ZMod q) 3) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (ZMod q) × ZMod q)).map fun ω =>
    decide (GTree.eval (oracleOf ω.1) (dlogInputs ω.1 ω.2) A = ω.2)

/-- Shoup Theorem 1-style bound with the derived explicit constant. -/
theorem genericDlog_winProb_le {q : ℕ} [Fact q.Prime] (A : GTree (ZMod q) 3) {m : ℕ}
    (hm : GTree.numQueries A ≤ m) :
    winProb (genericDlogGame q A) ≤ (((m + 3).choose 2 + 1 : ℕ) : ℝ) / q := by
  classical
  rw [genericDlogGame, winProb_map_uniform, Fintype.card_prod, ZMod.card]
  simp only [decide_eq_true_eq]
  have hcard : (univ.filter fun ω : Equiv.Perm (ZMod q) × ZMod q =>
      GTree.eval (oracleOf ω.1) (dlogInputs ω.1 ω.2) A = ω.2).card ≤
      Fintype.card (Equiv.Perm (ZMod q)) * ((m + 3).choose 2 + 1) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    calc _ ≤ ∑ _enc : Equiv.Perm (ZMod q), ((m + 3).choose 2 + 1) := by
          refine Finset.sum_le_sum fun enc _ => ?_
          rw [← Finset.card_filter]
          exact dlog_success_card_le enc A hm
      _ = _ := by simp
  have hP : 0 < Fintype.card (Equiv.Perm (ZMod q)) := Fintype.card_pos
  have hq : 0 < q := (Fact.out : q.Prime).pos
  rw [div_le_div_iff₀ (by exact_mod_cast Nat.mul_pos hP hq) (by exact_mod_cast hq)]
  have hcardR : ((univ.filter fun ω : Equiv.Perm (ZMod q) × ZMod q =>
      GTree.eval (oracleOf ω.1) (dlogInputs ω.1 ω.2) A = ω.2).card : ℝ) ≤
      (Fintype.card (Equiv.Perm (ZMod q)) : ℝ) * (((m + 3).choose 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hqR : (0 : ℝ) ≤ q := by positivity
  calc _ ≤ (Fintype.card (Equiv.Perm (ZMod q)) : ℝ) * (((m + 3).choose 2 + 1 : ℕ) : ℝ) * q :=
        mul_le_mul_of_nonneg_right hcardR hqR
    _ = _ := by push_cast; ring

/-- The `O(m²/q)` shape of Shoup's Theorem 1. -/
theorem genericDlog_winProb_le_sq {q : ℕ} [Fact q.Prime] (A : GTree (ZMod q) 3) {m : ℕ}
    (hm : GTree.numQueries A ≤ m) :
    winProb (genericDlogGame q A) ≤ ((m : ℝ) + 3) ^ 2 / q := by
  refine (genericDlog_winProb_le A hm).trans ?_
  have h : (m + 3).choose 2 + 1 ≤ (m + 3) ^ 2 := by
    rw [Nat.choose_two_right]
    have h1 : (m + 3) * (m + 3 - 1) / 2 ≤ (m + 3) * (m + 3 - 1) := Nat.div_le_self _ _
    have h2 : m + 3 - 1 = m + 2 := by omega
    rw [h2] at h1 ⊢
    nlinarith
  gcongr
  exact_mod_cast h

end Cslib.Crypto.Framework.GenericGroup
