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
Problems*, revised version, Section 2, Theorem 1 and Lemma 1 in degree at most 1).
For a prime `q`, distinct affine forms over `ZMod q` agree at at most one
point; a union bound over the forms a decision tree mentions bounds its
success set by `(m + 3).choose 2 + 1` secrets for every fixed encoding, and
averaging the encoding gives the game bound
`(((m + 3).choose 2 + 1 : ℕ) : ℝ) / q`, hence the explicit bound
`((m : ℝ) + 3) ^ 2 / q`, of Shoup's `O(m²/p)` shape. The explicit constant is
derived from Shoup's proof game; Shoup states the bound as `O(m²/p)` with no
explicit constant.

The model is the Nechaev-style symbolic one of the imported module: prime
order `q`, labels `ZMod q`, encodings are permutations of the labels, the
adversary is a deterministic decision tree, group-operation queries are
counted and equality tests are free. A query is one multiplication or one
inversion, where Shoup's oracle computes a sum or a difference in one query.
The tree receives three labels, `enc 0`, `enc 1` and `enc x`; Shoup's
algorithm receives only the generator's and the target's, so the identity
label adds one form: the tree's list has at most `m + 3` forms where Shoup's
game has `m + 2`. This is not Shoup's bitstring encoding model, and composite
orders and randomized adversaries are out of scope.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup

open Finset

/-- **Distinct affine forms agree at most once.** Let `q` be prime, and read a pair `u = (a, b)`
over `ZMod q` as the affine form `x ↦ a + b * x` (`affEval`). Two distinct forms `u ≠ v` take the
same value at no more than one point `x` of `ZMod q`.

Source: V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of
the Eurocrypt 1997 paper, Section 2, Lemma 1, in one variable and degree at most 1 over the
prime field. -/
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

/-- **Agreement probability of two affine forms.** Let `q` be prime and let `u ≠ v` be affine
forms over `ZMod q` (`affEval`). For `x` uniform in `ZMod q`, the probability that `u` and `v`
take the same value at `x` is at most `1 / q`.

Source: V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of
the Eurocrypt 1997 paper, Section 2, Lemma 1, in one variable and degree at most 1 over the
prime field. -/
theorem affEval_agree_winProb_le {q : ℕ} [Fact q.Prime] {u v : Aff q} (huv : u ≠ v) :
    winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod q)).map fun x =>
      decide (affEval x u = affEval x v)) ≤ 1 / q := by
  rw [winProb_map_uniform, ZMod.card]
  simp only [decide_eq_true_eq]
  gcongr
  exact_mod_cast affEval_eq_card_le_one huv

/-- **Collision count of a list of affine forms.** Let `q` be prime and let `l` be a list of
affine forms over `ZMod q` (`affEval`). At most `l.length.choose 2` points `x` of `ZMod q` make two
distinct forms of `l` take the same value at `x`.

Source: V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of
the Eurocrypt 1997 paper, Section 2, proof of Theorem 1. -/
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

/-- **Generic discrete-logarithm success count, fixed encoding.** Let `q` be prime, let `enc` be
an encoding (a permutation of `ZMod q`), and let `A` be a decision tree on three labels with leaves
in `ZMod q` that makes at most `m` group operations on every path (`GTree.numQueries A ≤ m`). Run
on the labels `enc 0`, `enc 1` and `enc x` with the oracle `oracleOf enc`, `A` outputs `x` for at
most `(m + 3).choose 2 + 1` secrets `x ∈ ZMod q`.

Source: V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of
the Eurocrypt 1997 paper, Section 2, proof of Theorem 1. -/
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

/-- **Generic discrete-logarithm bound, fixed encoding.** Let `q` be prime, let `enc` be an
encoding (a permutation of `ZMod q`), and let `A` be a decision tree on three labels with leaves in
`ZMod q` that makes at most `m` group operations on every path (`GTree.numQueries A ≤ m`). For a
uniform secret `x ∈ ZMod q`, `A`, run on the labels `enc 0`, `enc 1` and `enc x` with the oracle
`oracleOf enc`, outputs `x` with probability at most `((m + 3).choose 2 + 1) / q`.

Source: V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of
the Eurocrypt 1997 paper, Section 2, proof of Theorem 1. -/
theorem dlog_winProb_le {q : ℕ} [Fact q.Prime] (enc : Equiv.Perm (ZMod q))
    (A : GTree (ZMod q) 3) {m : ℕ} (hm : GTree.numQueries A ≤ m) :
    winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod q)).map fun x =>
      decide (GTree.eval (oracleOf enc) (dlogInputs enc x) A = x)) ≤
      (((m + 3).choose 2 + 1 : ℕ) : ℝ) / q := by
  rw [winProb_map_uniform, ZMod.card]
  simp only [decide_eq_true_eq]
  gcongr
  exact_mod_cast dlog_success_card_le enc A hm

/-- **Generic discrete-logarithm game.** Let `q > 1` and let `A` be a decision tree on three
labels with leaves in `ZMod q`. The game draws an encoding `enc` (a permutation of `ZMod q`) and a
secret `x ∈ ZMod q` uniformly and independently, runs `A` on the labels `enc 0`, `enc 1` and
`enc x` (of the identity, the generator and the target) with the oracle `oracleOf enc`, and
outputs `true` when `A` outputs `x`. Shoup's algorithm receives only the generator's and the
target's labels; the identity label gives the tree one more form than Shoup's game, hence the
`m + 3` in the bounds on this game where Shoup's proof has `m + 2`.

Source: V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of
the Eurocrypt 1997 paper, Section 2, Theorem 1. -/
noncomputable def genericDlogGame (q : ℕ) [Fact (1 < q)] (A : GTree (ZMod q) 3) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (ZMod q) × ZMod q)).map fun ω =>
    decide (GTree.eval (oracleOf ω.1) (dlogInputs ω.1 ω.2) A = ω.2)

/-- **Generic discrete-logarithm bound, uniform encoding.** Let `q` be prime and let `A` be a
decision tree that is given the labels of `0`, `1` and the secret `x`, tests labels only for
equality, and makes at most `m` group operations on every path (`GTree.numQueries A ≤ m`). For a
uniform encoding (a permutation of `ZMod q`) and a uniform secret `x`, `A` outputs `x` with
probability at most `((m + 3).choose 2 + 1) / q` (`genericDlogGame`).

Source: V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of
the Eurocrypt 1997 paper, Section 2, Theorem 1, here for prime order in Nechaev's
model. -/
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

/-- **Generic discrete-logarithm bound, squared form.** Let `q` be prime and let `A` be a
decision tree that is given the labels of `0`, `1` and the secret `x`, tests labels only for
equality, and makes at most `m` group operations on every path (`GTree.numQueries A ≤ m`). For a
uniform encoding (a permutation of `ZMod q`) and a uniform secret `x`, `A` outputs `x` with
probability at most `(m + 3) ^ 2 / q` (`genericDlogGame`), an explicit bound of Shoup's
`O(m^2/p)` shape.

Source: V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of
the Eurocrypt 1997 paper, Section 2, Theorem 1, here for prime order in Nechaev's
model. -/
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
