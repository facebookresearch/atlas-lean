/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Antichain
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The weak order on the symmetric group is Sperner

This file proves `weakOrderSperner_holds`: for every `n`, no antichain of the weak order on the
permutations of `Fin n` has more elements than the largest rank level, the rank of a permutation
being its number of inversions. J. Cooper's problem list asks whether the weak order on `S_n` (the
"inversion" poset) is Sperner; C. Gaetz and Y. Gao proved that it is, and even that it is strongly
Sperner.

Source: J. Cooper, Combinatorial Problems I Like (2020 snapshot), Matroids, Lattices, and Posets,
item 39, https://people.math.sc.edu/cooper/combprob.html. UnsolvedMath record UM-03100039
(`AMR-030-0039`), dataset ulamai/UnsolvedMath v1.8.0.

The weak order compares inversion sets, `σ ≤ τ` iff `Inv(σ) ⊆ Inv(τ)`, with inversions taken as
pairs of positions (the left weak order; the right weak order, by value pairs, is isomorphic via `σ
↦ σ⁻¹`, so the Sperner property is the same). It is graded by the number of inversions; Sperner
means that no antichain is larger than the largest rank level. The target is stated for every `n`.

## Proof outline

The proof follows Gaetz and Gao. It works with the right weak order on the permutations `w` of
`Fin n`, in which `w * swap p (p + 1)` covers `w` when `w p < w (p + 1)`; inverting permutations
turns it into the order `weakLE` of the statement. On the rational functions on permutations:

* `U` sends `w` to the sum of its covers `w * swap p (p + 1)`, with weight `p + 1` (positions
  counted from `1`);
* `D` sends `w` to the sum of the permutations `w * swap i j` that it covers in the Bruhat order
  (`i < j`, `w j < w i`, and no position between `i` and `j` holds a value between `w j` and
  `w i`), with weight `2b + 1`, where `b` counts the positions `k > j` with `w j < w k < w i`. On a
  Bruhat cover this is Gaetz and Gao's weight `2(w i - w j - a) - 1`, where `a` counts the
  positions `k < i` with `w j < w k < w i`;
* `H` multiplies `w` by `2ℓ(w) - N`, where `ℓ(w)` is the number of inversions of `w` and `N` the
  number of pairs of positions.

Then `[U, D] = H`. Off the diagonal, the two-step paths of `UD` and of `DU` cancel in pairs, in
five cases according to how the transposition `swap i j` meets the adjacent pair `{p, p + 1}`; on
the diagonal, an Abel summation of the signs of the pairs of positions gives `2ℓ(w) - N`. The
`sl₂` argument then shows that `U` is injective on the permutations of rank `k` when `2k < N`,
and, applied to the transposed operators, that the transpose of `U` is injective on rank `k` when
`2k > N`. By Hall's theorem, each rank below the middle rank `⌊N / 2⌋` maps injectively into the
next rank along covers, and each rank above it maps injectively into the previous rank. Following
these maps to the middle rank sends distinct elements of an antichain to distinct permutations of
the middle rank.

## References

* C. Gaetz and Y. Gao, A combinatorial sl₂-action and the Sperner property for the weak order,
  Proc. Amer. Math. Soc. 148 (2020), 1-7, https://doi.org/10.1090/proc/14655; arXiv:1811.05501.
* J. Cooper, Combinatorial Problems I Like (2020 snapshot), Matroids, Lattices, and Posets,
  item 39, https://people.math.sc.edu/cooper/combprob.html.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.WeakOrderSpernerAMR30Problem0039Wanted

/-- **Inversion set of a permutation.** For a permutation $\sigma$ of $\{0, \dots, n-1\}$, the
inversion set of $\sigma$ is the set of pairs of positions $(i, j)$ with $i < j$ and
$\sigma(j) < \sigma(i)$. -/
def inversions {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ σ p.2 < σ p.1

/-- **Weak order on the symmetric group.** For permutations $\sigma$ and $\tau$ of
$\{0, \dots, n-1\}$, $\sigma \le \tau$ in the weak order when the inversion set of $\sigma$ (its
pairs of positions $(i, j)$ with $i < j$ and $\sigma(j) < \sigma(i)$) is contained in the inversion
set of $\tau$. -/
def weakLE {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : Prop :=
  inversions σ ⊆ inversions τ

/-- **Sperner property of the weak order.** This is the statement that for every $n$ and every
antichain $A$ of the weak order on the permutations of $\{0, \dots, n-1\}$ (where $\sigma \le \tau$
when the inversion set of $\sigma$ is contained in that of $\tau$), there is a $k$ such that $A$
has at most as many elements as there are permutations with exactly $k$ inversions. Equivalently,
no antichain is larger than the largest rank level, the rank of a permutation being its number of
inversions. -/
def weakOrderSperner : Prop :=
  ∀ (n : ℕ) (A : Finset (Equiv.Perm (Fin n))), IsAntichain weakLE (A : Set (Equiv.Perm (Fin n))) →
    ∃ k : ℕ, A.card ≤
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => (inversions σ).card = k).card

open Equiv Finset Matrix

section WeakOrder

variable {n : ℕ}

/-! ### Swapping two adjacent positions -/

/-- `swap p q` with `q = p + 1` preserves the order of every pair of positions other than
`(p, q)` and `(q, p)`. -/
private lemma swap_lt_swap_iff {p q : Fin n} (hq : (q : ℕ) = p + 1) {a b : Fin n}
    (h1 : ¬ (a = p ∧ b = q)) (h2 : ¬ (a = q ∧ b = p)) :
    swap p q a < swap p q b ↔ a < b := by
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  rw [Fin.lt_def, Fin.lt_def]
  rcases eq_or_ne a p with rfl | hap
  · rw [swap_apply_left]
    rcases eq_or_ne b a with rfl | hbp
    · simp
    · have hbq : b ≠ q := fun h => h1 ⟨rfl, h⟩
      rw [swap_apply_of_ne_of_ne hbp hbq]
      have := Fin.val_ne_of_ne hbq
      omega
  rcases eq_or_ne a q with rfl | haq
  · rw [swap_apply_right]
    rcases eq_or_ne b a with rfl | hbq
    · simp
    · have hbp : b ≠ p := fun h => h2 ⟨rfl, h⟩
      rw [swap_apply_of_ne_of_ne hbp hbq]
      have := Fin.val_ne_of_ne hbp
      omega
  rw [swap_apply_of_ne_of_ne hap haq]
  rcases eq_or_ne b p with rfl | hbp
  · rw [swap_apply_left]
    have := Fin.val_ne_of_ne haq
    omega
  rcases eq_or_ne b q with rfl | hbq
  · rw [swap_apply_right]
    have := Fin.val_ne_of_ne hap
    omega
  rw [swap_apply_of_ne_of_ne hbp hbq]

/-- Relabelling by a permutation does not change the size of a filter. -/
private lemma card_filter_equiv {α : Type*} [Fintype α] (e : α ≃ α) (P : α → Prop)
    [DecidablePred P] : #{x | P (e x)} = #{x | P x} := by
  simp only [card_filter]
  exact Equiv.sum_comp e (fun x => if P x then 1 else 0)

/-- Swapping two adjacent positions holding an ascent adds exactly one inversion. -/
private lemma card_inversions_mul_swap (v : Perm (Fin n)) {p q : Fin n} (hq : (q : ℕ) = p + 1)
    (hv : v p < v q) : #(inversions (v * swap p q)) = #(inversions v) + 1 := by
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  have hlt : p < q := by rw [Fin.lt_def]; omega
  set s := swap p q with hs
  have h1 : #(inversions (v * s)) = #{x : Fin n × Fin n | s x.1 < s x.2 ∧ v x.2 < v x.1} := by
    rw [← card_filter_equiv (s.prodCongr s)]
    unfold inversions
    congr 1
    apply Finset.filter_congr
    intro x _
    simp [hs, swap_apply_self]
  rw [h1, ← card_insert_of_notMem (s := inversions v) (a := (q, p))]
  · congr 1
    ext ⟨a, b⟩
    simp only [inversions, mem_filter, mem_univ, true_and, mem_insert, Prod.mk.injEq]
    by_cases hab : a = p ∧ b = q
    · obtain ⟨rfl, rfl⟩ := hab
      simp [hs, swap_apply_left, swap_apply_right, hpq, hpq.symm, not_lt.2 hlt.le, hv.not_gt]
    by_cases hba : a = q ∧ b = p
    · obtain ⟨rfl, rfl⟩ := hba
      simp [hs, swap_apply_left, swap_apply_right, hlt, hv]
    rw [swap_lt_swap_iff hq hab hba]
    tauto
  · simp [inversions, not_lt.2 hlt.le]


/-! ### The weights of the two operators -/

/-- Weight of the weak-order cover `w ⋖ w * swap p q`, for adjacent positions `q = p + 1`. -/
private def upWt (w : Perm (Fin n)) (p q : Fin n) : ℚ :=
  if (q : ℕ) = p + 1 ∧ w p < w q then ((p : ℕ) + 1 : ℚ) else 0

/-- Weight of the Bruhat cover `w * swap i j ⋖ w`. -/
private def downWt (w : Perm (Fin n)) (i j : Fin n) : ℚ :=
  if i < j ∧ w j < w i ∧ ∀ k, i < k → k < j → ¬ (w j < w k ∧ w k < w i) then
    2 * (#{k | j < k ∧ w j < w k ∧ w k < w i} : ℚ) + 1
  else 0

/-- Two products of guarded weights agree when the guards are equivalent and the weights agree
under them. -/
private lemma ite_mul_ite_eq {U₁ C₁ U₂ C₂ : Prop} [Decidable U₁] [Decidable C₁] [Decidable U₂]
    [Decidable C₂] (a b₁ b₂ : ℚ) (h : U₁ ∧ C₁ ↔ C₂ ∧ U₂) (hb : U₁ ∧ C₁ → b₁ = b₂) :
    (if U₁ then a else 0) * (if C₁ then b₁ else 0) =
      (if C₂ then b₂ else 0) * (if U₂ then a else 0) := by
  by_cases h₁ : U₁ ∧ C₁
  · have h₂ := h.1 h₁
    rw [ite_eq_left h₁.1, ite_eq_left h₁.2, ite_eq_left h₂.1, ite_eq_left h₂.2, hb h₁,
      mul_comm]
  · have h₂ : ¬ (C₂ ∧ U₂) := fun h₂ => h₁ (h.2 h₂)
    rw [not_and_or] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [h₁, h₂]

/-! ### Cancellation of the off-diagonal paths -/

/-- Case where the transposition `swap i j` has support disjoint from the adjacent pair
`{p, q}`. -/
private lemma case_disjoint (w : Perm (Fin n)) {p q i j : Fin n} (hq : (q : ℕ) = p + 1)
    (hip : i ≠ p) (hiq : i ≠ q) (hjp : j ≠ p) (hjq : j ≠ q) :
    upWt (w * swap i j) p q * downWt w i j = downWt (w * swap p q) i j * upWt w p q := by
  have hs : ∀ k, (swap p q k < j ↔ k < j) ∧ (i < swap p q k ↔ i < k) ∧
      (j < swap p q k ↔ j < k) := by
    intro k
    refine ⟨?_, ?_, ?_⟩
    · have := swap_lt_swap_iff hq (a := k) (b := j) (fun h => hjq h.2) (fun h => hjp h.2)
      rwa [swap_apply_of_ne_of_ne hjp hjq] at this
    · have := swap_lt_swap_iff hq (a := i) (b := swap p q k) (fun h => hip h.1)
        (fun h => hiq h.1)
      rw [swap_apply_of_ne_of_ne hip hiq, swap_apply_self] at this
      exact this.symm
    · have := swap_lt_swap_iff hq (a := j) (b := swap p q k) (fun h => hjp h.1)
        (fun h => hjq h.1)
      rw [swap_apply_of_ne_of_ne hjp hjq, swap_apply_self] at this
      exact this.symm
  unfold upWt downWt
  simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hip.symm hjp.symm,
    swap_apply_of_ne_of_ne hiq.symm hjq.symm, swap_apply_of_ne_of_ne hip hiq,
    swap_apply_of_ne_of_ne hjp hjq]
  refine ite_mul_ite_eq _ _ _ ?_ ?_
  · have hforall : (∀ k, i < k → k < j → ¬(w j < w (swap p q k) ∧ w (swap p q k) < w i)) ↔
        (∀ k, i < k → k < j → ¬(w j < w k ∧ w k < w i)) := by
      constructor
      · intro h k hik hkj
        have := h (swap p q k) ((hs k).2.1.2 hik) ((hs k).1.2 hkj)
        rwa [swap_apply_self] at this
      · intro h k hik hkj
        exact h (swap p q k) ((hs k).2.1.2 hik) ((hs k).1.2 hkj)
    rw [hforall]
    tauto
  · intro _
    have e1 := card_filter_equiv (swap p q) (fun x => j < swap p q x ∧ w j < w x ∧ w x < w i)
    simp only [swap_apply_self] at e1
    have hc : #{k | j < k ∧ w j < w k ∧ w k < w i} =
        #{x | j < swap p q x ∧ w j < w x ∧ w x < w i} := by
      congr 1
      apply filter_congr
      intro x _
      rw [(hs x).2.2]
    rw [e1, hc]


/-- Case `i = p`: the transposition `swap p j` with `q < j`. -/
private lemma case_left_left (w : Perm (Fin n)) {p q j : Fin n} (hq : (q : ℕ) = p + 1)
    (hqj : q < j) :
    upWt (w * swap p j) p q * downWt w p j = downWt (w * swap p q) q j * upWt w p q := by
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  have hlt : p < q := by rw [Fin.lt_def]; omega
  have hpj : p < j := hlt.trans hqj
  have hjp : j ≠ p := ne_of_gt hpj
  have hjq : j ≠ q := ne_of_gt hqj
  have hsk : ∀ k, q < k → swap p q k = k := fun k hk =>
    swap_apply_of_ne_of_ne (ne_of_gt (hlt.trans hk)) (ne_of_gt hk)
  unfold upWt downWt
  simp only [Perm.mul_apply, swap_apply_left, swap_apply_right,
    swap_apply_of_ne_of_ne hpq.symm hjq.symm, swap_apply_of_ne_of_ne hjp hjq]
  refine ite_mul_ite_eq _ _ _ ?_ ?_
  · constructor
    · rintro ⟨⟨_, hjq'⟩, _, hjp', hC⟩
      have hpq' : w p < w q := by
        rcases lt_trichotomy (w p) (w q) with h | h | h
        · exact h
        · exact absurd (w.injective h) hpq
        · exact absurd ⟨hjq', h⟩ (hC q hlt hqj)
      refine ⟨⟨hqj, hjp', fun k hqk hkj => ?_⟩, hq, hpq'⟩
      rw [hsk k hqk]
      exact hC k (hlt.trans hqk) hkj
    · rintro ⟨⟨_, hjp', hC⟩, _, hpq'⟩
      refine ⟨⟨hq, hjp'.trans hpq'⟩, hpj, hjp', fun k hpk hkj => ?_⟩
      rcases eq_or_ne k q with rfl | hkq
      · exact fun h => absurd h.2 (not_lt.2 hpq'.le)
      · have hqk : q < k := by
          rw [Fin.lt_def] at hpk ⊢; have := Fin.val_ne_of_ne hkq; omega
        have := hC k hqk hkj
        rwa [hsk k hqk] at this
  · intro _
    have : (univ.filter fun k => j < k ∧ w j < w k ∧ w k < w p) =
        univ.filter fun k => j < k ∧ w j < w (swap p q k) ∧ w (swap p q k) < w p := by
      apply filter_congr; intro k _
      by_cases hjk : j < k
      · rw [hsk k (hqj.trans hjk)]
      · simp [hjk]
    rw [this]

/-- Case `i = q`: the transposition `swap q j` with `q < j`. -/
private lemma case_right_left (w : Perm (Fin n)) {p q j : Fin n} (hq : (q : ℕ) = p + 1)
    (hqj : q < j) :
    upWt (w * swap q j) p q * downWt w q j = downWt (w * swap p q) p j * upWt w p q := by
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  have hlt : p < q := by rw [Fin.lt_def]; omega
  have hpj : p < j := hlt.trans hqj
  have hjp : j ≠ p := ne_of_gt hpj
  have hjq : j ≠ q := ne_of_gt hqj
  have hsk : ∀ k, q < k → swap p q k = k := fun k hk =>
    swap_apply_of_ne_of_ne (ne_of_gt (hlt.trans hk)) (ne_of_gt hk)
  unfold upWt downWt
  simp only [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hpq hjp.symm,
    swap_apply_of_ne_of_ne hjp hjq]
  refine ite_mul_ite_eq _ _ _ ?_ ?_
  · constructor
    · rintro ⟨⟨_, hpj'⟩, _, hjq', hC⟩
      refine ⟨⟨hpj, hjq', fun k hpk hkj => ?_⟩, hq, hpj'.trans hjq'⟩
      rcases eq_or_ne k q with rfl | hkq
      · rw [swap_apply_right]; exact fun h => absurd h.1 (not_lt.2 hpj'.le)
      · have hqk : q < k := by
          rw [Fin.lt_def] at hpk ⊢; have := Fin.val_ne_of_ne hkq; omega
        rw [hsk k hqk]; exact hC k hqk hkj
    · rintro ⟨⟨_, hjq', hC⟩, _, hpq'⟩
      have hpj' : w p < w j := by
        have := hC q hlt hqj
        rw [swap_apply_right] at this
        rcases lt_trichotomy (w p) (w j) with h | h | h
        · exact h
        · exact absurd (w.injective h) hjp.symm
        · exact absurd ⟨h, hpq'⟩ this
      refine ⟨⟨hq, hpj'⟩, hqj, hjq', fun k hqk hkj => ?_⟩
      have := hC k (hlt.trans hqk) hkj
      rwa [hsk k hqk] at this
  · intro _
    have : (univ.filter fun k => j < k ∧ w j < w k ∧ w k < w q) =
        univ.filter fun k => j < k ∧ w j < w (swap p q k) ∧ w (swap p q k) < w q := by
      apply filter_congr; intro k _
      by_cases hjk : j < k
      · rw [hsk k (hqj.trans hjk)]
      · simp [hjk]
    rw [this]

/-- Case `j = p`: the transposition `swap i p` with `i < p`. -/
private lemma case_left_right (w : Perm (Fin n)) {p q i : Fin n} (hq : (q : ℕ) = p + 1)
    (hip : i < p) :
    upWt (w * swap i p) p q * downWt w i p = downWt (w * swap p q) i q * upWt w p q := by
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  have hlt : p < q := by rw [Fin.lt_def]; omega
  have hiq' : i < q := hip.trans hlt
  have hi_p : i ≠ p := ne_of_lt hip
  have hi_q : i ≠ q := ne_of_lt hiq'
  have hsk : ∀ k, k < p → swap p q k = k := fun k hk =>
    swap_apply_of_ne_of_ne (ne_of_lt hk) (ne_of_lt (hk.trans hlt))
  have hsk' : ∀ k, q < k → swap p q k = k := fun k hk =>
    swap_apply_of_ne_of_ne (ne_of_gt (hlt.trans hk)) (ne_of_gt hk)
  unfold upWt downWt
  simp only [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hi_q.symm hpq.symm,
    swap_apply_of_ne_of_ne hi_p hi_q]
  refine ite_mul_ite_eq _ _ _ ?_ ?_
  · constructor
    · rintro ⟨⟨_, hiq_w⟩, _, hpi_w, hC⟩
      refine ⟨⟨hiq', hpi_w, fun k hik hkq => ?_⟩, hq, hpi_w.trans hiq_w⟩
      rcases eq_or_ne k p with rfl | hkp
      · rw [swap_apply_left]; exact fun h => absurd h.2 (not_lt.2 hiq_w.le)
      · have hkp' : k < p := by
          rw [Fin.lt_def] at hkq ⊢; have := Fin.val_ne_of_ne hkp; omega
        rw [hsk k hkp']; exact hC k hik hkp'
    · rintro ⟨⟨_, hpi_w, hC⟩, _, hpq_w⟩
      have hiq_w : w i < w q := by
        have := hC p hip hlt
        rw [swap_apply_left] at this
        rcases lt_trichotomy (w i) (w q) with h | h | h
        · exact h
        · exact absurd (w.injective h) hi_q
        · exact absurd ⟨hpq_w, h⟩ this
      refine ⟨⟨hq, hiq_w⟩, hip, hpi_w, fun k hik hkp => ?_⟩
      have := hC k hik (hkp.trans hlt)
      rwa [hsk k hkp] at this
  · rintro ⟨⟨_, hiq_w⟩, _⟩
    have : (univ.filter fun k => p < k ∧ w p < w k ∧ w k < w i) =
        univ.filter fun k => q < k ∧ w p < w (swap p q k) ∧ w (swap p q k) < w i := by
      apply filter_congr; intro k _
      rcases eq_or_ne k q with rfl | hkq
      · simp only [lt_irrefl, false_and, iff_false]
        exact fun h => absurd h.2.2 (not_lt.2 hiq_w.le)
      · by_cases hqk : q < k
        · rw [hsk' k hqk]; simp [hlt.trans hqk, hqk]
        · have : ¬ p < k := by
            rw [Fin.lt_def] at hqk ⊢; have := Fin.val_ne_of_ne hkq; omega
          simp [this, hqk]
    rw [this]

/-- Case `j = q`: the transposition `swap i q` with `i < p`. -/
private lemma case_right_right (w : Perm (Fin n)) {p q i : Fin n} (hq : (q : ℕ) = p + 1)
    (hip : i < p) :
    upWt (w * swap i q) p q * downWt w i q = downWt (w * swap p q) i p * upWt w p q := by
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  have hlt : p < q := by rw [Fin.lt_def]; omega
  have hiq' : i < q := hip.trans hlt
  have hi_p : i ≠ p := ne_of_lt hip
  have hi_q : i ≠ q := ne_of_lt hiq'
  have hsk : ∀ k, k < p → swap p q k = k := fun k hk =>
    swap_apply_of_ne_of_ne (ne_of_lt hk) (ne_of_lt (hk.trans hlt))
  have hsk' : ∀ k, q < k → swap p q k = k := fun k hk =>
    swap_apply_of_ne_of_ne (ne_of_gt (hlt.trans hk)) (ne_of_gt hk)
  have hpq_of : (∀ k, i < k → k < q → ¬(w q < w k ∧ w k < w i)) → w p < w i → w p < w q := by
    intro hC hpi_w
    have := hC p hip hlt
    rcases lt_trichotomy (w p) (w q) with h | h | h
    · exact h
    · exact absurd (w.injective h) hpq
    · exact absurd ⟨h, hpi_w⟩ this
  unfold upWt downWt
  simp only [Perm.mul_apply, swap_apply_left, swap_apply_right,
    swap_apply_of_ne_of_ne hi_p.symm hpq, swap_apply_of_ne_of_ne hi_p hi_q]
  refine ite_mul_ite_eq _ _ _ ?_ ?_
  · constructor
    · rintro ⟨⟨_, hpi_w⟩, _, hqi_w, hC⟩
      refine ⟨⟨hip, hqi_w, fun k hik hkp => ?_⟩, hq, hpq_of hC hpi_w⟩
      rw [hsk k hkp]; exact hC k hik (hkp.trans hlt)
    · rintro ⟨⟨_, hqi_w, hC⟩, _, hpq_w⟩
      refine ⟨⟨hq, hpq_w.trans hqi_w⟩, hiq', hqi_w, fun k hik hkq => ?_⟩
      rcases eq_or_ne k p with rfl | hkp
      · exact fun h => absurd h.1 (not_lt.2 hpq_w.le)
      · have hkp' : k < p := by
          rw [Fin.lt_def] at hkq ⊢; have := Fin.val_ne_of_ne hkp; omega
        have := hC k hik hkp'
        rwa [hsk k hkp'] at this
  · rintro ⟨⟨_, hpi_w⟩, _, _, hC⟩
    have hpq_w := hpq_of hC hpi_w
    have : (univ.filter fun k => q < k ∧ w q < w k ∧ w k < w i) =
        univ.filter fun k => p < k ∧ w q < w (swap p q k) ∧ w (swap p q k) < w i := by
      apply filter_congr; intro k _
      rcases eq_or_ne k q with rfl | hkq
      · rw [swap_apply_right]; simp only [lt_irrefl, false_and, false_iff]
        exact fun h => absurd h.2.1 (not_lt.2 hpq_w.le)
      · by_cases hqk : q < k
        · rw [hsk' k hqk]; simp [hlt.trans hqk, hqk]
        · have : ¬ p < k := by
            rw [Fin.lt_def] at hqk ⊢; have := Fin.val_ne_of_ne hkq; omega
          simp [this, hqk]
    rw [this]

/-- **Local cancellation.** The two length-two paths through a weak cover and a Bruhat cover
have the same weight, except along the adjacent transposition itself. -/
private lemma local_eq (w : Perm (Fin n)) (i j p q : Fin n) :
    upWt (w * swap i j) p q * downWt w i j
      - downWt (w * swap p q) (swap p q i) (swap p q j) * upWt w p q
    = (if i = p ∧ j = q then upWt (w * swap p q) p q * downWt w p q else 0)
      - (if i = q ∧ j = p then downWt (w * swap p q) p q * upWt w p q else 0) := by
  by_cases hq : (q : ℕ) = p + 1
  swap
  · have h0 : ∀ v : Perm (Fin n), upWt v p q = 0 := fun v => by simp [upWt, hq]
    simp [h0]
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  have hlt : p < q := by rw [Fin.lt_def]; omega
  have hd0 : ∀ v : Perm (Fin n), downWt v q p = 0 := fun v => by
    simp [downWt, not_lt.2 hlt.le]
  by_cases hij : i = p ∧ j = q
  · obtain ⟨rfl, rfl⟩ := hij
    simp [swap_apply_left, swap_apply_right, hd0, hpq]
  by_cases hji : i = q ∧ j = p
  · obtain ⟨rfl, rfl⟩ := hji
    simp [swap_apply_left, swap_apply_right, hd0, hpq, hpq.symm]
  rw [ite_eq_right hij, ite_eq_right hji, sub_zero, sub_eq_zero]
  by_cases hij' : i < j
  swap
  · have : ¬ (swap p q i < swap p q j) := by rwa [swap_lt_swap_iff hq hij hji]
    simp [downWt, hij', this]
  rcases eq_or_ne i p with rfl | hip
  · have hjq : j ≠ q := fun h => hij ⟨rfl, h⟩
    have hqj : q < j := by
      rw [Fin.lt_def] at hij' ⊢; have := Fin.val_ne_of_ne hjq; omega
    rw [swap_apply_left, swap_apply_of_ne_of_ne (ne_of_gt hij') hjq]
    exact case_left_left w hq hqj
  rcases eq_or_ne i q with rfl | hiq
  · rw [swap_apply_right, swap_apply_of_ne_of_ne (ne_of_gt (hlt.trans hij')) (ne_of_gt hij')]
    exact case_right_left w hq hij'
  rcases eq_or_ne j p with rfl | hjp
  · rw [swap_apply_of_ne_of_ne hip hiq, swap_apply_left]
    exact case_left_right w hq hij'
  rcases eq_or_ne j q with rfl | hjq
  · have hip' : i < p := by
      rw [Fin.lt_def] at hij' ⊢; have := Fin.val_ne_of_ne hip; omega
    rw [swap_apply_of_ne_of_ne hip hiq, swap_apply_right]
    exact case_right_right w hq hip'
  rw [swap_apply_of_ne_of_ne hip hiq, swap_apply_of_ne_of_ne hjp hjq]
  exact case_disjoint w hq hip hiq hjp hjq


/-! ### The operators and their commutator -/

/-- Gaetz–Gao's raising operator: the weak-order cover `v ⋖ v * swap p (p + 1)` has weight
`p + 1` (positions counted from `1`). -/
private def upMat : Matrix (Perm (Fin n)) (Perm (Fin n)) ℚ :=
  Matrix.of fun u v => ∑ pq : Fin n × Fin n,
    if u = v * swap pq.1 pq.2 then upWt v pq.1 pq.2 else 0

/-- Gaetz–Gao's lowering operator, supported on Bruhat covers. -/
private def downMat : Matrix (Perm (Fin n)) (Perm (Fin n)) ℚ :=
  Matrix.of fun u v => ∑ ij : Fin n × Fin n,
    if u = v * swap ij.1 ij.2 then downWt v ij.1 ij.2 else 0

/-- The entries of `UD` as a sum over the paths `w → w * swap i j → w * swap i j * swap p q`. -/
private lemma upMat_mul_downMat_apply (u w : Perm (Fin n)) :
    (upMat * downMat : Matrix (Perm (Fin n)) (Perm (Fin n)) ℚ) u w =
      ∑ pq : Fin n × Fin n, ∑ ij : Fin n × Fin n,
      if u = w * swap ij.1 ij.2 * swap pq.1 pq.2 then
        upWt (w * swap ij.1 ij.2) pq.1 pq.2 * downWt w ij.1 ij.2 else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, upMat, downMat, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pq _ => ?_
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  rw [Finset.sum_ite_eq' univ (w * swap ij.1 ij.2)]
  simp

/-- Conjugating a transposition by `swap p q`. -/
private lemma swap_mul_swap_swap (p q i j : Fin n) :
    swap p q * swap (swap p q i) (swap p q j) = swap i j * swap p q := by
  rw [swap_apply_apply, swap_inv, ← mul_assoc, ← mul_assoc, swap_mul_self, one_mul]

/-- The entries of `DU` as a sum over the same paths as `UD`, after relabelling the Bruhat
cover by `swap p q`. -/
private lemma downMat_mul_upMat_apply (u w : Perm (Fin n)) :
    (downMat * upMat : Matrix (Perm (Fin n)) (Perm (Fin n)) ℚ) u w =
      ∑ pq : Fin n × Fin n, ∑ ij : Fin n × Fin n,
      if u = w * swap ij.1 ij.2 * swap pq.1 pq.2 then
        downWt (w * swap pq.1 pq.2) (swap pq.1 pq.2 ij.1) (swap pq.1 pq.2 ij.2) *
          upWt w pq.1 pq.2 else 0 := by
  simp only [Matrix.mul_apply, upMat, downMat, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [Finset.sum_comm]
  rw [← Equiv.sum_comp ((swap pq.1 pq.2).prodCongr (swap pq.1 pq.2))]
  refine Finset.sum_congr rfl fun ij _ => ?_
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  rw [Finset.sum_ite_eq' univ (w * swap pq.1 pq.2)]
  simp only [mem_univ, ite_true, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  rw [mul_assoc w, swap_mul_swap_swap, ← mul_assoc]

/-- Only the transpositions `swap p q` and `swap q p` survive in the sum over `(i, j)`. -/
private lemma inner_sum_eval (u w : Perm (Fin n)) (p q : Fin n) (X Y : ℚ) :
    ∑ ij : Fin n × Fin n, (if u = w * swap ij.1 ij.2 * swap p q then
      ((if ij.1 = p ∧ ij.2 = q then X else 0) - (if ij.1 = q ∧ ij.2 = p then Y else 0)) else 0)
    = if u = w then X - Y else 0 := by
  have h : ∀ ij : Fin n × Fin n, (if u = w * swap ij.1 ij.2 * swap p q then
      ((if ij.1 = p ∧ ij.2 = q then X else 0) - (if ij.1 = q ∧ ij.2 = p then Y else 0)) else 0) =
      (if u = w * swap ij.1 ij.2 * swap p q then (if ij.1 = p ∧ ij.2 = q then X else 0) else 0) -
      (if u = w * swap ij.1 ij.2 * swap p q then (if ij.1 = q ∧ ij.2 = p then Y else 0) else 0) :=
    fun ij => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun ij _ => h ij, Finset.sum_sub_distrib,
    Finset.sum_eq_single (p, q), Finset.sum_eq_single (q, p)]
  · simp only [and_self, ite_true, mul_swap_mul_self, swap_comm q p]
    split_ifs <;> simp
  · rintro ⟨i, j⟩ _ h
    have h' : ¬ (i = q ∧ j = p) := fun ⟨h1, h2⟩ => h (by rw [h1, h2])
    dsimp only
    rw [ite_eq_right h', ite_self]
  · simp
  · rintro ⟨i, j⟩ _ h
    have h' : ¬ (i = p ∧ j = q) := fun ⟨h1, h2⟩ => h (by rw [h1, h2])
    dsimp only
    rw [ite_eq_right h', ite_self]
  · simp

/-- The commutator of the two operators is diagonal, with the entries of the paths along an
adjacent transposition. -/
private lemma commutator_apply (u w : Perm (Fin n)) :
    (upMat * downMat - downMat * upMat : Matrix (Perm (Fin n)) (Perm (Fin n)) ℚ) u w =
      if u = w then ∑ pq : Fin n × Fin n, (upWt (w * swap pq.1 pq.2) pq.1 pq.2 *
        downWt w pq.1 pq.2 - downWt (w * swap pq.1 pq.2) pq.1 pq.2 * upWt w pq.1 pq.2)
      else 0 := by
  rw [Matrix.sub_apply, upMat_mul_downMat_apply, downMat_mul_upMat_apply,
    ← Finset.sum_sub_distrib]
  have h : ∀ pq : Fin n × Fin n,
      (∑ ij : Fin n × Fin n, if u = w * swap ij.1 ij.2 * swap pq.1 pq.2 then
        upWt (w * swap ij.1 ij.2) pq.1 pq.2 * downWt w ij.1 ij.2 else 0) -
      (∑ ij : Fin n × Fin n, if u = w * swap ij.1 ij.2 * swap pq.1 pq.2 then
        downWt (w * swap pq.1 pq.2) (swap pq.1 pq.2 ij.1) (swap pq.1 pq.2 ij.2) *
          upWt w pq.1 pq.2 else 0) =
      if u = w then (upWt (w * swap pq.1 pq.2) pq.1 pq.2 * downWt w pq.1 pq.2 -
        downWt (w * swap pq.1 pq.2) pq.1 pq.2 * upWt w pq.1 pq.2) else 0 := by
    intro pq
    rw [← Finset.sum_sub_distrib, ← inner_sum_eval u w pq.1 pq.2]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [← local_eq w ij.1 ij.2 pq.1 pq.2]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun pq _ => h pq]
  by_cases huw : u = w <;> simp [huw]

/-! ### The diagonal of the commutator -/

/-- `+1` on an inversion `(a, b)`, `-1` on a non-inversion with `a < b`, and `0` otherwise. -/
private def sgnInv (w : Perm (Fin n)) (a b : Fin n) : ℚ :=
  if a < b then (if w b < w a then 1 else -1) else 0

/-- For adjacent positions `p` and `q = p + 1`, the signs at `p` and at `q` differ only at `q`
and at the positions after `q` holding a value between `w p` and `w q`. -/
private lemma sgnInv_sub_eq (w : Perm (Fin n)) {p q : Fin n} (hq : (q : ℕ) = p + 1)
    (r : Fin n) :
    sgnInv w p r - sgnInv w q r =
      (if r = q then (if w q < w p then 1 else -1) else 0)
      + (if q < r ∧ w q < w r ∧ w r < w p then 2 else 0)
      - (if q < r ∧ w p < w r ∧ w r < w q then 2 else 0) := by
  have hlt : p < q := by rw [Fin.lt_def]; omega
  unfold sgnInv
  rcases eq_or_ne r q with rfl | hrq
  · simp [hlt]
  by_cases hqr : q < r
  · have hpr : p < r := hlt.trans hqr
    have h1 : w r ≠ w p := fun h => (ne_of_gt hpr) (w.injective h)
    have h2 : w r ≠ w q := fun h => (ne_of_gt hqr) (w.injective h)
    simp only [hpr, hqr, hrq, ite_true, ite_false, true_and, zero_add]
    rcases lt_or_gt_of_ne h1 with h1 | h1 <;> rcases lt_or_gt_of_ne h2 with h2 | h2 <;>
      simp [h1, h2, not_lt.2 h1.le, not_lt.2 h2.le] <;> norm_num
  · have hpr : ¬ p < r := by
      rw [Fin.lt_def] at hqr ⊢; have := Fin.val_ne_of_ne hrq; omega
    simp [hpr, hqr, hrq]

/-- Summing `sgnInv_sub_eq` over the positions. -/
private lemma sum_sgnInv_sub (w : Perm (Fin n)) {p q : Fin n} (hq : (q : ℕ) = p + 1) :
    ∑ r, (sgnInv w p r - sgnInv w q r) =
      (if w q < w p then 1 else -1) + 2 * (#{k | q < k ∧ w q < w k ∧ w k < w p} : ℚ)
        - 2 * (#{k | q < k ∧ w p < w k ∧ w k < w q} : ℚ) := by
  simp only [sgnInv_sub_eq w hq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', mem_univ, ite_true]
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul]
  ring


/-- The diagonal contribution of the adjacent transposition `swap p q`. -/
private lemma diag_term (w : Perm (Fin n)) (p q : Fin n) :
    upWt (w * swap p q) p q * downWt w p q - downWt (w * swap p q) p q * upWt w p q =
      if (q : ℕ) = p + 1 then ((p : ℕ) + 1 : ℚ) * ∑ r, (sgnInv w p r - sgnInv w q r) else 0 := by
  by_cases hq : (q : ℕ) = p + 1
  swap
  · simp [upWt, hq]
  rw [ite_eq_left hq, sum_sgnInv_sub w hq]
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  have hlt : p < q := by rw [Fin.lt_def]; omega
  have hnb : ∀ k, p < k → k < q → False := fun k h1 h2 => by
    rw [Fin.lt_def] at h1 h2; omega
  have hsk : ∀ k, q < k → swap p q k = k := fun k hk =>
    swap_apply_of_ne_of_ne (ne_of_gt (hlt.trans hk)) (ne_of_gt hk)
  have hB : (univ.filter fun k => q < k ∧ w p < w (swap p q k) ∧ w (swap p q k) < w q) =
      univ.filter fun k => q < k ∧ w p < w k ∧ w k < w q := by
    apply filter_congr; intro k _
    by_cases hqk : q < k
    · rw [hsk k hqk]
    · simp [hqk]
  unfold upWt downWt
  simp only [Perm.mul_apply, swap_apply_left, swap_apply_right, hq, true_and, hlt, hB]
  have hv₁ : ∀ k, p < k → k < q → ¬(w q < w k ∧ w k < w p) :=
    fun k h1 h2 => (hnb k h1 h2).elim
  have hv₂ : ∀ k, p < k → k < q → ¬(w p < w (swap p q k) ∧ w (swap p q k) < w q) :=
    fun k h1 h2 => (hnb k h1 h2).elim
  simp only [eq_true hv₁, eq_true hv₂, and_true]
  rcases lt_or_gt_of_ne (w.injective.ne hpq) with h | h
  · have hA : (univ.filter fun k => q < k ∧ w q < w k ∧ w k < w p) = ∅ := by
      apply filter_false_of_mem; rintro k _ ⟨_, h1, h2⟩
      exact absurd (h1.trans h2) (not_lt.2 h.le)
    simp only [h, not_lt.2 h.le, hA, ite_true, ite_false, card_empty, Nat.cast_zero]
    ring
  · have hB' : (univ.filter fun k => q < k ∧ w p < w k ∧ w k < w q) = ∅ := by
      apply filter_false_of_mem; rintro k _ ⟨_, h1, h2⟩
      exact absurd (h1.trans h2) (not_lt.2 h.le)
    simp only [h, not_lt.2 h.le, hB', ite_true, ite_false, card_empty, Nat.cast_zero]
    ring

/-- Abel summation in the form used for the diagonal entries. -/
private lemma abel_sum (F : ℕ → ℚ) (m : ℕ) :
    ∑ p ∈ range m, ((p : ℚ) + 1) * (F p - F (p + 1)) = ∑ p ∈ range m, F p - m * F m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih, sum_range_succ]; push_cast; ring

/-- The number of pairs `(a, b)` of positions with `a < b`, the rank of the top element. -/
private def numPairs (n : ℕ) : ℕ := #{x : Fin n × Fin n | x.1 < x.2}

/-- The signs of all pairs of positions add up to `2ℓ(w) - N`. -/
private lemma sum_sgnInv (w : Perm (Fin n)) :
    ∑ a, ∑ r, sgnInv w a r = 2 * (#(inversions w) : ℚ) - numPairs n := by
  rw [← Fintype.sum_prod_type']
  have h : ∀ x : Fin n × Fin n, sgnInv w x.1 x.2 =
      2 * (if x.1 < x.2 ∧ w x.2 < w x.1 then 1 else 0) - (if x.1 < x.2 then 1 else 0) := by
    intro x
    unfold sgnInv
    split_ifs <;> simp_all
    norm_num
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp [inversions, numPairs]

/-- **Diagonal of the commutator.** By Abel summation, the diagonal entry of `[U, D]` at `w`
is `2ℓ(w) - N`. -/
private lemma diag_sum (w : Perm (Fin n)) :
    ∑ pq : Fin n × Fin n, (upWt (w * swap pq.1 pq.2) pq.1 pq.2 * downWt w pq.1 pq.2
      - downWt (w * swap pq.1 pq.2) pq.1 pq.2 * upWt w pq.1 pq.2) =
      2 * (#(inversions w) : ℚ) - numPairs n := by
  simp only [diag_term]
  set F : ℕ → ℚ := fun a => if h : a < n then ∑ r, sgnInv w ⟨a, h⟩ r else 0 with hF
  have hFp : ∀ p : Fin n, F p = ∑ r, sgnInv w p r := fun p => by simp [hF, p.isLt]
  have hFn : F n = 0 := by simp [hF]
  have step : ∀ p : Fin n, ∑ q : Fin n, (if (q : ℕ) = p + 1 then
      ((p : ℕ) + 1 : ℚ) * ∑ r, (sgnInv w p r - sgnInv w q r) else 0) =
      ((p : ℕ) + 1 : ℚ) * (F p - F (p + 1)) := by
    intro p
    by_cases hp : (p : ℕ) + 1 < n
    · rw [Finset.sum_eq_single ⟨p + 1, hp⟩]
      · simp only [ite_true, Finset.sum_sub_distrib, hFp]
        rw [show F (↑p + 1) = ∑ x, sgnInv w ⟨↑p + 1, hp⟩ x from hFp ⟨↑p + 1, hp⟩]
      · intro q _ hq
        have : (q : ℕ) ≠ p + 1 := fun h => hq (Fin.ext h)
        simp [this]
      · simp
    · have h0 : ∀ q : Fin n, (q : ℕ) ≠ p + 1 := fun q h => hp (h ▸ q.isLt)
      have hp' : (p : ℕ) + 1 = n := by have := p.isLt; omega
      have hFp0 : F p = 0 := by
        rw [hFp]
        refine Finset.sum_eq_zero fun r _ => ?_
        have : ¬ p < r := by rw [Fin.lt_def]; have := r.isLt; omega
        simp [sgnInv, this]
      rw [Finset.sum_eq_zero fun q _ => ite_eq_right (h0 q), hFp0, hp', hFn]
      ring
  rw [Fintype.sum_prod_type]
  simp only [step]
  rw [Fin.sum_univ_eq_sum_range (fun a => ((a : ℚ) + 1) * (F a - F (a + 1))) n, abel_sum, hFn,
    mul_zero, sub_zero, ← Fin.sum_univ_eq_sum_range F n]
  simp only [hFp]
  exact sum_sgnInv w

/-- **Gaetz–Gao commutation relation.** `[U, D] = H`, where `H` multiplies a permutation of rank
`ℓ` by `2ℓ - N`. -/
private lemma commutator_eq :
    (upMat * downMat - downMat * upMat : Matrix (Perm (Fin n)) (Perm (Fin n)) ℚ) =
      Matrix.diagonal fun w => 2 * (#(inversions w) : ℚ) - numPairs n := by
  ext u w
  rw [commutator_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact diag_sum u
  · rfl

/-! ### The covers of the raising operator -/

/-- The nonzero entries of the raising operator are the weak-order covers. -/
private lemma upMat_ne_zero {u v : Perm (Fin n)} (h : upMat u v ≠ 0) :
    ∃ p q : Fin n, (q : ℕ) = p + 1 ∧ v p < v q ∧ u = v * swap p q := by
  simp only [upMat, Matrix.of_apply] at h
  obtain ⟨pq, _, hpq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hu : u = v * swap pq.1 pq.2
  · rw [ite_eq_left hu] at hpq
    unfold upWt at hpq
    by_cases hc : (pq.2 : ℕ) = pq.1 + 1 ∧ v pq.1 < v pq.2
    · exact ⟨pq.1, pq.2, hc.1, hc.2, hu⟩
    · exact absurd (ite_eq_right hc) hpq
  · exact absurd (ite_eq_right hu) hpq

/-- The raising operator raises the number of inversions by one. -/
private lemma card_inversions_of_upMat_ne_zero {u v : Perm (Fin n)} (h : upMat u v ≠ 0) :
    #(inversions u) = #(inversions v) + 1 := by
  obtain ⟨p, q, hq, hv, rfl⟩ := upMat_ne_zero h
  exact card_inversions_mul_swap v hq hv

/-- A cover `v ⋖ v * swap p (p + 1)` of the right weak order is a relation of the weak order
`weakLE` between the inverses. -/
private lemma weakLE_inv_of_upMat_ne_zero {u v : Perm (Fin n)} (h : upMat u v ≠ 0) :
    weakLE v⁻¹ u⁻¹ := by
  obtain ⟨p, q, hq, hv, rfl⟩ := upMat_ne_zero h
  have hlt : p < q := by rw [Fin.lt_def]; omega
  rw [mul_inv_rev, swap_inv]
  simp only [weakLE, Finset.subset_iff, inversions, mem_filter, mem_univ, true_and, Prod.forall]
  intro a b ⟨hab, hba⟩
  refine ⟨hab, ?_⟩
  rw [Perm.mul_apply, Perm.mul_apply, swap_lt_swap_iff hq]
  · exact hba
  · rintro ⟨h1, h2⟩
    rw [Perm.inv_eq_iff_eq] at h1 h2
    rw [h1, h2] at hab
    exact absurd hab (not_lt.2 hv.le)
  · rintro ⟨h1, h2⟩
    rw [h1, h2] at hba
    exact absurd hba (not_lt.2 hlt.le)

/-- A permutation has at most `N` inversions. -/
private lemma card_inversions_le (w : Perm (Fin n)) : #(inversions w) ≤ numPairs n :=
  card_le_card fun x hx => by
    simp only [inversions, mem_filter, mem_univ, true_and] at hx
    simpa using hx.1

end WeakOrder

/-! ### The `sl₂` argument and Hall's theorem -/

section Abstract

variable {P : Type*} [Fintype P]

/-- **The `sl₂` argument.** If `E` raises a grading `rk` by one and `[E, F] = H`, where `H` acts on
grade `k` by `2k - N`, then `E` is injective on grades `k` with `2k < N`. -/
private lemma sl2_injective [DecidableEq P] (rk : P → ℕ) (N : ℕ) (E F : Matrix P P ℚ)
    (hE : ∀ u v, E u v ≠ 0 → rk u = rk v + 1)
    (hEF : E * F - F * E = Matrix.diagonal fun x => 2 * (rk x : ℚ) - N)
    {k : ℕ} (hk : 2 * k < N) (v : P → ℚ) (hv : ∀ x, v x ≠ 0 → rk x = k)
    (hEv : E *ᵥ v = 0) : v = 0 := by
  -- the part of `F` that lowers the grading by one
  set F' : Matrix P P ℚ := Matrix.of fun u w => if rk u + 1 = rk w then F u w else 0 with hF'
  have hF'rk : ∀ u w, F' u w ≠ 0 → rk w = rk u + 1 := by
    intro u w h
    simp only [hF', Matrix.of_apply] at h
    by_contra h'
    exact h (ite_eq_right fun h'' => h' h''.symm)
  set H : Matrix P P ℚ := Matrix.diagonal fun x => 2 * (rk x : ℚ) - N with hH
  have hEF' : E * F' = H + F' * E := by
    rw [← sub_eq_iff_eq_add]
    ext u w
    have h1 := congrFun (congrFun hEF u) w
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply] at h1 ⊢
    by_cases huw : rk u = rk w
    · have e1 : ∑ x, E u x * F' x w = ∑ x, E u x * F x w := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : E u x = 0
        · simp [hx]
        · have := hE u x hx
          simp only [hF', Matrix.of_apply]
          rw [ite_eq_left (by omega)]
      have e2 : ∑ x, F' u x * E x w = ∑ x, F u x * E x w := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : E x w = 0
        · simp [hx]
        · have := hE x w hx
          simp only [hF', Matrix.of_apply]
          rw [ite_eq_left (by omega)]
      rw [e1, e2, h1]
    · have e1 : ∑ x, E u x * F' x w = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        by_cases hx : E u x = 0
        · simp [hx]
        · have := hE u x hx
          simp only [hF', Matrix.of_apply]
          rw [ite_eq_right (by omega), mul_zero]
      have e2 : ∑ x, F' u x * E x w = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        by_cases hx : E x w = 0
        · simp [hx]
        · have := hE x w hx
          simp only [hF', Matrix.of_apply]
          rw [ite_eq_right (by omega), zero_mul]
      have huw' : u ≠ w := fun h => huw (h ▸ rfl)
      rw [e1, e2, hH, Matrix.diagonal_apply_ne _ huw', sub_zero]
  -- the iterates `F'^j v`, supported on grade `k - j`
  set f : ℕ → P → ℚ := fun j => (F' ^ j) *ᵥ v with hf
  have hf0 : f 0 = v := by simp [hf]
  have hfs : ∀ j, f (j + 1) = F' *ᵥ f j := fun j => by
    simp only [hf, pow_succ', Matrix.mulVec_mulVec]
  have hsupp : ∀ j x, f j x ≠ 0 → rk x + j = k := by
    intro j
    induction j with
    | zero => intro x hx; rw [hf0] at hx; simpa using hv x hx
    | succ j ih =>
      intro x hx
      rw [hfs] at hx
      simp only [Matrix.mulVec, dotProduct] at hx
      obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have h1 := hF'rk x y (left_ne_zero_of_mul hy)
      have h2 := ih y (right_ne_zero_of_mul hy)
      omega
  have hHf : ∀ j, H *ᵥ f j = (2 * ((k : ℚ) - j) - N) • f j := by
    intro j
    ext x
    rw [hH, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hx : f j x = 0
    · simp [hx]
    · have h1 := hsupp j x hx
      have h2 : (rk x : ℚ) = k - j := by rw [← h1]; push_cast; ring
      rw [h2]
  set lam : ℚ := 2 * k - N with hlam
  have hrec : ∀ j, E *ᵥ f (j + 1) = (((j : ℚ) + 1) * (lam - j)) • f j := by
    intro j
    induction j with
    | zero =>
      rw [hfs, Matrix.mulVec_mulVec, hEF', Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hf0, hEv,
        Matrix.mulVec_zero, add_zero, ← hf0, hHf]
      congr 1
      rw [hlam]; push_cast; ring
    | succ j ih =>
      rw [hfs, Matrix.mulVec_mulVec, hEF', Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ih,
        Matrix.mulVec_smul, ← hfs, hHf, ← add_smul]
      congr 1
      rw [hlam]; push_cast; ring
  have hlam_neg : lam < 0 := by
    rw [hlam]
    have : ((2 * k : ℕ) : ℚ) < N := by exact_mod_cast hk
    push_cast at this
    linarith
  have hzero : ∀ j, f (j + 1) = 0 → f j = 0 := by
    intro j hj
    have h1 := hrec j
    rw [hj, Matrix.mulVec_zero] at h1
    have hc : ((j : ℚ) + 1) * (lam - j) ≠ 0 := by
      apply mul_ne_zero
      · positivity
      · have : (0 : ℚ) ≤ j := Nat.cast_nonneg j
        linarith
    exact (smul_eq_zero.mp h1.symm).resolve_left hc
  have htop : f (k + 1) = 0 := by
    ext x
    by_contra hx
    have := hsupp (k + 1) x hx
    omega
  have key : ∀ i j, j + i = k + 1 → f j = 0 := by
    intro i
    induction i with
    | zero => intro j hj; rw [add_zero] at hj; rw [hj]; exact htop
    | succ i ih => intro j hj; exact hzero j (ih (j + 1) (by omega))
  rw [← hf0]
  exact key (k + 1) 0 (by simp)

/-- An injective map on the vectors supported on `S` gives Hall's condition for `S`. -/
private lemma card_le_card_biUnion_of_injective [DecidableEq P] (E : Matrix P P ℚ)
    (S : Finset P) (hinj : ∀ v : P → ℚ, (∀ x, v x ≠ 0 → x ∈ S) → E *ᵥ v = 0 → v = 0) :
    #S ≤ #(S.biUnion fun x => univ.filter fun y => E y x ≠ 0) := by
  set T := S.biUnion fun x => univ.filter fun y => E y x ≠ 0 with hT
  set M : Matrix T S ℚ := E.submatrix Subtype.val Subtype.val with hM
  have hMinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    set v : P → ℚ := fun x => if h : x ∈ S then g ⟨x, h⟩ else 0 with hv
    have hvS : ∀ x, v x ≠ 0 → x ∈ S := by
      intro x hx
      by_contra h
      exact hx (by simp [hv, h])
    have hsum : ∀ y, (E *ᵥ v) y = ∑ x : S, E y x * g x := by
      intro y
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_subset (subset_univ S) (fun x _ hx => by simp [hv, hx]),
        ← Finset.sum_coe_sort S]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [hv, x.2]
    have hEv : E *ᵥ v = 0 := by
      ext y
      rw [hsum, Pi.zero_apply]
      by_cases hy : y ∈ T
      · have := congrFun hg ⟨y, hy⟩
        simpa [hM, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using this
      · refine Finset.sum_eq_zero fun x _ => ?_
        have : E y x = 0 := by
          by_contra h
          exact hy (mem_biUnion.2 ⟨x, x.2, by simp [h]⟩)
        rw [this, zero_mul]
    have hv0 := hinj v hvS hEv
    ext ⟨x, hx⟩
    have := congrFun hv0 x
    simpa [hv, hx] using this
  have := LinearMap.finrank_le_finrank_of_injective hMinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

/-- **Matchings from injectivity.** If `E` is injective on the vectors supported on `L`, then by
Hall's theorem there is an injective map `f` on `L` with `E (f x) x ≠ 0` for every `x ∈ L`. -/
private lemma exists_matching (E : Matrix P P ℚ) (L : Finset P)
    (hinj : ∀ v : P → ℚ, (∀ x, v x ≠ 0 → x ∈ L) → E *ᵥ v = 0 → v = 0) :
    ∃ f : P → P, (∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) ∧ ∀ x ∈ L, E (f x) x ≠ 0 := by
  classical
  have hall : ∀ s : Finset L,
      #s ≤ #(s.biUnion fun x => univ.filter fun y => E y (x : P) ≠ 0) := by
    intro s
    have h := card_le_card_biUnion_of_injective E (s.image Subtype.val)
      (fun v hv hEv => hinj v (fun x hx => by
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 (hv x hx)
        exact y.2) hEv)
    rwa [Finset.card_image_of_injective _ Subtype.val_injective, Finset.image_biUnion] at h
  obtain ⟨f, hf, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective _).1 hall
  refine ⟨fun x => if h : x ∈ L then f ⟨x, h⟩ else x, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [hx, hy, dite_true] at hxy
    exact congrArg Subtype.val (hf hxy)
  · intro x hx
    simp only [hx, dite_true]
    simpa using hfmem ⟨x, hx⟩

/-! ### Chains through the middle rank -/

/-- **Chains through the middle rank.** Let `le` be a reflexive and transitive relation on a
finite type graded by `rk`, and let `step` move each element one rank towards `m`, upwards along
`le` below `m` and downwards along `le` above `m`, fix rank `m`, and be injective on each rank.
Then no antichain of `le` has more elements than rank `m`. -/
private lemma card_antichain_le_of_step (le : P → P → Prop) (hrefl : ∀ x, le x x)
    (htrans : ∀ x y z, le x y → le y z → le x z) (rk : P → ℕ) (m : ℕ) (step : P → P)
    (hup : ∀ x, rk x < m → rk (step x) = rk x + 1 ∧ le x (step x))
    (hdown : ∀ x, m < rk x → rk (step x) + 1 = rk x ∧ le (step x) x)
    (hmid : ∀ x, rk x = m → step x = x)
    (hinj : ∀ x y, rk x = rk y → step x = step y → x = y)
    (A : Finset P) (hA : IsAntichain le (A : Set P)) :
    #A ≤ #{x | rk x = m} := by
  classical
  have hrk : ∀ x y, rk x = rk y → rk (step x) = rk (step y) := by
    intro x y h
    rcases lt_trichotomy (rk x) m with h1 | h1 | h1
    · rw [(hup x h1).1, (hup y (h ▸ h1)).1, h]
    · rw [hmid x h1, hmid y (h ▸ h1), h]
    · have := (hdown x h1).1
      have := (hdown y (h ▸ h1)).1
      omega
  have hiter_up : ∀ j x, rk x ≤ m → rk (step^[j] x) = min (rk x + j) m := by
    intro j
    induction j with
    | zero => intro x hx; simp [hx]
    | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply]
      by_cases h : rk x < m
      · have h1 := (hup x h).1
        rw [ih (step x) (by omega), h1]
        omega
      · have h1 : rk x = m := by omega
        rw [hmid x h1, ih x hx]
        omega
  have hiter_down : ∀ j x, m ≤ rk x → rk (step^[j] x) = max (rk x - j) m := by
    intro j
    induction j with
    | zero => intro x hx; simp [hx]
    | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply]
      by_cases h : m < rk x
      · have h1 := (hdown x h).1
        rw [ih (step x) (by omega)]
        omega
      · have h1 : rk x = m := by omega
        rw [hmid x h1, ih x hx]
        omega
  have hle_up : ∀ j x, rk x ≤ m → le x (step^[j] x) := by
    intro j
    induction j with
    | zero => intro x _; exact hrefl x
    | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply]
      by_cases h : rk x < m
      · exact htrans _ _ _ (hup x h).2 (ih (step x) (by have := (hup x h).1; omega))
      · rw [hmid x (by omega)]
        exact ih x hx
  have hle_down : ∀ j x, m ≤ rk x → le (step^[j] x) x := by
    intro j
    induction j with
    | zero => intro x _; exact hrefl x
    | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply]
      by_cases h : m < rk x
      · exact htrans _ _ _ (ih (step x) (by have := (hdown x h).1; omega)) (hdown x h).2
      · rw [hmid x (by omega)]
        exact ih x hx
  have hinj_iter : ∀ j x y, rk x = rk y → step^[j] x = step^[j] y → x = y := by
    intro j
    induction j with
    | zero => intro x y _ h; exact h
    | succ j ih =>
      intro x y hxy h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      exact hinj x y hxy (ih (step x) (step y) (hrk x y hxy) h)
  have hfix : ∀ j z, rk z = m → step^[j] z = z := fun j z hz =>
    Function.iterate_fixed (hmid z hz) j
  have hcomm : ∀ a b x, step^[a] (step^[b] x) = step^[b] (step^[a] x) := by
    intro a b x
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
  set K := univ.sup rk + m with hK
  have hKx : ∀ x, rk x ≤ univ.sup rk := fun x => Finset.le_sup (mem_univ x)
  have hφrk : ∀ x, rk (step^[K] x) = m := by
    intro x
    have := hKx x
    rcases le_total (rk x) m with h | h
    · rw [hiter_up K x h]; omega
    · rw [hiter_down K x h]; omega
  have claim : ∀ x ∈ A, ∀ y ∈ A, step^[K] x = step^[K] y → rk x ≤ rk y → x = y := by
    intro x hx y hy hxy hle
    by_contra hne
    apply hA hx hy hne
    by_cases hy_m : rk y ≤ m
    · have hxd : rk (step^[rk y - rk x] x) = rk y := by
        rw [hiter_up _ x (by omega)]; omega
      have : step^[rk y - rk x] x = y := by
        apply hinj_iter K _ _ hxd
        rw [hcomm, hfix _ _ (hφrk x), hxy]
      rw [← this]
      exact hle_up _ x (by omega)
    · by_cases hx_m : m ≤ rk x
      · have hyd : rk (step^[rk y - rk x] y) = rk x := by
          rw [hiter_down _ y (by omega)]; omega
        have : step^[rk y - rk x] y = x := by
          apply hinj_iter K _ _ hyd
          rw [hcomm, hfix _ _ (hφrk y), hxy]
        rw [← this]
        exact hle_down _ y (by omega)
      · have h1 := hle_up K x (by omega)
        have h2 := hle_down K y (by omega)
        rw [hxy] at h1
        exact htrans _ _ _ h1 h2
  have hinjA : Set.InjOn (step^[K]) A := by
    intro x hx y hy hxy
    rcases le_total (rk x) (rk y) with h | h
    · exact claim x hx y hy hxy h
    · exact (claim y hy x hx hxy.symm h).symm
  calc #A = #(A.image (step^[K])) := (card_image_of_injOn hinjA).symm
    _ ≤ #{x | rk x = m} := card_le_card fun z hz => by
        obtain ⟨x, _, rfl⟩ := mem_image.1 hz
        simp [hφrk x]

end Abstract

/--
**The weak order on the symmetric group is Sperner.** For every $n$ and every antichain $A$ of the
weak order on the symmetric group $S_n$ of permutations of $\{0, \dots, n-1\}$ (where
$\sigma \le \tau$ when the inversion set of $\sigma$ is contained in that of $\tau$), there is a $k$
such that $A$ has at most as many elements as there are permutations with exactly $k$ inversions.

Resolved true: Gaetz and Gao prove Stanley's conjecture that the weak order on $S_n$ is strongly
Sperner (a Peck poset); in particular it is Sperner.

Source: J. Cooper, Combinatorial Problems I
Like (2020 snapshot), Matroids, Lattices, and Posets, item 39,
https://people.math.sc.edu/cooper/combprob.html; resolution: C. Gaetz and Y. Gao, A combinatorial
sl₂-action and the Sperner property for the weak order, Proc. Amer. Math. Soc. 148 (2020);
arXiv:1811.05501, abstract: the sl₂-representation resolves Stanley's conjecture that the weak order
has the strong Sperner property (and is a Peck poset); strongly Sperner implies Sperner,
https://doi.org/10.1090/proc/14655.
-/
public theorem weakOrderSperner_holds : weakOrderSperner := by
  intro n A hA
  classical
  set ℓ : Perm (Fin n) → ℕ := fun w => #(inversions w) with hℓ
  set N := numPairs n with hN
  set m := N / 2 with hm
  refine ⟨m, ?_⟩
  have hℓN : ∀ w, ℓ w ≤ N := card_inversions_le
  -- below the middle rank: injective maps into the next rank along covers
  have hup : ∀ k, ∃ f : Perm (Fin n) → Perm (Fin n), k < m →
      (∀ x y, ℓ x = k → ℓ y = k → f x = f y → x = y) ∧
        ∀ x, ℓ x = k → ℓ (f x) = k + 1 ∧ weakLE x⁻¹ (f x)⁻¹ := by
    intro k
    by_cases hk : k < m
    · obtain ⟨f, hf1, hf2⟩ := exists_matching upMat (univ.filter fun x => ℓ x = k)
        (fun v hv hEv => sl2_injective ℓ N upMat downMat
          (fun u v h => card_inversions_of_upMat_ne_zero h) commutator_eq (k := k) (by omega) v
          (fun x hx => by simpa using hv x hx) hEv)
      refine ⟨f, fun _ => ⟨fun x y hx hy => hf1 x (by simpa using hx) y (by simpa using hy),
        fun x hx => ⟨?_, weakLE_inv_of_upMat_ne_zero (hf2 x (by simpa using hx))⟩⟩⟩
      rw [← hx]
      exact card_inversions_of_upMat_ne_zero (hf2 x (by simpa using hx))
    · exact ⟨id, fun h => absurd h hk⟩
  -- above the middle rank: injective maps into the previous rank along covers
  have hdown : ∀ k, ∃ g : Perm (Fin n) → Perm (Fin n), m < k →
      (∀ x y, ℓ x = k → ℓ y = k → g x = g y → x = y) ∧
        ∀ x, ℓ x = k → ℓ (g x) + 1 = k ∧ weakLE (g x)⁻¹ x⁻¹ := by
    intro k
    by_cases hk : m < k
    · have hcomm : upMatᵀ * downMatᵀ - downMatᵀ * upMatᵀ =
          Matrix.diagonal fun x : Perm (Fin n) => 2 * ((N - ℓ x : ℕ) : ℚ) - N := by
        rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_sub]
        have : (downMat * upMat - upMat * downMat : Matrix (Perm (Fin n)) (Perm (Fin n)) ℚ) =
            -(upMat * downMat - downMat * upMat) := by abel
        rw [this, commutator_eq, Matrix.transpose_neg, Matrix.diagonal_transpose,
          Matrix.diagonal_neg]
        congr 1
        ext x
        rw [Nat.cast_sub (hℓN x)]
        ring
      obtain ⟨g, hg1, hg2⟩ := exists_matching upMatᵀ (univ.filter fun x => ℓ x = k)
        (fun v hv hEv => by
          by_cases hkN : k ≤ N
          · exact sl2_injective (fun x => N - ℓ x) N upMatᵀ downMatᵀ
              (fun u v h => by
                have h1 : ℓ v = ℓ u + 1 := card_inversions_of_upMat_ne_zero (u := v) (v := u) h
                have h2 := hℓN v
                omega)
              hcomm (k := N - k) (by omega) v
              (fun x hx => by
                have := hv x hx
                simp only [mem_filter, mem_univ, true_and] at this
                omega) hEv
          · ext x
            by_contra hx
            have := hv x hx
            simp only [mem_filter, mem_univ, true_and] at this
            have := hℓN x
            omega)
      refine ⟨g, fun _ => ⟨fun x y hx hy => hg1 x (by simpa using hx) y (by simpa using hy),
        fun x hx => ⟨?_, weakLE_inv_of_upMat_ne_zero (hg2 x (by simpa using hx))⟩⟩⟩
      rw [← hx]
      exact (card_inversions_of_upMat_ne_zero (hg2 x (by simpa using hx))).symm
    · exact ⟨id, fun h => absurd h hk⟩
  choose F hF using hup
  choose G hG using hdown
  set step : Perm (Fin n) → Perm (Fin n) := fun x =>
    if ℓ x < m then F (ℓ x) x else if m < ℓ x then G (ℓ x) x else x with hstep
  have hB : IsAntichain (fun x y : Perm (Fin n) => weakLE x⁻¹ y⁻¹)
      ((A.image (·⁻¹) : Finset (Perm (Fin n))) : Set (Perm (Fin n))) := by
    intro x hx y hy hxy
    simp only [coe_image, Set.mem_image, mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (h ▸ rfl)
    simpa using hA ha hb hab
  have key := card_antichain_le_of_step (fun x y : Perm (Fin n) => weakLE x⁻¹ y⁻¹)
    (fun x => subset_refl _) (fun x y z h1 h2 => subset_trans h1 h2) ℓ m step
    (fun x hx => by
      simp only [hstep, hx, ite_true]
      exact (hF (ℓ x) hx).2 x rfl)
    (fun x hx => by
      simp only [hstep, not_lt.2 hx.le, hx, ite_true, ite_false]
      exact (hG (ℓ x) hx).2 x rfl)
    (fun x hx => by simp [hstep, hx])
    (fun x y hxy h => by
      simp only [hstep, hxy] at h
      by_cases h1 : ℓ y < m
      · simp only [h1, ite_true] at h
        exact (hF (ℓ y) h1).1 x y hxy rfl h
      · by_cases h2 : m < ℓ y
        · simp only [h1, h2, ite_true, ite_false] at h
          exact (hG (ℓ y) h2).1 x y hxy rfl h
        · simpa [h1, h2] using h)
    _ hB
  rwa [card_image_of_injective _ inv_injective] at key

end MathlibExt.Combinatorics.WeakOrderSpernerAMR30Problem0039Wanted
