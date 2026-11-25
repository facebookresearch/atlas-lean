/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.NormNum

/-!
# Massive sets of independent relators in `F₂` (Kourovka Notebook Problem 10.13)

The theorem `existsMassiveNormallyIndependentSet_refuted` answers this problem in the negative.

Kourovka Notebook, Problem 10.13 (R. I. Grigorchuk), marked solved: does there exist a massive set
of independent elements in the free group `F₂` on `a, b`, that is, a set `E` of reduced words in `a,
b, a⁻¹, b⁻¹` such that (1) no `w ∈ E` lies in the normal closure of `E \ {w}` and (2) `limsup_{n →
∞} |Eₙ|^{1/n} = 3`, where `Eₙ` is the set of words of length `n` in `E`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 10.13 (R. I. Grigorchuk). UnsolvedMath
record UM-00700630 (`KOU-10.13`), dataset ulamai/UnsolvedMath v1.8.0.

Reduced words are the elements of `FreeGroup (Fin 2)` and length is `FreeGroup.norm`. Since there
are `4 · 3^{n-1}` reduced words of length `n ≥ 1`, `limsup |Eₙ|^{1/n} ≤ 3` always, so condition (2)
is stated as: for every `0 < c < 3`, `|Eₙ| ≥ cⁿ` for infinitely many `n`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.MassiveIndependentSetFreeGroupKourovka10Problem13Wanted

/-- **Normally independent sets in the free group of rank two.** A subset $E$ of the free group
$F_2$ on two generators is normally independent when no element $w \in E$ lies in the normal
closure of $E \setminus \{w\}$, the smallest normal subgroup of $F_2$ containing
$E \setminus \{w\}$. -/
def IsNormallyIndependent (E : Set (FreeGroup (Fin 2))) : Prop :=
  ∀ w ∈ E, w ∉ Subgroup.normalClosure (E \ {w})

/-- **Grigorchuk's problem on massive independent sets in the free group of rank two.** The
statement that some subset $E$ of the free group $F_2$ on two generators is normally independent
(no $w \in E$ lies in the normal closure of $E \setminus \{w\}$) and massive: for every real number
$c$ with $0 < c < 3$ and every natural number $N$ there is $n \ge N$ such that the set $E_n$ of
elements of $E$ of reduced word length $n$ has at least $c^n$ elements.

Since $F_2$ has $4 \cdot 3^{n-1}$ reduced words of length $n \ge 1$, $\limsup |E_n|^{1/n} \le 3$
always, so massiveness says $\limsup |E_n|^{1/n} = 3$, as in Kourovka Notebook Problem 10.13
(R. I. Grigorchuk). -/
def existsMassiveNormallyIndependentSet : Prop :=
  ∃ E : Set (FreeGroup (Fin 2)), IsNormallyIndependent E ∧
    ∀ c : ℝ, 0 < c → c < 3 → ∀ N : ℕ, ∃ n ≥ N, c ^ n ≤ ({w ∈ E | w.norm = n}.ncard : ℝ)

private abbrev F₂ := FreeGroup (Fin 2)

-- If each relator is a quotient of two elements of V, imposing it identifies
-- two images of V. Normal independence makes this identification strict at every step.
private theorem card_le_of_divisions {E : Set F₂} (hE : IsNormallyIndependent E)
    (S V : Finset F₂) (hS : ↑S ⊆ E)
    (hsplit : ∀ w ∈ S, ∃ x ∈ V, ∃ y ∈ V, x / y = w) : S.card ≤ V.card := by
  classical
  let closure (T : Finset F₂) := Subgroup.normalClosure (T : Set F₂)
  let images (T : Finset F₂) := V.image (QuotientGroup.mk' (closure T))
  have bound (T : Finset F₂) (hT : T ⊆ S) : T.card + (images T).card ≤ V.card := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.card_empty, zero_add]
      exact Finset.card_image_le
    | @insert w T hw ih =>
      have hTS := (Finset.subset_insert w T).trans hT
      have hwS := hT (Finset.mem_insert_self w T)
      obtain ⟨x, hx, y, hy, hxy⟩ := hsplit w hwS
      have hprev : (T : Set F₂) ⊆ E \ {w} := by
        intro z hz
        exact ⟨hS (hTS hz), fun he => hw ((Set.mem_singleton_iff.mp he) ▸ hz)⟩
      have hne : (x : F₂ ⧸ closure T) ≠ y := by
        intro he
        apply hE w (hS hwS)
        apply Subgroup.normalClosure_mono hprev
        exact hxy ▸ QuotientGroup.eq_iff_div_mem.mp he
      have heq : (x : F₂ ⧸ closure (insert w T)) = y := by
        apply QuotientGroup.eq_iff_div_mem.mpr
        rw [hxy]
        exact Subgroup.subset_normalClosure (Finset.mem_insert_self w T)
      let f := QuotientGroup.map (closure T) (closure (insert w T)) (MonoidHom.id F₂)
        (Subgroup.normalClosure_mono (show (T : Set F₂) ⊆ ↑(insert w T) from
          Finset.subset_insert w T))
      have hdrop : (images (insert w T)).card < (images T).card := by
        have himage : images (insert w T) = (images T).image f := by
          simp only [images, Finset.image_image]
          rfl
        rw [himage]
        apply lt_of_le_of_ne Finset.card_image_le
        intro hcard
        exact hne (Finset.card_image_iff.mp hcard (Finset.mem_image_of_mem _ hx)
          (Finset.mem_image_of_mem _ hy) heq)
      specialize ih hTS
      rw [Finset.card_insert_of_notMem hw]
      omega
  exact (Nat.le_add_right _ _).trans (bound S Finset.Subset.rfl)

-- All signed words of a given length suffice for an upper bound, including unreduced ones.
private def words (k : ℕ) : Finset F₂ :=
  Finset.univ.image fun v : List.Vector (Fin 2 × Bool) k => FreeGroup.mk v.val

private theorem mk_mem_words (l : List (Fin 2 × Bool)) {k : ℕ} (hl : l.length = k) :
    FreeGroup.mk l ∈ words k :=
  Finset.mem_image.mpr ⟨⟨l, hl⟩, Finset.mem_univ _, rfl⟩

private theorem card_words_le (k : ℕ) : (words k).card ≤ 4 ^ k := by
  simpa [words] using (Finset.card_image_le (s := Finset.univ)
    (f := fun v : List.Vector (Fin 2 × Bool) k => FreeGroup.mk v.val))

private theorem sphere_bound {E : Set F₂} (hE : IsNormallyIndependent E) (n : ℕ) :
    {w ∈ E | w.norm = n}.ncard ≤ 4 * 2 ^ n := by
  classical
  have hfin : {w ∈ E | w.norm = n}.Finite := by
    apply (words n).finite_toSet.subset
    intro w hw
    exact FreeGroup.mk_toWord (x := w) ▸ mk_mem_words w.toWord hw.2
  let k := n / 2
  let V := words k ∪ (words (n - k)).image (·⁻¹)
  calc
    _ = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
    _ ≤ V.card := by
      apply card_le_of_divisions hE
      · intro w hw
        exact (hfin.mem_toFinset.mp hw).1
      intro w hw
      have hlen : w.toWord.length = n := (hfin.mem_toFinset.mp hw).2
      let a := w.toWord.take k
      let b := w.toWord.drop k
      have ha : FreeGroup.mk a ∈ words k := mk_mem_words _ (by simp [a, hlen, k, Nat.div_le_self])
      have hb : FreeGroup.mk b ∈ words (n - k) := mk_mem_words _ (by simp [b, hlen])
      refine ⟨FreeGroup.mk a, Finset.mem_union_left _ ha, (FreeGroup.mk b)⁻¹,
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb), ?_⟩
      simp [div_eq_mul_inv, FreeGroup.mul_mk, a, b, FreeGroup.mk_toWord]
    _ ≤ (words k).card + (words (n - k)).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
    _ ≤ 4 ^ k + 4 ^ (n - k) := Nat.add_le_add (card_words_le _) (card_words_le _)
    _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by
      rw [show 4 = 2 ^ 2 by decide, ← pow_mul, ← pow_mul]
      apply Nat.add_le_add <;> apply Nat.pow_le_pow_right (by decide) <;> dsimp [k] <;> omega
    _ = 4 * 2 ^ n := by rw [pow_succ]; omega

/--
**No massive normally independent set in the free group of rank two.** There is no subset $E$ of
the free group $F_2$ on two generators such that no element $w \in E$ lies in the normal closure
of $E \setminus \{w\}$ and, for every real number $c$ with $0 < c < 3$ and every natural number
$N$, there is $n \ge N$ for which at least $c^n$ elements of $E$ have reduced word length $n$.

Koch-Hyde and Olive prove that a subset $S$ of the ball $B_n$ of the free group $F_r$ in which no
$x \in S$ lies in the subgroup generated by $S \setminus \{x\}$ has $|S| = O((2r - 1)^{n/2})$.
Normal independence implies this independence, so for every such $E \subseteq F_2$ the set $E_n$
of its elements of length $n$ has $|E_n| = O(3^{n/2})$, and the growth rate is at most
$\sqrt 3 < 3$. The Kourovka Notebook (21st issue) marks Problem 10.13 solved, "No, there is no
such set".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 10.13 (R. I.
Grigorchuk); resolution: L. Koch-Hyde and É. Olive, Two problems about bases and independent sets in
free groups, arXiv:2609.00382 (2026), Theorem 1.7 (an independent set S ⊆ B_n ⊆ F_r has |S| = O((2r
- 1)^{n/2})) and the Solution to Problem 1.5; the Kourovka Notebook (21st issue) marks 10.13 solved,
https://arxiv.org/abs/2609.00382.
-/
theorem existsMassiveNormallyIndependentSet_refuted :
    ¬ existsMassiveNormallyIndependentSet := by
  rintro ⟨E, hE, hmass⟩
  obtain ⟨n, hn, hmany⟩ := hmass (5 / 2) (by norm_num) (by norm_num) 8
  have hfew : ({w ∈ E | w.norm = n}.ncard : ℝ) ≤ 4 * 2 ^ n := by
    exact_mod_cast sphere_bound hE n
  have hratio : (4 : ℝ) < (5 / 4) ^ n := calc
    _ < (5 / 4 : ℝ) ^ 8 := by norm_num
    _ ≤ (5 / 4 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hlt := mul_lt_mul_of_pos_right hratio (by positivity : (0 : ℝ) < 2 ^ n)
  rw [← mul_pow, show (5 / 4 : ℝ) * 2 = 5 / 2 by norm_num] at hlt
  exact hlt.not_ge (hmany.trans hfew)

end MathlibExt.GroupTheory.MassiveIndependentSetFreeGroupKourovka10Problem13Wanted
