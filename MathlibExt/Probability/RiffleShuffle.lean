/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RandomWalkFiniteGroup
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Sort

import Mathlib.Order.Fin.Basic

/-!
# Riffle shuffles: the Bayer–Diaconis formula

An `a`-shuffle of `n` cards cuts the deck into `a` packets and riffles them together; for `a = 2`
it is the Gilbert–Shannon–Reeds model of the riffle shuffle. In the inverse description (Bayer and
Diaconis 1992, Section 3), every position receives a pile label `f i ∈ Fin a`, uniformly and
independently, and the piles are stacked in label order keeping their internal order: the
resulting inverse shuffle is the stable sorting permutation `Tuple.sort f`. Bayer and Diaconis
prove that an `a`-shuffle produces the arrangement `π` with probability `C(a + n - r, n) / aⁿ`,
`r` the number of rising sequences of `π` (`risingSequences`).

* `card_sort_eq`: exactly `C(a + n - r, n)` label maps `f : Fin n → Fin a` have
  `Tuple.sort f = π⁻¹`, the counting form of Bayer and Diaconis's Theorem 3.

The proof is the stars-and-bars argument of the paper, made bijective: with `σ = π⁻¹`, the label
maps are the maps `g = f ∘ σ` that are monotone and strictly increase at every descent of `σ`;
adding to `g k` the number of non-descents before `k` turns them into the strictly increasing
maps `Fin n → Fin (a + n - r)`, which are counted by `C(a + n - r, n)`.

Source: D. Bayer and P. Diaconis, *Trailing the dovetail shuffle to its lair*, Ann. Appl. Probab.
2 (1992) 294–313, Theorem 3, Lemma 1 and Section 3.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace MathlibExt.Probability.RiffleShuffle

open Classical in
/-- **Number of rising sequences of an arrangement.** Read `π : Sₙ` as an arrangement of a deck,
card `π i` at position `i` (Bayer and Diaconis 1992, Section 3). A rising sequence is a maximal run
of consecutive face values `v, v + 1, …` lying in increasing positions; the runs break exactly at
the values `v` whose successor `v + 1` lies above `v` (`π⁻¹ (v + 1) < π⁻¹ v`), so the number of
rising sequences is one plus the number of such `v` (Bayer and Diaconis 1992, Section 2, and the
remark in Section 1 that `π` has `r` rising sequences iff `π⁻¹` has `r - 1` descents). -/
noncomputable def risingSequences {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  1 + (Finset.univ.filter fun p : Fin n × Fin n =>
    p.2.val = p.1.val + 1 ∧ π⁻¹ p.2 < π⁻¹ p.1).card

/-! ### Strictly increasing maps between finite intervals -/

/-- Strictly increasing maps `Fin r → Fin k` correspond to `r`-subsets of `Fin k`. -/
private def strictMonoEquivFinset (r k : ℕ) :
    { f : Fin r → Fin k // StrictMono f } ≃ { s : Finset (Fin k) // s.card = r } where
  toFun f := ⟨Finset.image f.1 Finset.univ, by
    rw [Finset.card_image_of_injective _ f.property.injective, Finset.card_univ,
      Fintype.card_fin]⟩
  invFun s := ⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩
  left_inv f := by
    apply Subtype.ext
    symm
    apply Finset.orderEmbOfFin_unique
    · intro i
      simp
    · exact f.property
  right_inv s := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ s.1 s.2

/-- There are `C(k, r)` strictly increasing maps `Fin r → Fin k`. -/
private theorem card_strictMono (r k : ℕ) :
    Fintype.card { f : Fin r → Fin k // StrictMono f } = k.choose r := by
  rw [Fintype.card_congr (strictMonoEquivFinset r k), Fintype.card_finset_len, Fintype.card_fin]

/-! ### Monotone maps with prescribed strict ascents -/

section Shift

variable {m : ℕ} (D : Fin m → Prop) [DecidablePred D]

/-- The number of non-descents `i` (with `¬ D i`) strictly before position `k`. -/
private def shift (k : Fin (m + 1)) : ℕ :=
  (univ.filter fun i : Fin m => i.castSucc < k ∧ ¬ D i).card

private theorem shift_zero : shift D 0 = 0 := by
  simp [shift]

private theorem shift_succ (i : Fin m) :
    shift D i.succ = shift D i.castSucc + if D i then 0 else 1 := by
  unfold shift
  have hsplit : (univ.filter fun j : Fin m => j.castSucc < i.succ ∧ ¬ D j) =
      (univ.filter fun j : Fin m => j.castSucc < i.castSucc ∧ ¬ D j) ∪
        (univ.filter fun j : Fin m => j = i ∧ ¬ D j) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_eq_of_le (Fin.le_castSucc_iff.mpr h1) with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨Fin.castSucc_injective _ h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
      · exact ⟨h1.trans (Fin.castSucc_lt_succ), h2⟩
      · exact ⟨Fin.castSucc_lt_succ, h2⟩
  rw [hsplit, card_union_of_disjoint]
  · congr 1
    by_cases h : D i
    · simp [h]
    · simp only [h, ite_false]
      rw [Finset.card_eq_one]
      exact ⟨i, by ext j; simp only [mem_filter, mem_univ, true_and, mem_singleton]
                   constructor
                   · exact fun h' => h'.1
                   · rintro rfl; exact ⟨rfl, h⟩⟩
  · rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [mem_filter, mem_univ, true_and] at hj hj'
    rw [hj'.1] at hj
    exact lt_irrefl _ hj.1

private theorem shift_le (k : Fin (m + 1)) :
    shift D k ≤ (univ.filter fun i : Fin m => ¬ D i).card :=
  card_le_card fun i => by simp only [mem_filter, mem_univ, true_and]; exact fun h => h.2

private theorem shift_last :
    shift D (Fin.last m) = (univ.filter fun i : Fin m => ¬ D i).card := by
  unfold shift
  congr 1
  ext i
  simp [Fin.castSucc_lt_last]

/-- Monotone at every step, and strictly increasing at the marked steps. -/
private def Good {a : ℕ} (g : Fin (m + 1) → Fin a) : Prop :=
  ∀ i : Fin m, g i.castSucc ≤ g i.succ ∧ (D i → g i.castSucc < g i.succ)

private instance {a : ℕ} : DecidablePred (Good D (a := a)) := fun g => by
  unfold Good; infer_instance

private theorem good_iff_strictMono {a : ℕ} (g : Fin (m + 1) → Fin a) :
    Good D g ↔ StrictMono fun k => (g k : ℕ) + shift D k := by
  rw [Fin.strictMono_iff_lt_succ]
  refine forall_congr' fun i => ?_
  rw [shift_succ]
  by_cases h : D i
  · simp only [h, ite_true, add_zero, add_lt_add_iff_right, Fin.val_fin_lt, true_implies]
    exact ⟨fun h' => h'.2, fun h' => ⟨h'.le, h'⟩⟩
  · simp only [h, ite_false, false_implies, and_true]
    rw [Fin.le_iff_val_le_val]
    omega

private theorem shift_le_of_strictMono {M : ℕ} (G : Fin (m + 1) → Fin M) (hG : StrictMono G)
    (k : Fin (m + 1)) : shift D k ≤ G k := by
  induction k using Fin.induction with
  | zero => rw [shift_zero]; exact Nat.zero_le _
  | succ i ih =>
    rw [shift_succ]
    have h1 : (G i.castSucc : ℕ) < G i.succ := hG (Fin.castSucc_lt_succ (i := i))
    split_ifs <;> omega

/-- The bijection `g ↦ g + shift` from good maps to strictly increasing maps. -/
private def goodEquiv (a : ℕ) :
    { g : Fin (m + 1) → Fin a // Good D g } ≃
      { G : Fin (m + 1) → Fin (a + (univ.filter fun i : Fin m => ¬ D i).card) //
        StrictMono G } where
  toFun g := ⟨fun k => ⟨(g.1 k : ℕ) + shift D k, by
      have := shift_le D k; have := (g.1 k).2; omega⟩, by
    intro x y hxy
    exact ((good_iff_strictMono D g.1).mp g.2) hxy⟩
  invFun G := ⟨fun k => ⟨(G.1 k : ℕ) - shift D k, by
      have hmono : StrictMono fun k => ((G.1 k : ℕ) - shift D k) + shift D k := by
        intro x y hxy
        simp only [Nat.sub_add_cancel (shift_le_of_strictMono D G.1 G.2 _)]
        exact G.2 hxy
      have hlast := shift_le_of_strictMono D G.1 G.2 (Fin.last m)
      have hb := (G.1 (Fin.last m)).2
      rw [shift_last] at hlast
      -- `k ↦ G k - shift k` is monotone, so it is at most its value at `last`.
      have hmono' : Monotone fun k => (G.1 k : ℕ) - shift D k := by
        refine Fin.monotone_iff_le_succ.mpr fun i => ?_
        have h1 : (G.1 i.castSucc : ℕ) < G.1 i.succ := G.2 (Fin.castSucc_lt_succ (i := i))
        have h2 := shift_le_of_strictMono D G.1 G.2 i.castSucc
        have h3 := shift_succ D i
        change (G.1 i.castSucc : ℕ) - shift D i.castSucc ≤ (G.1 i.succ : ℕ) - shift D i.succ
        split_ifs at h3 <;> omega
      have hle : (G.1 k : ℕ) - shift D k ≤ (G.1 (Fin.last m) : ℕ) - shift D (Fin.last m) :=
        hmono' (Fin.le_last k)
      rw [shift_last] at hle
      omega⟩, by
    rw [good_iff_strictMono]
    intro x y hxy
    simp only [Nat.sub_add_cancel (shift_le_of_strictMono D G.1 G.2 _)]
    exact G.2 hxy⟩
  left_inv g := by
    apply Subtype.ext; funext k; apply Fin.ext; simp
  right_inv G := by
    apply Subtype.ext; funext k; apply Fin.ext
    simp [Nat.sub_add_cancel (shift_le_of_strictMono D G.1 G.2 k)]

private theorem card_good (a : ℕ) :
    Fintype.card { g : Fin (m + 1) → Fin a // Good D g } =
      (a + (univ.filter fun i : Fin m => ¬ D i).card).choose (m + 1) := by
  rw [Fintype.card_congr (goodEquiv D a), card_strictMono]

end Shift

/-! ### Stable sorting and descents -/

section Sorting

variable {m a : ℕ} (σ : Equiv.Perm (Fin (m + 1)))

/-- `i` is a descent of `σ` when `σ (i + 1) < σ i`. -/
private abbrev Desc (i : Fin m) : Prop := σ i.succ < σ i.castSucc

private theorem sort_eq_iff_good (f : Fin (m + 1) → Fin a) :
    Tuple.sort f = σ ↔ Good (Desc σ) (f ∘ σ) := by
  rw [eq_comm, Tuple.eq_sort_iff]
  constructor
  · rintro ⟨hmono, hstab⟩ i
    refine ⟨hmono (Fin.castSucc_lt_succ (i := i)).le, fun hD => ?_⟩
    rcases lt_or_eq_of_le (hmono (Fin.castSucc_lt_succ (i := i)).le) with h | h
    · exact h
    · exact absurd hD (not_lt.2 (hstab (Fin.castSucc_lt_succ (i := i)).le h))
  · intro hg
    have hmono : Monotone (f ∘ σ) := Fin.monotone_iff_le_succ.mpr fun i => (hg i).1
    refine ⟨hmono, ?_⟩
    intro i j hij heq
    induction j using Fin.induction with
    | zero => exact le_of_eq (congrArg σ (Fin.le_zero_iff.mp hij))
    | succ l ih =>
      have hstep : (f ∘ σ) l.castSucc = (f ∘ σ) l.succ → σ l.castSucc < σ l.succ := by
        intro he
        have hnd : ¬ Desc σ l := fun hD => absurd he (ne_of_lt ((hg l).2 hD))
        rcases lt_or_gt_of_ne (σ.injective.ne (Fin.castSucc_lt_succ (i := l)).ne) with h | h
        · exact h
        · exact absurd h hnd
      rcases hij.lt_or_eq with h | h
      · replace h := Fin.le_castSucc_iff.mpr h
        have heq' : (f ∘ σ) i = (f ∘ σ) l.succ := heq
        have h1 : (f ∘ σ) i ≤ (f ∘ σ) l.castSucc := hmono h
        have h2 : (f ∘ σ) l.castSucc ≤ (f ∘ σ) l.succ := hmono (Fin.castSucc_lt_succ (i := l)).le
        have he1 : (f ∘ σ) i = (f ∘ σ) l.castSucc := le_antisymm h1 (h2.trans heq'.symm.le)
        exact (ih h he1).trans (hstep (he1.symm.trans heq')).le
      · subst h
        exact le_rfl

private theorem card_sort_eq_succ :
    (univ.filter fun f : Fin (m + 1) → Fin a => Tuple.sort f = σ).card =
      (a + (univ.filter fun i : Fin m => ¬ Desc σ i).card).choose (m + 1) := by
  rw [← card_good (Desc σ) a,
    ← Fintype.card_subtype (fun f : Fin (m + 1) → Fin a => Tuple.sort f = σ)]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun f => ⟨f.1 ∘ σ, (sort_eq_iff_good σ f.1).mp f.2⟩
      invFun := fun g => ⟨g.1 ∘ σ.symm, (sort_eq_iff_good σ _).mpr (by
        simpa [Function.comp_def] using g.2)⟩
      left_inv := fun f => by apply Subtype.ext; funext k; simp
      right_inv := fun g => by apply Subtype.ext; funext k; simp }

/-- Descents of `σ`, counted on `Fin m`, against the pairs counted by `risingSequences`. -/
private theorem card_desc_eq :
    (univ.filter fun p : Fin (m + 1) × Fin (m + 1) =>
        p.2.val = p.1.val + 1 ∧ σ p.2 < σ p.1).card =
      (univ.filter fun i : Fin m => Desc σ i).card := by
  symm
  refine Finset.card_bij (fun i _ => (i.castSucc, i.succ)) ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact ⟨by simp, hi⟩
  · intro i _ j _ h
    exact Fin.castSucc_injective _ (Prod.ext_iff.mp h).1
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    have hx : x.val < m := by omega
    refine ⟨⟨x.val, hx⟩, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      have hy : y = (⟨x.val, hx⟩ : Fin m).succ := Fin.ext (by simp [hp.1])
      have hx' : x = (⟨x.val, hx⟩ : Fin m).castSucc := Fin.ext rfl
      change σ (⟨x.val, hx⟩ : Fin m).succ < σ (⟨x.val, hx⟩ : Fin m).castSucc
      rw [← hy, ← hx']
      exact hp.2
    · exact Prod.ext (Fin.ext rfl) (Fin.ext (by simp [hp.1]))

end Sorting

/-- **Bayer–Diaconis formula for `a`-shuffles.** For every arrangement `π` of `n` cards with `r`
rising sequences, exactly `C(a + n - r, n)` of the `aⁿ` pile-label maps `f : Fin n → Fin a` give
`Tuple.sort f = π⁻¹`, that is, give `π` as the `a`-shuffle whose inverse stacks the piles of `f`
in label order. Hence an `a`-shuffle produces `π` with probability `C(a + n - r, n) / aⁿ`
(Bayer and Diaconis 1992, Theorem 3, in the inverse description of Section 3; their Lemma 1 shows
that this description generates the same law as the others). -/
theorem card_sort_eq (n a : ℕ) (π : Equiv.Perm (Fin n)) :
    (univ.filter (fun f : Fin n → Fin a => Tuple.sort f = π⁻¹)).card =
      (a + n - risingSequences π).choose n := by
  cases n with
  | zero =>
    have h1 : (univ.filter (fun f : Fin 0 → Fin a => Tuple.sort f = π⁻¹)) = univ := by
      ext f; simp [Subsingleton.elim (Tuple.sort f) π⁻¹]
    rw [h1, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_zero,
      Nat.choose_zero_right]
  | succ m =>
    rw [card_sort_eq_succ (a := a) π⁻¹, risingSequences, card_desc_eq π⁻¹]
    have hsum : (univ.filter fun i : Fin m => ¬ Desc π⁻¹ i).card +
        (univ.filter fun i : Fin m => Desc π⁻¹ i).card = m := by
      rw [add_comm, Finset.card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
    congr 1
    omega

end MathlibExt.Probability.RiffleShuffle
