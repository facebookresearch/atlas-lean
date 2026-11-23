/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.FinRange
public import Mathlib.Order.Basic
import Mathlib.Data.List.TakeDrop

/-!
# RNA secondary structure: the Nussinov algorithm

Nussinov, Pieczenik, Griggs and Kleitman (1978) predict the secondary structure of an RNA
sequence as a set of base pairs that is as large as possible, subject to three rules: paired
bases are complementary, every base is in at most one pair, and no two pairs cross (the
structure is a non-crossing matching, i.e. it nests like parentheses). The parameter `m` adds
the common refinement that the hairpin loop closed by a pair `(i, j)` encloses at least `m`
positions (`i + m < j`); `m = 0` is the loop matching problem of Nussinov et al., and RNA folding
programs typically use `m = 3`.

`IsStructure pair m s P` says that the finite set `P` of index pairs is such a structure on the
sequence `s` for the complementarity relation `pair` (for RNA, Watson–Crick pairs, possibly with
`G–U` wobble pairs). `nussinov pair m s` is the Nussinov recursion on the first base: it is
either unpaired, or paired with a later complementary base, which splits the rest into the
enclosed and the outer part.

## Main results

* `card_le_nussinov`: every secondary structure has at most `nussinov pair m s` pairs.
* `exists_isStructure_card_eq`: some secondary structure attains it, so **the Nussinov recursion
  computes the maximum number of pairs** of a non-crossing structure of complementary pairs.

## Cost model

`nussinov` is a specification by recursion on lists: it recomputes overlapping subproblems and
takes exponential time if evaluated directly. Every list it recurses on is a contiguous
interval `s[i, j)` of the input, so memoizing it on the `O(n²)` intervals gives the usual
`O(n³)` table (each interval maximizes over `O(n)` partners); that table is not formalized here.

## References

* R. Nussinov, G. Pieczenik, J. R. Griggs and D. J. Kleitman, *Algorithms for loop matchings*,
  SIAM J. Appl. Math. 35 (1978), 68–82.
* R. Durbin, S. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis*, Cambridge
  University Press, 1998, §10.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.RNA.Nussinov

/-- A secondary structure on `s` (Nussinov et al. 1978): a finite set of base pairs `(i, j)`,
each closing a hairpin with at least `m` unpaired positions strictly inside (`i + m < j`), joining
complementary bases (`pair s[i] s[j]`, which also puts both positions inside `s`), with every
position in at most one pair and no two pairs crossing (`i < k < j < l`). -/
structure IsStructure {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (P : Finset (ℕ × ℕ)) : Prop where
  /-- Each pair encloses at least `m` positions: `i + m < j`. -/
  loop : ∀ p ∈ P, p.1 + m < p.2
  /-- Both positions of a pair lie in `s` and carry complementary bases. -/
  compl : ∀ p ∈ P, ∃ a b, s[p.1]? = some a ∧ s[p.2]? = some b ∧ pair a b
  /-- Distinct pairs share no position. -/
  disjoint : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2
  /-- No two pairs cross. -/
  noncrossing : ∀ p ∈ P, ∀ q ∈ P, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)

/-- The largest of a list of naturals (`0` for the empty list). -/
def listMax (l : List ℕ) : ℕ := l.foldr max 0

/-- **The Nussinov recursion**: the first base `a` of `a :: rest` is either unpaired, or paired
with `rest[k]` for some `k ≥ m` with `pair a rest[k]`, splitting the rest into the enclosed part
`rest.take k` and the outer part `rest.drop (k + 1)`. Exponential-time specification; the usual
`O(n³)` table memoizes it on the intervals of `s`. -/
def nussinov {B : Type*} (pair : B → B → Prop) [DecidableRel pair] (m : ℕ) : List B → ℕ
  | [] => 0
  | a :: rest =>
      max (nussinov pair m rest)
        (listMax ((List.finRange rest.length).map fun k =>
          if m ≤ k.val ∧ pair a rest[k] then
            1 + nussinov pair m (rest.take k.val) + nussinov pair m (rest.drop (k.val + 1))
          else 0))
  termination_by l => l.length
  decreasing_by
    all_goals simp only [List.length_cons, List.length_take, List.length_drop]
    all_goals omega

private theorem le_listMax (l : List ℕ) (x : ℕ) (h : x ∈ l) : x ≤ listMax l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

private theorem listMax_mem (l : List ℕ) : listMax l = 0 ∨ listMax l ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    change max a (listMax l) = 0 ∨ max a (listMax l) ∈ a :: l
    by_cases h : listMax l ≤ a
    · exact Or.inr (by simp [max_eq_left h])
    · rw [max_eq_right (by omega)]
      rcases ih with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem bounds {B : Type*} {pair : B → B → Prop} {m : ℕ} {s : List B}
    {P : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P) (p : ℕ × ℕ) (hp : p ∈ P) :
    p.1 < s.length ∧ p.2 < s.length := by
  obtain ⟨a, b, ha, hb, _⟩ := hP.compl p hp
  exact ⟨(List.getElem?_eq_some_iff.mp ha).choose,
    (List.getElem?_eq_some_iff.mp hb).choose⟩

private theorem subset_structure {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P Q : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P) (h : Q ⊆ P) :
    IsStructure pair m s Q := by
  exact ⟨fun p hp => hP.loop p (h hp), fun p hp => hP.compl p (h hp),
    fun p hp q hq => hP.disjoint p (h hp) q (h hq),
    fun p hp q hq => hP.noncrossing p (h hp) q (h hq)⟩

private def move (P : Finset (ℕ × ℕ)) (d e : ℕ) : Finset (ℕ × ℕ) :=
  P.image (fun p => (p.1 - d + e, p.2 - d + e))

private theorem move_card (P : Finset (ℕ × ℕ)) (d e : ℕ)
    (hl : ∀ p ∈ P, d ≤ p.1 ∧ d ≤ p.2) : (move P d e).card = P.card := by
  apply Finset.card_image_of_injOn
  intro p hp q hq he
  have hp' := hl p hp
  have hq' := hl q hq
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  apply Prod.ext <;> dsimp at h₁ h₂ <;> omega

private theorem move_structure {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s t : List B} {P : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P) (d e : ℕ)
    (hl : ∀ p ∈ P, d ≤ p.1)
    (hc : ∀ p ∈ P, ∃ a b, t[p.1 - d + e]? = some a ∧
      t[p.2 - d + e]? = some b ∧ pair a b) :
    IsStructure pair m t (move P d e) := by
  have hlow (p : ℕ × ℕ) (hp : p ∈ P) : d ≤ p.1 ∧ d ≤ p.2 := by
    have := hP.loop p hp
    have := hl p hp
    exact ⟨by omega, by omega⟩
  constructor
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have := hP.loop q hq
    have := hlow q hq
    dsimp
    omega
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hc q hq
  · intro p hp q hq hne
    obtain ⟨p, hp₀, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q, hq₀, rfl⟩ := Finset.mem_image.mp hq
    have hp' := hlow p hp₀
    have hq' := hlow q hq₀
    have hd := hP.disjoint p hp₀ q hq₀ (by intro h; subst q; exact hne rfl)
    dsimp
    omega
  · intro p hp q hq hcross
    obtain ⟨p, hp₀, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q, hq₀, rfl⟩ := Finset.mem_image.mp hq
    have hp' := hlow p hp₀
    have hq' := hlow q hq₀
    apply hP.noncrossing p hp₀ q hq₀
    dsimp at hcross
    omega

private theorem cons_lookup {B : Type*} (a : B) (s : List B) (i : ℕ) (h : 0 < i) :
    (a :: s)[i]? = s[i - 1]? := by
  have he : i = (i - 1) + 1 := by omega
  rw [he, List.getElem?_cons_succ]
  simp

private theorem empty_structure {B : Type*} (pair : B → B → Prop) (m : ℕ)
    (s : List B) : IsStructure pair m s ∅ := by
  constructor <;> simp

private theorem prepend_structure {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P) (a : B) :
    IsStructure pair m (a :: s) (move P 0 1) := by
  apply move_structure hP 0 1 (by intros; omega)
  intro p hp
  simpa using hP.compl p hp

private theorem separated_union {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P Q : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P)
    (hQ : IsStructure pair m s Q) (hs : ∀ p ∈ P, ∀ q ∈ Q, p.2 < q.1) :
    IsStructure pair m s (P ∪ Q) ∧ Disjoint P Q := by
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have := hs p hp p hq
    have := hP.loop p hp
    omega
  refine ⟨?_, hd⟩
  constructor
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP.loop p hp
    · exact hQ.loop p hp
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP.compl p hp
    · exact hQ.compl p hp
  · intro p hp q hq hne
    rcases Finset.mem_union.mp hp with hp | hp <;>
      rcases Finset.mem_union.mp hq with hq | hq
    · exact hP.disjoint p hp q hq hne
    · have := hs p hp q hq
      have := hP.loop p hp
      have := hQ.loop q hq
      omega
    · have := hs q hq p hp
      have := hQ.loop p hp
      have := hP.loop q hq
      omega
    · exact hQ.disjoint p hp q hq hne
  · intro p hp q hq hc
    rcases Finset.mem_union.mp hp with hp | hp <;>
      rcases Finset.mem_union.mp hq with hq | hq
    · exact hP.noncrossing p hp q hq hc
    · have := hs p hp q hq
      omega
    · have := hs q hq p hp
      have := hQ.loop p hp
      omega
    · exact hQ.noncrossing p hp q hq hc

private theorem enclose {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P) (j : ℕ)
    (hl : m < j) (hc : ∃ a b, s[0]? = some a ∧ s[j]? = some b ∧ pair a b)
    (hi : ∀ p ∈ P, 0 < p.1 ∧ p.2 < j) :
    IsStructure pair m s (insert (0, j) P) ∧ (0, j) ∉ P := by
  have hn : (0, j) ∉ P := by
    intro h
    have := hi (0, j) h
    omega
  refine ⟨?_, hn⟩
  constructor
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa using hl
    · exact hP.loop p hp
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hc
    · exact hP.compl p hp
  · intro p hp q hq hne
    rcases Finset.mem_insert.mp hp with rfl | hp <;>
      rcases Finset.mem_insert.mp hq with rfl | hq
    · exact (hne rfl).elim
    · have := hi q hq
      have := hP.loop q hq
      dsimp
      omega
    · have := hi p hp
      have := hP.loop p hp
      dsimp
      omega
    · exact hP.disjoint p hp q hq hne
  · intro p hp q hq hcross
    rcases Finset.mem_insert.mp hp with rfl | hp <;>
      rcases Finset.mem_insert.mp hq with rfl | hq
    · dsimp at hcross
      omega
    · have := hi q hq
      dsimp at hcross
      omega
    · have := hi p hp
      have := hP.loop p hp
      dsimp at hcross
      omega
    · exact hP.noncrossing p hp q hq hcross

private theorem drop_structure {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P) (d : ℕ)
    (hl : ∀ p ∈ P, d ≤ p.1) : IsStructure pair m (s.drop d) (move P d 0) := by
  apply move_structure hP d 0 hl
  intro p hp
  have h₁ := hl p hp
  have h₂ := hP.loop p hp
  obtain ⟨a, b, ha, hb, hab⟩ := hP.compl p hp
  refine ⟨a, b, ?_, ?_, hab⟩
  · simpa only [Nat.add_zero, List.getElem?_drop, Nat.add_sub_of_le h₁] using ha
  · simpa only [Nat.add_zero, List.getElem?_drop,
      Nat.add_sub_of_le (show d ≤ p.2 by omega)] using hb

private theorem slice_structure {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P) (d n : ℕ)
    (hl : ∀ p ∈ P, d ≤ p.1) (hu : ∀ p ∈ P, p.2 < d + n) :
    IsStructure pair m ((s.drop d).take n) (move P d 0) := by
  apply move_structure hP d 0 hl
  intro p hp
  have h₁ := hl p hp
  have h₂ := hP.loop p hp
  have h₃ := hu p hp
  obtain ⟨a, b, ha, hb, hab⟩ := hP.compl p hp
  refine ⟨a, b, ?_, ?_, hab⟩
  · simpa only [Nat.add_zero, List.getElem?_take, ite_eq_left (show p.1 - d < n by omega),
      List.getElem?_drop, Nat.add_sub_of_le h₁] using ha
  · simpa only [Nat.add_zero, List.getElem?_take, ite_eq_left (show p.2 - d < n by omega),
      List.getElem?_drop, Nat.add_sub_of_le (show d ≤ p.2 by omega)] using hb

private theorem split_structure {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {a : B} {rest : List B} {P : Finset (ℕ × ℕ)} (hP : IsStructure pair m (a :: rest) P)
    (j : ℕ) (hj : (0, j) ∈ P) :
    ∃ I O : Finset (ℕ × ℕ),
      IsStructure pair m (rest.take (j - 1)) (move I 1 0) ∧
      IsStructure pair m (rest.drop j) (move O (j + 1) 0) ∧
      (move I 1 0).card = I.card ∧ (move O (j + 1) 0).card = O.card ∧
      P.card = 1 + I.card + O.card := by
  let I := P.filter (fun p => p.2 < j)
  let O := P.filter (fun p => j < p.1)
  have hi (p : ℕ × ℕ) (hp : p ∈ I) : p ∈ P ∧ 0 < p.1 ∧ p.2 < j := by
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    have hn : p ≠ (0, j) := by intro he; subst p; omega
    have hd := hP.disjoint p hp (0, j) hj hn
    dsimp at hd
    exact ⟨hp, by omega, hlt⟩
  have ho (p : ℕ × ℕ) (hp : p ∈ O) : p ∈ P ∧ j < p.1 :=
    Finset.mem_filter.mp hp
  have hclass (p : ℕ × ℕ) (hp : p ∈ P) : p = (0, j) ∨ p ∈ I ∨ p ∈ O := by
    by_cases he : p = (0, j)
    · exact Or.inl he
    · have hd := hP.disjoint p hp (0, j) hj he
      have hn := hP.noncrossing (0, j) hj p hp
      have hl := hP.loop p hp
      dsimp at hd hn
      have hlt : p.2 < j ∨ j < p.1 := by omega
      exact Or.inr (hlt.elim
        (fun h => Or.inl (Finset.mem_filter.mpr ⟨hp, h⟩))
        (fun h => Or.inr (Finset.mem_filter.mpr ⟨hp, h⟩)))
  have he : P = insert (0, j) (I ∪ O) := by
    ext p
    constructor
    · intro hp
      simpa only [Finset.mem_insert, Finset.mem_union] using hclass p hp
    · intro hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hj
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact (hi p hp).1
        · exact (ho p hp).1
  have hd : Disjoint I O := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have := hi p hp
    have := ho p hq
    have := hP.loop p (hi p hp).1
    omega
  have hn : (0, j) ∉ I ∪ O := by simp [I, O]
  have hI := subset_structure hP (Finset.filter_subset (fun p => p.2 < j) P)
  have hO := subset_structure hP (Finset.filter_subset (fun p => j < p.1) P)
  refine ⟨I, O, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using slice_structure hI 1 (j - 1)
      (fun p hp => by have := hi p hp; omega)
      (fun p hp => by have := hi p hp; omega)
  · simpa using drop_structure hO (j + 1)
      (fun p hp => by have := ho p hp; omega)
  · apply move_card
    intro p hp
    have := hi p hp
    have := hP.loop p (hi p hp).1
    omega
  · apply move_card
    intro p hp
    have := ho p hp
    have := hP.loop p (ho p hp).1
    omega
  · rw [he, Finset.card_insert_of_notMem hn, Finset.card_union_of_disjoint hd]
    omega

private theorem assemble {B : Type*} {pair : B → B → Prop} {m : ℕ}
    (a : B) (rest : List B) (k : Fin rest.length) (hk : m ≤ k.val ∧ pair a rest[k])
    (P Q : Finset (ℕ × ℕ)) (hP : IsStructure pair m (rest.take k.val) P)
    (hQ : IsStructure pair m (rest.drop (k.val + 1)) Q) :
    ∃ R : Finset (ℕ × ℕ), IsStructure pair m (a :: rest) R ∧
      R.card = 1 + P.card + Q.card := by
  have hI : IsStructure pair m (a :: rest) (move P 0 1) := by
    apply move_structure hP 0 1 (by intros; omega)
    intro p hp
    have hb := bounds hP p hp
    simp only [List.length_take] at hb
    obtain ⟨b, c, hb', hc', hbc⟩ := hP.compl p hp
    refine ⟨b, c, ?_, ?_, hbc⟩
    · simpa only [Nat.sub_zero, List.getElem?_cons_succ, List.getElem?_take,
        ite_eq_left (show p.1 < k.val by omega)] using hb'
    · simpa only [Nat.sub_zero, List.getElem?_cons_succ, List.getElem?_take,
        ite_eq_left (show p.2 < k.val by omega)] using hc'
  have hO : IsStructure pair m (a :: rest) (move Q 0 (k.val + 2)) := by
    apply move_structure hQ 0 (k.val + 2) (by intros; omega)
    intro p hp
    obtain ⟨b, c, hb, hc, hbc⟩ := hQ.compl p hp
    refine ⟨b, c, ?_, ?_, hbc⟩
    · rw [Nat.sub_zero, cons_lookup a rest _ (by omega)]
      simpa only [List.getElem?_drop,
        show p.1 + (k.val + 2) - 1 = k.val + 1 + p.1 by omega] using hb
    · rw [Nat.sub_zero, cons_lookup a rest _ (by omega)]
      simpa only [List.getElem?_drop,
        show p.2 + (k.val + 2) - 1 = k.val + 1 + p.2 by omega] using hc
  have hi (p : ℕ × ℕ) (hp : p ∈ move P 0 1) : 0 < p.1 ∧ p.2 < k.val + 1 := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have := bounds hP q hq
    simp only [List.length_take] at this
    dsimp
    omega
  have ho (p : ℕ × ℕ) (hp : p ∈ move Q 0 (k.val + 2)) : k.val + 1 < p.1 := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    dsimp
    omega
  obtain ⟨hE, hn⟩ := enclose hI (k.val + 1) (by omega)
    ⟨a, rest[k], by simp, by simp, hk.2⟩ hi
  obtain ⟨hR, hd⟩ := separated_union hE hO (by
    intro p hp q hq
    rcases Finset.mem_insert.mp hp with rfl | hp
    · have := ho q hq
      dsimp
      omega
    · have := hi p hp
      have := ho q hq
      omega)
  refine ⟨_, hR, ?_⟩
  rw [Finset.card_union_of_disjoint hd, Finset.card_insert_of_notMem hn,
    move_card P 0 1 (by intros; omega), move_card Q 0 (k.val + 2) (by intros; omega)]
  omega

/-- **Soundness bound**: every secondary structure has at most `nussinov pair m s` pairs. -/
theorem card_le_nussinov {B : Type*} (pair : B → B → Prop) [DecidableRel pair] (m : ℕ)
    (s : List B) (P : Finset (ℕ × ℕ)) (hP : IsStructure pair m s P) :
    P.card ≤ nussinov pair m s := by
  classical
  suffices hall : ∀ (n : ℕ) (t : List B), t.length = n →
      ∀ Q, IsStructure pair m t Q → Q.card ≤ nussinov pair m t from
    hall s.length s rfl P hP
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t ht Q hQ
    cases t with
    | nil =>
      have he : Q = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have := bounds hQ p hp
        simp at this
      simp [he, nussinov]
    | cons a rest =>
      have hlen : rest.length + 1 = n := ht
      rw [nussinov]
      by_cases hzero : ∃ j, (0, j) ∈ Q
      · obtain ⟨j, hj⟩ := hzero
        have hloop := hQ.loop (0, j) hj
        have hb := bounds hQ (0, j) hj
        simp only [List.length_cons, Nat.zero_add] at hb hloop
        let k : Fin rest.length := ⟨j - 1, by omega⟩
        have hjk : j = k.val + 1 := by dsimp [k]; omega
        have hk : m ≤ k.val ∧ pair a rest[k] := by
          refine ⟨by dsimp [k]; omega, ?_⟩
          obtain ⟨b, c, ha, hc, hab⟩ := hQ.compl (0, j) hj
          have ha' : a = b := by simpa using ha
          subst b
          have hc' : rest[k] = c := by
            simpa [hjk] using hc
          simpa only [hc'] using hab
        obtain ⟨I, O, hI, hO, hcI, hcO, hcQ⟩ := split_structure hQ j hj
        have hi := ih (rest.take (j - 1)).length (by
          simp only [List.length_take]
          omega) _ rfl _ hI
        have ho := ih (rest.drop j).length (by
          simp only [List.length_drop]
          omega) _ rfl _ hO
        rw [hcI] at hi
        rw [hcO] at ho
        have hmem : 1 + nussinov pair m (rest.take k.val) +
            nussinov pair m (rest.drop (k.val + 1)) ∈
            (List.finRange rest.length).map (fun k =>
              if m ≤ k.val ∧ pair a rest[k] then
                1 + nussinov pair m (rest.take k.val) +
                  nussinov pair m (rest.drop (k.val + 1)) else 0) := by
          apply List.mem_map.mpr
          exact ⟨k, List.mem_finRange k, ite_eq_left hk⟩
        have hm := le_listMax _ _ hmem
        apply le_trans _ (le_max_right _ _)
        have htake : k.val = j - 1 := rfl
        rw [htake, ← hjk] at hm
        omega
      · have hl (p : ℕ × ℕ) (hp : p ∈ Q) : 1 ≤ p.1 := by
          have hn : p.1 ≠ 0 := by
            intro he
            exact hzero ⟨p.2, by simpa only [← he, Prod.mk.eta] using hp⟩
          omega
        have hrest : IsStructure pair m rest (move Q 1 0) := by
          simpa using drop_structure hQ 1 hl
        have hi := ih rest.length (by omega) rest rfl _ hrest
        have hc : (move Q 1 0).card = Q.card := by
          apply move_card
          intro p hp
          have := hl p hp
          have := hQ.loop p hp
          omega
        rw [hc] at hi
        exact le_trans hi (le_max_left _ _)

/-- **Optimality**: some secondary structure has exactly `nussinov pair m s` pairs, so the
recursion computes the maximum number of pairs over all non-crossing structures. -/
theorem exists_isStructure_card_eq {B : Type*} (pair : B → B → Prop) [DecidableRel pair]
    (m : ℕ) (s : List B) :
    ∃ P : Finset (ℕ × ℕ), IsStructure pair m s P ∧ P.card = nussinov pair m s := by
  classical
  suffices hall : ∀ (n : ℕ) (t : List B), t.length = n →
      ∃ Q : Finset (ℕ × ℕ), IsStructure pair m t Q ∧ Q.card = nussinov pair m t from
    hall s.length s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t ht
    cases t with
    | nil => exact ⟨∅, empty_structure pair m [], by simp [nussinov]⟩
    | cons a rest =>
      have hlen : rest.length + 1 = n := ht
      let values := (List.finRange rest.length).map (fun k =>
        if m ≤ k.val ∧ pair a rest[k] then
          1 + nussinov pair m (rest.take k.val) +
            nussinov pair m (rest.drop (k.val + 1)) else 0)
      rw [nussinov]
      change ∃ Q, IsStructure pair m (a :: rest) Q ∧
        Q.card = max (nussinov pair m rest) (listMax values)
      by_cases hmax : listMax values ≤ nussinov pair m rest
      · obtain ⟨P, hP, hc⟩ := ih rest.length (by omega) rest rfl
        refine ⟨move P 0 1, prepend_structure hP a, ?_⟩
        rw [move_card P 0 1 (by intros; omega), hc, max_eq_left hmax]
      · have hmem : listMax values ∈ values := by
          rcases listMax_mem values with he | he
          · omega
          · exact he
        obtain ⟨k, _, he⟩ := List.mem_map.mp hmem
        have hk : m ≤ k.val ∧ pair a rest[k] := by
          by_contra hn
          simp only [ite_eq_right hn] at he
          omega
        simp only [ite_eq_left hk] at he
        obtain ⟨P, hP, hcP⟩ := ih (rest.take k.val).length (by
          simp only [List.length_take]
          omega) _ rfl
        obtain ⟨Q, hQ, hcQ⟩ := ih (rest.drop (k.val + 1)).length (by
          simp only [List.length_drop]
          omega) _ rfl
        obtain ⟨R, hR, hcR⟩ := assemble a rest k hk P Q hP hQ
        refine ⟨R, hR, ?_⟩
        rw [hcR, hcP, hcQ, he, max_eq_right (by omega)]

end Cslib.Bioinformatics.RNA.Nussinov
