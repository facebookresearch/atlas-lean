/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.ModEq

/-!
# Even and odd compositions and Huang's Franklin-type identity

The signed count `compositionOddMinusEven` weights each composition by the parity of its length.
The theorem `card_composition_huang_franklin` counts compositions by a bijection
that exchanges parts outside the residue class of one for small parts satisfying
Huang's placement condition.

The bijection works from the first part. Prepending one on the source side increases
the first target part by one. Adding `k` to the first source part prepends `k` on
the target side. The remaining possible first source parts are `k + s + 1` with
`0 < s < k`. Such a part creates the pair `k, s` and increases the next target part
by one, or supplies a final `k` if the source part stood alone.
-/

namespace MetaMathlibExt

@[expose] public section

open Classical in
/-- **Signed count of compositions.** For a natural number $N$ and a property $P$ of compositions
of $N$, the signed count of the compositions of $N$ satisfying $P$ is the number of them with an
odd number of parts minus the number with an even number of parts. Equivalently, it is the sum
of $(-1)^{\ell(c) + 1}$ over all compositions $c$ of $N$ satisfying $P$, where $\ell(c)$ is the
number of parts of $c$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Section 1. -/
public noncomputable def compositionOddMinusEven (N : ℕ) (P : Composition N → Prop) : ℤ :=
  ∑ c : Composition N, if P c then (-1) ^ (c.length + 1) else 0

/-- **Signed count of the compositions of zero.** The only composition of $0$ is the empty one,
which has no parts and so is even. Hence the signed count of all compositions of $0$, the number
of odd compositions minus the number of even ones, is $-1$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Section 1. -/
public theorem compositionOddMinusEven_zero_true :
    compositionOddMinusEven 0 (fun _ => True) = -1 := by
  have h : ∀ c : Composition 0, c = Composition.ones 0 := fun c =>
    Composition.eq_ones_iff.2 fun i hi => by
      have h1 := c.blocks_pos hi
      have h2 : i ≤ c.blocks.sum := List.le_sum_of_mem hi
      rw [c.blocks_sum] at h2
      omega
  rw [compositionOddMinusEven,
    Fintype.sum_eq_single (Composition.ones 0) fun c hc => absurd (h c) hc]
  simp

/-- **Huang's placement condition for small parts.** Let $k$ be a natural number. A finite
sequence $(a_0, \dots, a_{\ell - 1})$ of natural numbers satisfies the placement condition for $k$
when every entry $a_i < k$ has a preceding entry and a following entry, the preceding entry
satisfies $a_{i-1} \ge k$, and the following entry $a_{i+1}$ is either the last entry (that is,
$i + 2 = \ell$) or satisfies $a_{i+1} > k$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 15. -/
public def IsHuangSmallPartPlacement (k : ℕ) (L : List ℕ) : Prop :=
  ∀ (i a : ℕ), L[i]? = some a → a < k →
    0 < i ∧ (∃ b, L[i - 1]? = some b ∧ k ≤ b) ∧
      ∃ c, L[i + 1]? = some c ∧ (i + 2 = L.length ∨ k < c)

/-- **Sequences without small parts satisfy Huang's placement condition.** If every entry of a
finite sequence of natural numbers is at least $k$, then the sequence satisfies Huang's placement
condition for $k$, vacuously.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 15. -/
public theorem isHuangSmallPartPlacement_of_forall_le {k : ℕ} {L : List ℕ}
    (h : ∀ a ∈ L, k ≤ a) : IsHuangSmallPartPlacement k L := by
  intro i a hi ha
  have := h a (List.mem_of_getElem? hi)
  omega

namespace card_composition_huang_franklin

/-- Check the placement rule from left to right, retaining the previous part. -/
private def placed (k : ℕ) (prev : Option ℕ) : List ℕ → Prop
  | [] => True
  | a :: xs =>
    (a < k → (∃ b, prev = some b ∧ k ≤ b) ∧
      ∃ c, xs[0]? = some c ∧ (xs.length = 1 ∨ k < c)) ∧ placed k (some a) xs

private theorem placed_iff_indexed (k : ℕ) (prev : Option ℕ) (xs : List ℕ) :
    placed k prev xs ↔ ∀ i a, xs[i]? = some a → a < k →
      (∃ b, (if i = 0 then prev else xs[i - 1]?) = some b ∧ k ≤ b) ∧
        ∃ c, xs[i + 1]? = some c ∧ (i + 2 = xs.length ∨ k < c) := by
  induction xs generalizing prev with
  | nil => simp [placed]
  | cons x xs ih =>
    have splitIndex (P : ℕ → Prop) : (∀ i, P i) ↔ P 0 ∧ ∀ i, P (i + 1) :=
      ⟨fun h => ⟨h 0, fun i => h (i + 1)⟩, fun ⟨h, hs⟩ i => by cases i <;> simp_all⟩
    conv_rhs => rw [splitIndex]
    rw [placed, ih]
    simp only [List.getElem?_cons_zero, Option.some.injEq, forall_eq', ite_true,
      List.getElem?_cons_succ, List.length_cons, Nat.succ_ne_zero, ite_false,
      Nat.add_one_sub_one, Nat.succ_add]
    apply and_congr
    · simp [eq_comm]
    · apply forall_congr'
      intro i
      cases i <;> simp [Nat.add_assoc, eq_comm]

private theorem placement_iff (k : ℕ) (xs : List ℕ) :
    IsHuangSmallPartPlacement k xs ↔ placed k none xs := by
  rw [placed_iff_indexed]
  unfold IsHuangSmallPartPlacement
  apply forall_congr'
  intro i
  cases i <;> simp

/-- Both leading parts are stored as offsets: the source starts with `a + 1`,
and the target starts with `b + k`. The last two constructors mark a small part. -/
private inductive Match (k : ℕ) : ℕ → List ℕ → ℕ → List ℕ → Prop where
  | single : Match k 0 [] 0 []
  | one {a xs b ys} : Match k a xs b ys → Match k 0 ((a + 1) :: xs) (b + 1) ys
  | shift {a xs b ys} : Match k a xs b ys → Match k (a + k) xs 0 ((b + k) :: ys)
  | last {s} : 0 < s → s < k → Match k (s + k) [] 0 [s, k]
  | mark {s a xs b ys} : 0 < s → s < k → Match k a xs b ys →
      Match k (s + k) ((a + 1) :: xs) 0 (s :: (b + 1 + k) :: ys)

variable {k m n a b a' b' : ℕ} {xs ys xs' ys' : List ℕ}

private theorem head_range (h : Match k a xs b ys) : a = 0 ∨ k ≤ a := by
  cases h <;> omega

private theorem weight (h : Match k a xs b ys) : a + xs.sum = b + ys.sum := by
  induction h <;> simp_all <;> omega

private theorem off_residue {s k : ℕ} (hs : 0 < s) (hsk : s < k) :
    (s + 1) % k ≠ 1 % k := by
  intro h
  have e := Nat.ModEq.add_right_cancel' 1 (show s + 1 ≡ 0 + 1 [MOD k] from h)
  change s % k = 0 % k at e
  rw [Nat.mod_eq_of_lt hsk, Nat.zero_mod] at e
  omega

private theorem statistics (h : Match k a xs b ys) :
    (((a + 1) :: xs).filter fun x => x % k ≠ 1 % k).length =
      (((b + k) :: ys).filter fun x => x < k).length := by
  induction h <;>
    simp_all [List.filter_cons, Nat.add_right_comm _ _ 1, Nat.add_mod_right] <;>
    split_ifs at * <;> simp_all [off_residue]

/-- For positive parts, admissibility on the source side amounts to being one or exceeding
`k`: a part strictly between one and `k + 1` has the wrong residue. -/
private def leftOK (k : ℕ) (xs : List ℕ) := ∀ x ∈ xs, x = 1 ∨ k < x

private theorem leftOK_iff {k : ℕ} {xs : List ℕ} (hp : ∀ x ∈ xs, 0 < x) :
    leftOK k xs ↔ ∀ x ∈ xs, x % k ≠ 1 % k → k < x := by
  constructor
  · intro h x hx hmod
    rcases h x hx with rfl | hlt
    · exact (hmod rfl).elim
    · exact hlt
  · intro h x hx
    have := hp x hx
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
    by_cases hsk : s < k
    · by_cases hs : s = 0
      · simp [hs]
      · exact Or.inr (h _ hx (off_residue (by omega) hsk))
    · omega

private theorem left_valid (h : Match k a xs b ys) : leftOK k ((a + 1) :: xs) := by
  induction h <;> simp_all [leftOK]

private theorem prev_large {b c : ℕ} (hb : k ≤ b) (hc : k ≤ c) (ys : List ℕ) :
    placed k (some b) ys ↔ placed k (some c) ys := by
  cases ys <;> simp [placed, hb, hc]

private theorem right_valid (hk : 0 < k) (h : Match k a xs b ys) :
    (∀ y ∈ ys, 0 < y) ∧ placed k (some (b + k)) ys := by
  induction h with
  | single => simp [placed]
  | one h ih =>
    exact ⟨ih.1, (prev_large (by omega) (by omega) _).mp ih.2⟩
  | shift h ih => simpa [placed, hk, Nat.add_pos_right] using ih
  | last hs hsk => simp [placed, hs, hsk, hk]
  | @mark s a xs b ys hs hsk h ih =>
    obtain ⟨hp, hpl⟩ := ih
    have hlt : k < b + 1 + k := by omega
    have hpl' := (prev_large (c := b + 1 + k) (by omega) (by omega) _).mp hpl
    simpa [placed, hs, hsk, hlt, not_lt_of_ge hlt.le, hpl'] using hp

private theorem exists_right (hk : 0 < k) (a : ℕ) (xs : List ℕ)
    (h : leftOK k ((a + 1) :: xs)) : ∃ b ys, Match k a xs b ys := by
  obtain ⟨ha, hxs⟩ : (a = 0 ∨ k ≤ a) ∧ leftOK k xs := by
    simpa [leftOK, Nat.lt_succ_iff] using h
  rcases ha with rfl | hka
  · cases xs with
    | nil => exact ⟨_, _, .single⟩
    | cons x xs =>
      have hx := hxs x List.mem_cons_self
      obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
      obtain ⟨_, _, hm⟩ := exists_right hk u xs hxs
      exact ⟨_, _, .one hm⟩
  · let s := a - k
    have he : s + k = a := by dsimp [s]; omega
    by_cases hs : s = 0 ∨ k ≤ s
    · have hv : leftOK k ((s + 1) :: xs) := by
        simpa [leftOK, Nat.lt_succ_iff] using And.intro hs hxs
      obtain ⟨_, _, hm⟩ := exists_right hk s xs hv
      exact ⟨_, _, he ▸ hm.shift⟩
    · have hs₀ : 0 < s := by omega
      have hsk : s < k := by omega
      cases xs with
      | nil => exact ⟨_, _, he ▸ Match.last hs₀ hsk⟩
      | cons x xs =>
        have hx := hxs x List.mem_cons_self
        obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
        obtain ⟨_, _, hm⟩ := exists_right hk u xs hxs
        exact ⟨_, _, he ▸ Match.mark hs₀ hsk hm⟩
termination_by a + xs.sum
decreasing_by
  all_goals simp_all [List.sum_cons]
  all_goals omega

private theorem exists_left (hk : 0 < k) (b : ℕ) (ys : List ℕ)
    (hp : ∀ y ∈ ys, 0 < y) (h : placed k (some (b + k)) ys) : ∃ a xs, Match k a xs b ys := by
  cases b with
  | succ b =>
    have h' := (prev_large (c := b + k) (by omega) (by omega) _).mp h
    obtain ⟨_, _, hm⟩ := exists_left hk b ys hp h'
    exact ⟨_, _, .one hm⟩
  | zero =>
    cases ys with
    | nil => exact ⟨_, _, .single⟩
    | cons s ys =>
      have hs := hp s List.mem_cons_self
      by_cases hsk : k ≤ s
      · obtain ⟨b, he⟩ := Nat.exists_eq_add_of_le hsk
        rw [Nat.add_comm] at he
        subst s
        have h' : placed k (some (b + k)) ys := h.2
        obtain ⟨_, _, hm⟩ := exists_left hk b ys (fun y hy => hp y (by simp [hy])) h'
        exact ⟨_, _, .shift hm⟩
      · have hnext := (h.1 (by omega)).2
        cases ys with
        | nil => simp at hnext
        | cons z zs =>
          have hz : k ≤ z := by
            by_contra! hlt
            simpa [hsk] using (h.2.1 hlt).1
          simp only [List.getElem?_cons_zero, Option.some.injEq, exists_eq_left',
            List.length_cons, Nat.add_one_inj, List.length_eq_zero_iff] at hnext
          by_cases he : z = k
          · subst z
            have : zs = [] := by simpa using hnext
            subst zs
            exact ⟨_, _, .last hs (by omega)⟩
          · let b := z - k - 1
            have heq : b + 1 + k = z := by dsimp [b]; omega
            have hz' : placed k (some (b + k)) zs :=
              (prev_large hz (by omega) _).mp h.2.2
            obtain ⟨_, _, hm⟩ := exists_left hk b zs (fun y hy => hp y (by simp [hy])) hz'
            exact ⟨_, _, heq ▸ Match.mark hs (by omega) hm⟩
termination_by b + ys.sum
decreasing_by
  all_goals simp_all
  omega

private theorem unique_right (hk : 0 < k) (h : Match k a xs b ys) (h' : Match k a' xs' b' ys')
    (ha : a = a') (hx : xs = xs') : b = b' ∧ ys = ys' := by
  induction h generalizing a' xs' b' ys' <;> cases h' <;> grind [→ head_range]

private theorem unique_left (h : Match k a xs b ys) (h' : Match k a' xs' b' ys')
    (hb : b = b') (hy : ys = ys') : a = a' ∧ xs = xs' := by
  induction h generalizing a' xs' b' ys' <;> cases h' <;> grind

private abbrev Source (k m n : ℕ) := {c : Composition n //
  (c.blocks.filter fun a => a % k ≠ 1 % k).length = m ∧
    ∀ a ∈ c.blocks, a % k ≠ 1 % k → k < a}

private abbrev Target (k m n : ℕ) := {c : Composition (n + k - 1) //
  (c.blocks.filter fun a => a < k).length = m ∧ IsHuangSmallPartPlacement k c.blocks}

private def paired (u : Source k m n) (v : Target k m n) : Prop :=
  ∃ a xs b ys, u.val.blocks = (a + 1) :: xs ∧ v.val.blocks = (b + k) :: ys ∧ Match k a xs b ys

private theorem target_partner (hk : 0 < k) (hn : 0 < n) (u : Source k m n) :
    ∃ v, paired u v := by
  obtain ⟨⟨l, hp, hsum⟩, hcount, hadm⟩ := u
  cases l with
  | nil => simp at hsum; omega
  | cons x xs =>
    have hx := hp List.mem_cons_self
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
    obtain ⟨b, ys, hm⟩ := exists_right hk a xs ((leftOK_iff (fun _ => hp)).mpr hadm)
    obtain ⟨hpos, hp'⟩ := right_valid hk hm
    have hw := weight hm
    simp only [List.sum_cons] at hsum
    let v : Composition (n + k - 1) :=
      ⟨(b + k) :: ys, by simpa [hk, Nat.add_pos_right] using hpos, by simp; omega⟩
    have hc : (v.blocks.filter fun x => x < k).length = m := (statistics hm).symm.trans hcount
    have hv : IsHuangSmallPartPlacement k v.blocks :=
      (placement_iff ..).mpr (by simpa [v, placed] using hp')
    exact ⟨⟨v, hc, hv⟩, a, xs, b, ys, rfl, rfl, hm⟩

private theorem source_partner (hk : 0 < k) (hn : 0 < n) (v : Target k m n) :
    ∃ u, paired u v := by
  obtain ⟨⟨l, hp, hsum⟩, hcount, hpl⟩ := v
  cases l with
  | nil => simp at hsum; omega
  | cons y ys =>
    have hp' := (placement_iff k (y :: ys)).mp hpl
    have hy : k ≤ y := by
      by_contra! hlt
      simpa using (hp'.1 hlt).1
    obtain ⟨b, he⟩ := Nat.exists_eq_add_of_le hy
    rw [Nat.add_comm] at he
    subst y
    obtain ⟨a, xs, hm⟩ := exists_left hk b ys (fun _ hy => hp (List.mem_cons_of_mem _ hy)) hp'.2
    have hl := left_valid hm
    have hpos : ∀ x ∈ (a + 1) :: xs, 0 < x := by
      intro x hx
      rcases hl x hx with rfl | hlt <;> omega
    have hw := weight hm
    simp only [List.sum_cons] at hsum
    let u : Composition n := ⟨(a + 1) :: xs, fun h => hpos _ h, by simp; omega⟩
    exact ⟨⟨u, (statistics hm).trans hcount, (leftOK_iff hpos).mp hl⟩,
      a, xs, b, ys, rfl, rfl, hm⟩

private theorem target_eq (hk : 0 < k) {u : Source k m n} {v v' : Target k m n}
    (h : paired u v) (h' : paired u v') : v = v' := by
  obtain ⟨a, xs, b, ys, hu, hv, hm⟩ := h
  obtain ⟨a', xs', b', ys', hu', hv', hm'⟩ := h'
  have he := List.cons.inj (hu.symm.trans hu')
  obtain ⟨rfl, rfl⟩ := unique_right hk hm hm' (by omega) he.2
  exact Subtype.ext (Composition.ext (hv.trans hv'.symm))

private theorem source_eq {v : Target k m n} {u u' : Source k m n}
    (h : paired u v) (h' : paired u' v) : u = u' := by
  obtain ⟨a, xs, b, ys, hu, hv, hm⟩ := h
  obtain ⟨a', xs', b', ys', hu', hv', hm'⟩ := h'
  have he := List.cons.inj (hv.symm.trans hv')
  obtain ⟨rfl, rfl⟩ := unique_left hm hm' (by omega) he.2
  exact Subtype.ext (Composition.ext (hu.trans hu'.symm))

end card_composition_huang_franklin

open card_composition_huang_franklin in
/-- **Huang's Franklin-type identity for compositions.** Let $k \ge 1$, $m \ge 0$ and $n \ge 1$.
The number of compositions of $n$ with exactly $m$ parts not congruent to $1$ modulo $k$, all of
which are greater than $k$, equals the number of compositions of $n + k - 1$ with exactly $m$
parts less than $k$ in which every part less than $k$ is preceded by a part at least $k$ and is
followed by a part that is either the last part or greater than $k$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 15 (Huang)
(`jis-2024-24.6.5-thm-15`). -/
public theorem card_composition_huang_franklin (k m n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    Nat.card {c : Composition n //
        (c.blocks.filter fun a => a % k ≠ 1 % k).length = m ∧
          ∀ a ∈ c.blocks, a % k ≠ 1 % k → k < a}
      = Nat.card {c : Composition (n + k - 1) //
        (c.blocks.filter fun a => a < k).length = m ∧ IsHuangSmallPartPlacement k c.blocks} := by
  choose f hf using target_partner (m := m) hk hn
  choose g hg using source_partner (m := m) hk hn
  exact Nat.card_congr
    { toFun := f
      invFun := g
      left_inv := fun u => source_eq (hg (f u)) (hf u)
      right_inv := fun v => target_eq hk (hf (g v)) (hg v) }

end

end MetaMathlibExt
