/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Sym.Card

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

namespace compositionOddMinusEven_huang_eq_sum

open card_composition_huang_franklin

-- Each source part is a terminal action (ordinary or marked), preceded by a run
-- of shifts. The second coordinate records the excess of a small part over one.
private abbrev Code (k : ℕ) := ℕ × Option (Fin (k - 1))

private def offset (k : ℕ) (p : Code k) : ℕ :=
  match p.2 with
  | none => p.1 * k
  | some g => (p.1 + 1) * k + ((g : ℕ) + 1)

private def codeOf (k a : ℕ) (hk : 0 < k) : Code k :=
  if h : a % k = 0 then (a / k, none)
  else (a / k - 1, some ⟨a % k - 1, by have := Nat.mod_lt a hk; omega⟩)

private theorem codeOf_offset (k : ℕ) (hk : 0 < k) (p : Code k) :
    codeOf k (offset k p) hk = p := by
  obtain ⟨q, _ | g⟩ := p
  · simp [codeOf, offset, hk]
  · have hg : (g : ℕ) + 1 < k := by have := g.isLt; omega
    rw [offset, codeOf]
    change (if h : ((q + 1) * k + ((g : ℕ) + 1)) % k = 0 then _ else _) = _
    have hm : ((q + 1) * k + ((g : ℕ) + 1)) % k = (g : ℕ) + 1 := by
      simp [Nat.mod_eq_of_lt hg]
    have hd : ((q + 1) * k + ((g : ℕ) + 1)) / k = q + 1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hg, Nat.zero_add]
    simp [hm, hd]

private theorem offset_codeOf (k a : ℕ) (hk : 0 < k) (ha : a = 0 ∨ k ≤ a) :
    offset k (codeOf k a hk) = a := by
  unfold codeOf
  split_ifs with h
  · simpa [offset, Nat.mul_comm, h] using Nat.div_add_mod a k
  · have hka : k ≤ a := ha.resolve_left (fun he => h (by simp [he]))
    have hd : 1 ≤ a / k := (Nat.le_div_iff_mul_le hk).2 (by simpa using hka)
    have he : a % k - 1 + 1 = a % k := by omega
    have hf : a / k - 1 + 1 = a / k := by omega
    simpa [offset, he, hf, Nat.mul_comm] using Nat.div_add_mod a k

private def codePart (k : ℕ) (p : Code k) : ℕ := offset k p + 1

private theorem codePart_injective (k : ℕ) (hk : 0 < k) : Function.Injective (codePart k) := by
  intro p q h
  have he : offset k p = offset k q := Nat.succ.inj h
  simpa only [codeOf_offset] using congrArg (fun a => codeOf k a hk) he

private def markCount {k : ℕ} (ps : List (Code k)) : ℕ :=
  (ps.filter fun p => p.2.isSome).length

private def shiftCount {k : ℕ} (ps : List (Code k)) : ℕ := (ps.map Prod.fst).sum

private def colorTotal {k : ℕ} (ps : List (Code k)) : ℕ :=
  (ps.map fun p => p.2.elim 0 (fun g => (g : ℕ))).sum

private theorem codeWeight (k : ℕ) (ps : List (Code k)) :
    (ps.map (codePart k)).sum = ps.length + (k + 1) * markCount ps + shiftCount ps * k +
      colorTotal ps := by
  induction ps with
  | nil => simp [markCount, shiftCount, colorTotal]
  | cons p ps ih =>
    obtain ⟨q, _ | g⟩ := p <;>
      simp [codePart, offset, markCount, shiftCount, colorTotal, ih, Nat.add_mul, Nat.mul_add] <;>
      omega

private theorem addShifts {k a b : ℕ} {xs ys : List ℕ} (t : ℕ) (h : Match k a xs b ys) :
    ∃ c zs, Match k (t * k + a) xs c zs ∧ zs.length = t + ys.length := by
  induction t with
  | zero => exact ⟨b, ys, by simpa, by simp⟩
  | succ t ih =>
    obtain ⟨c, zs, hm, hl⟩ := ih
    refine ⟨0, (c + k) :: zs, ?_, by simp [hl, Nat.add_right_comm]⟩
    have he : (t + 1) * k + a = t * k + a + k := by rw [Nat.succ_mul]; omega
    rw [he]
    exact hm.shift

private theorem fitCodes (k : ℕ) (ps : List (Code k)) (hp : ps ≠ []) :
    ∃ a xs b ys, ps.map (codePart k) = (a + 1) :: xs ∧ Match k a xs b ys ∧
      ys.length = 2 * markCount ps + shiftCount ps := by
  induction ps with
  | nil => exact (hp rfl).elim
  | cons p ps ih =>
    obtain ⟨q, _ | g⟩ := p
    · cases ps with
      | nil =>
        obtain ⟨b, ys, hm, hl⟩ := addShifts q (Match.single (k := k))
        exact ⟨q * k, [], b, ys, by simp [codePart, offset], by simpa using hm,
          by simpa [markCount, shiftCount] using hl⟩
      | cons p ps =>
        obtain ⟨a, xs, b, ys, he, hm, hl⟩ := ih (by simp)
        obtain ⟨c, zs, hm', hl'⟩ := addShifts q hm.one
        refine ⟨_, _, c, zs, ?_, by simpa using hm', ?_⟩
        · simp [codePart, offset, he]
        · simp [markCount, shiftCount] at *
          omega
    · have hg : (g : ℕ) + 1 < k := by have := g.isLt; omega
      have hf : (q + 1) * k + ((g : ℕ) + 1) = q * k + ((g : ℕ) + 1 + k) := by
        rw [Nat.succ_mul]; omega
      cases ps with
      | nil =>
        obtain ⟨b, ys, hm, hl⟩ := addShifts q (Match.last (by omega) hg)
        exact ⟨_, [], b, ys, by simp [codePart, offset, hf], hm,
          by simpa [markCount, shiftCount, Nat.add_comm] using hl⟩
      | cons p ps =>
        obtain ⟨a, xs, b, ys, he, hm, hl⟩ := ih (by simp)
        obtain ⟨c, zs, hm', hl'⟩ := addShifts q (hm.mark (by omega) hg)
        refine ⟨_, _, c, zs, ?_, hm', ?_⟩
        · simp [codePart, offset, hf, he]
        · simp [markCount, shiftCount] at *
          omega

private theorem codeMarks (k : ℕ) (ps : List (Code k)) :
    ((ps.map (codePart k)).filter fun x => x % k ≠ 1 % k).length = markCount ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨q, _ | g⟩ := p
    · simpa [markCount, codePart, offset, Nat.add_comm] using ih
    · have hg : (g : ℕ) + 1 < k := by have := g.isLt; omega
      have ho := off_residue (by omega) hg
      simpa [markCount, codePart, offset, Nat.add_assoc, ho] using ih

private abbrev CodeWord (k m n : ℕ) :=
  {ps : List (Code k) // (ps.map (codePart k)).sum = n ∧ markCount ps = m}

private theorem exists_target_of_code {k m n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (w : CodeWord k m n) : ∃ v : Target k m n, (∃ a xs b ys,
      w.val.map (codePart k) = (a + 1) :: xs ∧ v.val.blocks = (b + k) :: ys ∧
        Match k a xs b ys) ∧ v.val.length + 1 = 2 * (m + 1) + shiftCount w.val := by
  obtain ⟨ps, hs, hm⟩ := w
  obtain ⟨a, xs, b, ys, he, hmatch, hl⟩ := fitCodes k ps (by rintro rfl; simp at hs; omega)
  have hq := (weight hmatch)
  rw [he, List.sum_cons] at hs
  obtain ⟨hpos, hplace⟩ := right_valid hk hmatch
  have hc : (((a + 1) :: xs).filter fun x => x % k ≠ 1 % k).length = m :=
    he ▸ (codeMarks k ps).trans hm
  let v : Composition (n + k - 1) :=
    ⟨(b + k) :: ys, by simpa [hk, Nat.add_pos_right] using hpos, by simp; omega⟩
  have hv : IsHuangSmallPartPlacement k v.blocks :=
    (placement_iff ..).mpr (by simpa [v, placed] using hplace)
  refine ⟨⟨v, (statistics hmatch).symm.trans hc, hv⟩, ⟨a, xs, b, ys, he, rfl, hmatch⟩, ?_⟩
  change ys.length + 1 + 1 = 2 * (m + 1) + shiftCount ps
  omega

private theorem codeWord_preimage {k : ℕ} (hk : 0 < k) (xs : List ℕ) (hx : leftOK k xs) :
    ∃ ps : List (Code k), ps.map (codePart k) = xs := by
  refine ⟨xs.map fun x => codeOf k (x - 1) hk, ?_⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id xs]
  apply List.map_congr_left
  intro x h
  have h' := hx x h
  change offset k (codeOf k (x - 1) hk) + 1 = x
  rw [offset_codeOf _ _ hk (by omega)]
  omega

private noncomputable def codeWordTarget {k m n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    CodeWord k m n ≃ Target k m n := by
  classical
  let f (w : CodeWord k m n) := (exists_target_of_code hk hn w).choose
  have hf (w : CodeWord k m n) := (exists_target_of_code hk hn w).choose_spec
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro u v huv
    obtain ⟨⟨a, xs, b, ys, hu, ht, hm⟩, _⟩ := hf u
    obtain ⟨⟨a', xs', b', ys', hv, ht', hm'⟩, _⟩ := hf v
    have he := List.cons.inj (ht.symm.trans ((congrArg (fun t : Target k m n => t.val.blocks)
      huv).trans ht'))
    obtain ⟨rfl, rfl⟩ := unique_left hm hm' (by omega) he.2
    exact Subtype.ext (List.map_injective_iff.mpr (codePart_injective k hk) (hu.trans hv.symm))
  · intro v
    obtain ⟨u, a, xs, b, ys, hu, hv, hm⟩ := source_partner hk hn v
    obtain ⟨ps, he⟩ := codeWord_preimage hk u.val.blocks (hu ▸ left_valid hm)
    let w : CodeWord k m n :=
      ⟨ps, he ▸ u.val.blocks_sum, (codeMarks k ps).symm.trans (he ▸ u.prop.1)⟩
    obtain ⟨⟨a', xs', b', ys', hps, hfv, hm'⟩, _⟩ := hf w
    have h := List.cons.inj (hps.symm.trans (he.trans hu))
    obtain ⟨rfl, rfl⟩ := unique_right hk hm' hm (by omega) h.2
    exact ⟨w, Subtype.ext (Composition.ext (hfv.trans hv.symm))⟩

private theorem codeWordTarget_length {k m n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (w : CodeWord k m n) :
    (codeWordTarget hk hn w).val.length + 1 = 2 * (m + 1) + shiftCount w.val := by
  exact (exists_target_of_code hk hn w).choose_spec.2

-- Stars and bars give the weak count; inclusion-exclusion bounds the colors.
private abbrev HuangWeak (m H : ℕ) := {g : Fin m → ℕ // ∑ t, g t = H}

private theorem huangWeakCount (m H : ℕ) :
    Nat.card (HuangWeak m H) = (m + H - 1).choose H := by
  classical
  rw [Nat.card_congr (Sym.equivNatSumOfFintype (Fin m) H).symm,
    Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]

private def huangOffset {m : ℕ} (r : ℕ) (s : Finset (Fin m)) (i : Fin m) : ℕ :=
  if i ∈ s then r else 0

private theorem huangOffset_sum {m : ℕ} (r : ℕ) (s : Finset (Fin m)) :
    ∑ i, huangOffset r s i = s.card * r := by
  simp [huangOffset, Finset.sum_ite_mem]

private def huangShift {r m H : ℕ} (s : Finset (Fin m)) (hs : s.card * r ≤ H) :
    {g : HuangWeak m H // ∀ i ∈ s, r ≤ g.val i} ≃ HuangWeak m (H - s.card * r) where
  toFun g := ⟨fun i => g.val.val i - huangOffset r s i, by
    rw [Finset.sum_tsub_distrib, g.val.property, huangOffset_sum]
    intro i _
    by_cases hi : i ∈ s
    · simpa [huangOffset, hi] using g.property i hi
    · simp [huangOffset, hi]⟩
  invFun g := ⟨⟨fun i => g.val i + huangOffset r s i, by
    rw [Finset.sum_add_distrib, g.property, huangOffset_sum, Nat.sub_add_cancel hs]⟩,
    fun i hi => by simp [huangOffset, hi]⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change g.val.val i - huangOffset r s i + huangOffset r s i = g.val.val i
    apply Nat.sub_add_cancel
    by_cases hi : i ∈ s
    · simpa [huangOffset, hi] using g.property i hi
    · simp [huangOffset, hi]
  right_inv g := by
    apply Subtype.ext
    funext i
    change g.val i + huangOffset r s i - huangOffset r s i = g.val i
    omega

private def huangGoodEquiv (r m H : ℕ) :
    {g : HuangWeak m H // ∀ i, g.val i < r} ≃ {g : Fin m → Fin r // ∑ t, (g t : ℕ) = H} where
  toFun g := ⟨fun i => ⟨g.val.val i, g.property i⟩, g.val.property⟩
  invFun g := ⟨⟨fun i => (g.val i : ℕ), g.property⟩, fun i => (g.val i).isLt⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl

private theorem huangBoundedCount (r m H : ℕ) :
    (Fintype.card {g : Fin m → Fin r // ∑ t, (g t : ℕ) = H} : ℤ) =
      ∑ l ∈ Finset.range (m + 1), if l * r ≤ H then
        (-1 : ℤ) ^ l * (m.choose l : ℤ) * ((m + (H - l * r) - 1).choose (H - l * r) : ℤ)
        else 0 := by
  classical
  let _ : Fintype (HuangWeak m H) := Fintype.ofEquiv _ (Sym.equivNatSumOfFintype (Fin m) H)
  let bad (i : Fin m) : Finset (HuangWeak m H) := Finset.univ.filter (fun g => r ≤ g.val i)
  have bad_mem (i : Fin m) (g : HuangWeak m H) : g ∈ bad i ↔ r ≤ g.val i := by simp [bad]
  have good_mem (g : HuangWeak m H) :
      g ∈ (Finset.univ : Finset (Fin m)).inf (fun i => (bad i)ᶜ) ↔ ∀ i, g.val i < r := by
    simp [Finset.mem_inf, Finset.mem_compl, bad_mem, not_le]
  have good_card : Fintype.card {g : Fin m → Fin r // ∑ t, (g t : ℕ) = H} =
      ((Finset.univ : Finset (Fin m)).inf (fun i => (bad i)ᶜ)).card := by
    exact (Fintype.card_congr ((huangGoodEquiv r m H).symm.trans
      (Equiv.subtypeEquivRight fun g => (good_mem g).symm))).trans (Fintype.card_coe _)
  have inter_mem (s : Finset (Fin m)) (g : HuangWeak m H) :
      g ∈ s.inf bad ↔ ∀ i ∈ s, r ≤ g.val i := by simp [Finset.mem_inf, bad_mem]
  have inter_card (s : Finset (Fin m)) : (s.inf bad).card =
      if s.card * r ≤ H then (m + (H - s.card * r) - 1).choose (H - s.card * r) else 0 := by
    split_ifs with hs
    · rw [← huangWeakCount, ← Fintype.card_coe (s.inf bad)]
      exact (Nat.card_eq_fintype_card (α := ↥(s.inf bad))).symm.trans
        (Nat.card_congr ((Equiv.subtypeEquivRight fun g => inter_mem s g).trans (huangShift s hs)))
    · apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hg
      apply hs
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
        (f := huangOffset r s) (g := g.val) (fun i _ => by
          by_cases hi : i ∈ s
          · simpa [huangOffset, hi] using (inter_mem s g).mp hg i hi
          · simp [huangOffset, hi])
      rwa [huangOffset_sum, g.property] at hsum
  rw [good_card, Finset.inclusion_exclusion_card_inf_compl]
  simp_rw [inter_card]
  rw [Finset.sum_powerset_apply_card (fun l =>
    (-1 : ℤ) ^ l * ↑(if l * r ≤ H then (m + (H - l * r) - 1).choose (H - l * r) else 0))]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp [mul_left_comm, mul_assoc]

-- Separate a word into its marked positions, their colors, and its shift counts.
private abbrev MarkSet (i m : ℕ) := {s : Finset (Fin i) // s.card = m}

private noncomputable def markIndex {i m : ℕ} (s : MarkSet i m) : ↥s.val ≃ Fin m :=
  Fintype.equivFinOfCardEq ((Fintype.card_coe s.val).trans s.prop)

private noncomputable def label {i m r : ℕ} (s : MarkSet i m) (g : Fin m → Fin r) (t : Fin i) :
    Option (Fin r) :=
  if ht : t ∈ s.val then some (g (markIndex s ⟨t, ht⟩)) else none

private theorem label_marks {i m r : ℕ} (s : MarkSet i m) (g : Fin m → Fin r) :
    Finset.univ.filter (fun t => (label s g t).isSome) = s.val := by
  ext t
  by_cases ht : t ∈ s.val <;> simp [label, ht]

private theorem label_sum {i m r : ℕ} (s : MarkSet i m) (g : Fin m → Fin r) :
    ∑ t, (label s g t).elim 0 (fun c => (c : ℕ)) = ∑ t, (g t : ℕ) := by
  classical
  simp only [label, apply_dite (fun o : Option (Fin r) => o.elim 0 (fun c => (c : ℕ))),
    Option.elim_some, Option.elim_none]
  calc
    _ = ∑ t : ↥s.val, (g (markIndex s t) : ℕ) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach_eq_sum_dite s.val (fun t => (g (markIndex s t) : ℕ))).symm
    _ = _ := Fintype.sum_equiv (markIndex s) _ _ (fun _ => rfl)

private theorem label_injective {i m r : ℕ} {s s' : MarkSet i m} {g g' : Fin m → Fin r}
    (h : label s g = label s' g') : s = s' ∧ g = g' := by
  have hs : s = s' := Subtype.ext (by rw [← label_marks s g, ← label_marks s' g', h])
  subst s'
  refine ⟨rfl, funext fun t => ?_⟩
  let u := (markIndex s).symm t
  have he := congrFun h u.val
  simpa [label, u.property, u] using he

private theorem label_surjective {i m r : ℕ} (f : Fin i → Option (Fin r))
    (hf : (Finset.univ.filter fun t => (f t).isSome).card = m) :
    ∃ (s : MarkSet i m) (g : Fin m → Fin r), label s g = f := by
  let s : MarkSet i m := ⟨Finset.univ.filter fun t => (f t).isSome, hf⟩
  have hm (t : Fin i) : t ∈ s.val ↔ (f t).isSome := by simp [s]
  let g (u : Fin m) := (f ((markIndex s).symm u).val).get
    ((hm _).mp ((markIndex s).symm u).prop)
  refine ⟨s, g, funext fun t => ?_⟩
  by_cases ht : t ∈ s.val
  · simp [label, ht, g]
  · have he : f t = none := by simpa [hm, Option.isSome_iff_ne_none] using ht
    simp [label, ht, he]

private theorem markCount_ofFn {k i : ℕ} (f : Fin i → Code k) :
    markCount (List.ofFn f) = (Finset.univ.filter fun t => (f t).2.isSome).card := by
  rw [markCount, ← List.countP_eq_length_filter, List.countP_ofFn]

private theorem shiftCount_ofFn {k i : ℕ} (f : Fin i → Code k) :
    shiftCount (List.ofFn f) = ∑ t, (f t).1 := by
  simp only [shiftCount, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

private theorem colorTotal_ofFn {k i : ℕ} (f : Fin i → Code k) :
    colorTotal (List.ofFn f) = ∑ t, (f t).2.elim 0 (fun c => (c : ℕ)) := by
  simp only [colorTotal, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

private abbrev Table (k m n : ℕ) :=
  Σ i : Fin (n + 1), Σ j : Fin (n + 1),
    {g : Fin m → Fin (k - 1) // (i : ℕ) + (k + 1) * m + (j : ℕ) * k + ∑ t, (g t : ℕ) = n} ×
      (MarkSet i m × HuangWeak i j)

private noncomputable def tableWord {k m n : ℕ} (d : Table k m n) : CodeWord k m n := by
  obtain ⟨i, j, ⟨g, hg⟩, s, q⟩ := d
  let f (t : Fin (i : ℕ)) : Code k := (q.val t, label s g t)
  have hm : markCount (List.ofFn f) = m := by
    rw [markCount_ofFn, label_marks s g, s.prop]
  have hq : shiftCount (List.ofFn f) = j := shiftCount_ofFn f |>.trans q.prop
  have hc : colorTotal (List.ofFn f) = ∑ t, (g t : ℕ) := (colorTotal_ofFn f).trans (label_sum s g)
  exact ⟨List.ofFn f, by rw [codeWeight, List.length_ofFn, hm, hq, hc, hg], hm⟩

private theorem tableWord_length {k m n : ℕ} (d : Table k m n) :
    (tableWord d).val.length = d.1 := by
  rcases d with ⟨i, j, g, s, q⟩
  exact List.length_ofFn

private theorem tableWord_shifts {k m n : ℕ} (d : Table k m n) :
    shiftCount (tableWord d).val = d.2.1 := by
  rcases d with ⟨i, j, g, s, q⟩
  exact (shiftCount_ofFn _).trans q.prop

private noncomputable def tableWordEquiv {k m n : ℕ} (hk : 0 < k) :
    Table k m n ≃ CodeWord k m n := by
  classical
  apply Equiv.ofBijective tableWord
  constructor
  · rintro ⟨i, j, g, s, q⟩ ⟨i', j', g', s', q'⟩ h
    have hi := congrArg (fun w : CodeWord k m n => w.val.length) h
    simp only [tableWord_length] at hi
    have hj := congrArg (fun w : CodeWord k m n => shiftCount w.val) h
    simp only [tableWord_shifts] at hj
    obtain rfl : i = i' := Fin.ext hi
    obtain rfl : j = j' := Fin.ext hj
    have hf := List.ofFn_injective (congrArg Subtype.val h)
    change (fun t => (q.val t, label s g.val t)) = (fun t => (q'.val t, label s' g'.val t)) at hf
    obtain ⟨rfl, hg⟩ := label_injective (congrArg (fun f t => (f t).2) hf)
    obtain rfl : g = g' := Subtype.ext hg
    obtain rfl : q = q' := Subtype.ext (congrArg (fun f t => (f t).1) hf)
    rfl
  · rintro ⟨ps, hsum, hm⟩
    rw [codeWeight, hm] at hsum
    have hi : ps.length ≤ n := by omega
    have hj : shiftCount ps ≤ n := le_trans
      (by simpa using Nat.mul_le_mul_left (shiftCount ps) hk) (by omega)
    let i : Fin (n + 1) := ⟨ps.length, by omega⟩
    let j : Fin (n + 1) := ⟨shiftCount ps, by omega⟩
    let f : Fin (i : ℕ) → Code k := ps.get
    have hps : List.ofFn f = ps := List.ofFn_getElem
    obtain ⟨s, g, he⟩ := label_surjective (fun t => (f t).2) (by rw [← markCount_ofFn, hps, hm])
    have hg : (i : ℕ) + (k + 1) * m + (j : ℕ) * k + ∑ t, (g t : ℕ) = n := by
      rw [← label_sum s g, he, ← colorTotal_ofFn, hps]
      exact hsum
    let q : HuangWeak i j := ⟨fun t => (f t).1, by rw [← shiftCount_ofFn, hps]⟩
    refine ⟨⟨i, j, ⟨g, hg⟩, s, q⟩, Subtype.ext ?_⟩
    change List.ofFn (fun t => ((f t).1, label s g t)) = ps
    simpa only [he, Prod.eta] using hps

-- The shift count determines the sign; the other data contribute cardinalities.
private theorem tableSigned (k m n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    compositionOddMinusEven (n + k - 1)
      (fun c => (c.blocks.filter fun a => a < k).length = m ∧
        IsHuangSmallPartPlacement k c.blocks) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ j * (i.choose m : ℤ) * ((i + j - 1).choose j : ℤ) *
          (Fintype.card {g : Fin m → Fin (k - 1) //
            i + (k + 1) * m + j * k + ∑ t, (g t : ℕ) = n} : ℤ) := by
  classical
  let weak (i j : ℕ) : Fintype (HuangWeak i j) :=
    Fintype.ofEquiv _ (Sym.equivNatSumOfFintype (Fin i) j)
  let (i j : Fin (n + 1)) : Fintype (HuangWeak i j) := weak i j
  let e := (tableWordEquiv (m := m) (n := n) hk).trans (codeWordTarget hk hn)
  have hsign (d : Table k m n) : (-1 : ℤ) ^ (e d).val.length.succ = (-1) ^ (d.2.1 : ℕ) := by
    change (-1 : ℤ) ^ ((codeWordTarget hk hn (tableWord d)).val.length + 1) = _
    rw [codeWordTarget_length, tableWord_shifts, pow_add, pow_mul]
    norm_num
  let P (c : Composition (n + k - 1)) :=
    (c.blocks.filter fun a => a < k).length = m ∧ IsHuangSmallPartPlacement k c.blocks
  change compositionOddMinusEven (n + k - 1) P = _
  let _ : DecidablePred P := fun _ => Classical.propDecidable _
  rw [compositionOddMinusEven]
  rw [← Finset.sum_filter (s := Finset.univ) P (fun c => (-1 : ℤ) ^ (c.length + 1))]
  rw [Finset.sum_subtype _ (by simp : ∀ c, c ∈ Finset.univ.filter P ↔ P c)]
  change ∑ v : Target k m n, (-1 : ℤ) ^ (v.val.length + 1) = _
  calc
    _ = ∑ d : Table k m n, (-1 : ℤ) ^ (d.2.1 : ℕ) :=
      (Fintype.sum_equiv e _ _ fun d => (hsign d).symm).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp_rw [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_finset_len, Fintype.card_fin, ← Nat.card_eq_fintype_card (α := HuangWeak _ _),
        huangWeakCount, nsmul_eq_mul, Nat.cast_mul]
      conv_rhs => simp only [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ac_rfl

private theorem colorCountToSum (r m N a j i : ℕ) :
    (-1 : ℤ) ^ j * (i.choose m : ℤ) * ((i + j - 1).choose j : ℤ) *
        (Fintype.card {g : Fin m → Fin r // a + ∑ t, (g t : ℕ) = N} : ℤ) =
      ∑ l ∈ Finset.range (m + 1), ∑ h ∈ Finset.range (N + 1),
        if a + l * r + h = N then
          (-1 : ℤ) ^ (l + j) * (i.choose m : ℤ) * ((i + j - 1).choose j : ℤ) *
            (m.choose l : ℤ) * ((m + h - 1).choose h : ℤ)
        else 0 := by
  classical
  by_cases ha : a ≤ N
  · have hcard : Fintype.card {g : Fin m → Fin r // a + ∑ t, (g t : ℕ) = N} =
        Fintype.card {g : Fin m → Fin r // ∑ t, (g t : ℕ) = N - a} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun _ => by omega)
    rw [hcard, huangBoundedCount, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l * r ≤ N - a
    · let h₀ := N - a - l * r
      have he : a + l * r + h₀ = N := by dsimp [h₀]; omega
      rw [Finset.sum_eq_single h₀]
      · rw [ite_eq_left hl, ite_eq_left he, pow_add]
        dsimp only [h₀]
        ac_rfl
      · intro h _ hh
        rw [ite_eq_right (show a + l * r + h ≠ N by omega)]
      · intro hh
        exfalso
        exact hh (Finset.mem_range.mpr (by omega))
    · rw [ite_eq_right hl, mul_zero]
      symm
      exact Finset.sum_eq_zero fun h _ => ite_eq_right (by omega)
  · let : IsEmpty {g : Fin m → Fin r // a + ∑ t, (g t : ℕ) = N} :=
      ⟨fun g => ha (g.prop ▸ Nat.le_add_right _ _)⟩
    simp only [Fintype.card_eq_zero, Nat.cast_zero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro l _
    exact Finset.sum_eq_zero fun h _ => ite_eq_right (by omega)

end compositionOddMinusEven_huang_eq_sum

open compositionOddMinusEven_huang_eq_sum in
/-- **Signed count of Huang's compositions, binomial form.** Let $k, n \ge 1$ and $m \ge 0$.
Among the compositions of $n + k - 1$ with exactly $m$ parts less than $k$ in which every part
less than $k$ is preceded by a part at least $k$ and followed by a part that is either the last
part or greater than $k$, let $b^{(m)}_{k,n}$ be the number with an odd number of parts minus the
number with an even number of parts. Then $b^{(m)}_{k,n}$ is the sum of
$(-1)^{\ell+j} \binom{i}{m} \binom{i+j-1}{j} \binom{m}{\ell} \binom{m+h-1}{h}$ over all
$i, j, \ell, h \ge 0$ with $i + (k+1)m + jk + \ell(k-1) + h = n$, where $\binom{-1}{0} = 1$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 16
(`jis-2024-24.6.5-thm-16`). -/
public theorem compositionOddMinusEven_huang_eq_sum (k m n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    compositionOddMinusEven (n + k - 1)
        (fun c => (c.blocks.filter fun a => a < k).length = m ∧
          IsHuangSmallPartPlacement k c.blocks)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (m + 1), ∑ h ∈ Finset.range (n + 1),
            if i + (k + 1) * m + j * k + l * (k - 1) + h = n then
              (-1 : ℤ) ^ (l + j) * (i.choose m : ℤ) * ((i + j - 1).choose j : ℤ) *
                (m.choose l : ℤ) * ((m + h - 1).choose h : ℤ)
            else 0 := by
  rw [tableSigned k m n hk hn]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact colorCountToSum (k - 1) m n (i + (k + 1) * m + j * k) j i

end

end MetaMathlibExt
