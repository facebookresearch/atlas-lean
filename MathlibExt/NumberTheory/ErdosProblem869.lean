/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Disjoint

@[expose] public section

/-!
# Erdős Problem #869

We construct two disjoint asymptotic bases of order two whose union contains no minimal
basis, proving `Statement_refuted`.

At each scale `t = 610 * 100^k`, colour two intervals on either side of `100t` periodically.
In each colour every sum from `5t` to `500t`, except `200t`, has a representation by two
elements at least `t` (the upper end uses the next scale). Reflection about `100t` exchanges
disjoint residue classes, so the periodic sets cannot represent `200t`.

Following Larsen's selection argument, choose a red and a blue element at each stage and
adjoin their reflections in the same colours. These give the only representations of `200t`.
Every red-blue pair whose elements are within a factor of 500 of each other is chosen at
its pairing-function index. Thus any subbasis must meet every sufficiently large such pair.
For an ordinary sum, crossing the endpoints of its red and blue representations shows that
one representation survives intact. For exceptional sums, both summands in every representation
tend to infinity with the stage. Hence deleting any one element preserves the basis property.
-/

namespace MathlibExt.NumberTheory.ErdosProblem869Wanted

/-- **Sumset of a set of naturals.** For a set $A$ of natural numbers, $A + A$ is the set of
natural numbers $n$ such that $n = a + b$ for some $a, b \in A$. -/
def addSumset (A : Set ℕ) : Set ℕ :=
  { n | ∃ a ∈ A, ∃ b ∈ A, a + b = n }

/-- **Additive basis of order 2.** A set $A$ of natural numbers is an additive basis of order $2$
if there is a natural number $N$ such that every natural number $n \ge N$ can be written as
$n = a + b$ with $a, b \in A$. -/
def IsAdditiveBasisOrder2 (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ a ∈ A, ∃ b ∈ A, a + b = n

/-- **Minimal additive basis of order 2.** A set $A$ of natural numbers is a minimal additive
basis of order $2$ if it is an additive basis of order $2$ and, for every $a \in A$, infinitely
many natural numbers do not lie in the sumset $(A \setminus \{a\}) + (A \setminus \{a\})$. -/
def IsMinimalAdditiveBasisOrder2 (A : Set ℕ) : Prop :=
  IsAdditiveBasisOrder2 A ∧ ∀ a ∈ A, ((addSumset (A \ {a}))ᶜ).Infinite

/-- **Erdős Problem 869 (disjoint bases and minimal bases).** The statement that for all disjoint
sets $A_1$ and $A_2$ of natural numbers that are both additive bases of order $2$, there is a set
$B \subseteq A_1 \cup A_2$ that is a minimal additive basis of order $2$. -/
def Statement : Prop :=
  ∀ A1 A2 : Set ℕ, Disjoint A1 A2 → IsAdditiveBasisOrder2 A1 →
    IsAdditiveBasisOrder2 A2 →
    ∃ B : Set ℕ, B ⊆ A1 ∪ A2 ∧ IsMinimalAdditiveBasisOrder2 B

-- The four classes modulo 61 are each additive bases of the cyclic group. Classes 0 and 1
-- colour a lower interval, and the negatives of classes 2 and 3 colour an upper interval.
private def palette : Array ℕ :=
  #[3, 3, 1, 3, 2, 0, 2, 1, 3, 0, 0, 1, 1, 1, 0, 2, 0, 2, 3, 2, 0,
    2, 2, 2, 3, 2, 1, 3, 0, 1, 0, 0, 1, 0, 2, 1, 2, 0, 0, 1, 1, 3,
    1, 3, 1, 2, 2, 0, 1, 3, 0, 1, 0, 3, 3, 2, 3, 3, 3, 0, 2]

private def low (c : Fin 2) (x : ℕ) : Prop := palette[x % 61]! = c.val

private def high (c : Fin 2) (x : ℕ) : Prop := palette[(61 - x % 61) % 61]! = c.val + 2

private def lane (upper : Bool) (c : Fin 2) (x : ℕ) : Prop :=
  if upper then high c x else low c x

private instance decLane (u : Bool) (c : Fin 2) (x : ℕ) : Decidable (lane u c x) := by
  cases u <;> unfold lane high low <;> infer_instance

private theorem lane_mod (u c x) : lane u c (x % 61) ↔ lane u c x := by
  simp [lane, low, high]

set_option maxRecDepth 4096 in
private theorem residues : ∀ (u : Bool) (c : Fin 2) (r : Fin 61),
    ∃ a : Fin 61, lane u c a ∧ lane u c (r.val + 61 - a.val) := by decide

-- A translation of a residue witness into an interval of 61 possible first summands.
private theorem interval_rep (u : Bool) (c : Fin 2) (n p : ℕ) (hp : p + 61 ≤ n) :
    ∃ x y, p ≤ x ∧ x ≤ p + 60 ∧ lane u c x ∧ lane u c y ∧ x + y = n := by
  obtain ⟨a, ha, hb⟩ := residues u c ⟨n % 61, by omega⟩
  let x := p + (a.val + 61 - p % 61) % 61
  have hx : x % 61 = a.val := by dsimp [x]; omega
  have hy : (n - x) % 61 = (n % 61 + 61 - a.val) % 61 := by
    have : x ≤ n := by dsimp [x]; omega
    omega
  refine ⟨x, n - x, by dsimp [x]; omega, by dsimp [x]; omega, ?_, ?_, by dsimp [x]; omega⟩
  · rwa [← lane_mod, hx]
  · rw [← lane_mod, hy, lane_mod]
    exact hb

-- Center a fixed window at 244 (a multiple of the period). In the window, both colours
-- represent each nearby sum except the exact double of the center.
private def window (c : Fin 2) (x : ℕ) : Prop :=
  (x < 244 ∧ low c x) ∨ (244 < x ∧ high c x)

private instance decWindow (c : Fin 2) (x : ℕ) : Decidable (window c x) := by
  unfold window low high
  infer_instance

-- Nonzero shifts have a representation across the two halves. At shifts divisible by
-- the period we instead use two points on the same side of the center.
set_option maxRecDepth 4096 in
private theorem mixed_residues : ∀ (c : Fin 2) (s : Fin 61), s.val ≠ 0 →
    ∃ a : Fin 61, lane false c a ∧ lane true c (s.val + 61 - a.val) := by decide

private def sameSide (c : Fin 2) (j : Fin 5) : Fin 489 :=
  if j < 2 then (if c = 0 then 211 else 209) else (if c = 0 then 250 else 247)

private theorem window_rep (c : Fin 2) (r : Fin 245) (hr : r.val ≠ 122) :
    ∃ a : Fin 489, a.val ≤ 366 + r.val ∧ window c a ∧ window c (366 + r.val - a.val) := by
  by_cases h : r.val % 61 = 0
  · have check : ∀ (b : Fin 2) (j : Fin 5), j.val ≠ 2 →
        let a := sameSide b j
        a.val ≤ 366 + 61 * j.val ∧ window b a ∧ window b (366 + 61 * j.val - a.val) := by
      decide
    let j : Fin 5 := ⟨r.val / 61, by omega⟩
    have hj : 61 * j.val = r.val := by dsimp [j]; omega
    exact ⟨sameSide c j, hj ▸ check c j (by omega)⟩
  · obtain ⟨a, ha, hb⟩ := mixed_residues c ⟨r.val % 61, by omega⟩ h
    refine ⟨⟨a.val, by omega⟩, by dsimp; omega, Or.inl ⟨by dsimp; omega, ha⟩,
      Or.inr ⟨by dsimp; omega, ?_⟩⟩
    change high c (366 + r.val - a.val)
    change high c (r.val % 61 + 61 - a.val) at hb
    have he : (366 + r.val - a.val) % 61 = (r.val % 61 + 61 - a.val) % 61 := by omega
    simpa only [high, he] using hb

private def scale : ℕ → ℕ
  | 0 => 610
  | k + 1 => 100 * scale k

private theorem scale_large (k) : 610 + k ≤ scale k := by
  induction k with
  | zero => decide
  | succ k ih => rw [scale]; omega

private theorem scale_dvd (k) : 61 ∣ scale k := by
  induction k with
  | zero => decide
  | succ k ih => exact dvd_mul_of_dvd_right ih _

private theorem scale_gap {i j : ℕ} (h : i < j) : 100 * scale i ≤ scale j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [scale]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · have := ih h
      omega
    · rfl

private def block (k : ℕ) (c : Fin 2) (x : ℕ) : Prop :=
  (2 * scale k < x ∧ x < 100 * scale k ∧ low c x) ∨
  (100 * scale k < x ∧ x ≤ 150 * scale k ∧ high c x)

private def core (c : Fin 2) : Set ℕ := {x | ∃ k, block k c x}

private theorem block_bounds {k c x} (h : block k c x) :
    2 * scale k < x ∧ x ≤ 150 * scale k := by
  rcases h with h | h <;> obtain ⟨_, _, _⟩ := h <;> omega

private theorem core_disjoint {a b x} (ha : x ∈ core a) (hb : x ∈ core b) : a = b := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hi' := block_bounds hi
  have hj' := block_bounds hj
  obtain rfl : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · have := scale_gap h
      omega
    · exact h
    · have := scale_gap h
      omega
  rcases hi with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rcases hj with ⟨_, _, h'⟩ | ⟨_, _, h'⟩
  all_goals first | omega | (apply Fin.ext; unfold low at *; omega) |
    (apply Fin.ext; unfold high at *; omega)

private theorem regular_rep (k : ℕ) (c : Fin 2) {n : ℕ}
    (hn : 5 * scale k ≤ n) (hn' : n ≤ 500 * scale k) (hne : n ≠ 200 * scale k) :
    ∃ x ∈ core c, ∃ y ∈ core c, scale k ≤ x ∧ scale k ≤ y ∧ x + y = n := by
  let t := scale k
  change 5 * t ≤ n at hn
  change n ≤ 500 * t at hn'
  change n ≠ 200 * t at hne
  have ht : 610 ≤ t := (Nat.le_add_right _ _).trans (scale_large k)
  by_cases below : n < 200 * t - 122
  · obtain ⟨x, y, hx, hx', hcx, hcy, hxy⟩ :=
      interval_rep false c n (n / 2 - 30) (by omega)
    exact ⟨x, ⟨k, Or.inl ⟨by omega, by omega, hcx⟩⟩,
      y, ⟨k, Or.inl ⟨by omega, by omega, hcy⟩⟩, by omega, by omega, hxy⟩
  by_cases near : n ≤ 200 * t + 122
  · let r : Fin 245 := ⟨n - (200 * t - 122), by omega⟩
    have hr : r.val + 200 * t = n + 122 := by dsimp [r]; omega
    obtain ⟨a, ha, hca, hcb⟩ := window_rep c r (by omega)
    let d := 100 * t - 244
    have hd : d % 61 = 0 := by
      obtain ⟨v, hv⟩ := scale_dvd k
      change t = 61 * v at hv
      dsimp [d]
      omega
    have move {b : ℕ} (hb : window c b) (hbound : b ≤ 610) : d + b ∈ core c := by
      refine ⟨k, ?_⟩
      rcases hb with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · exact Or.inl ⟨by dsimp [d]; omega, by dsimp [d]; omega,
          by simpa [low, Nat.add_mod, hd] using hc⟩
      · exact Or.inr ⟨by dsimp [d]; omega, by dsimp [d]; omega,
          by simpa [high, Nat.add_mod, hd] using hc⟩
    exact ⟨_, move hca (by omega), _, move hcb (by omega), by dsimp [d]; omega,
      by dsimp [d]; omega, by dsimp [d]; omega⟩
  by_cases above : n ≤ 280 * t
  · obtain ⟨x, y, hx, hx', hcx, hcy, hxy⟩ :=
      interval_rep true c n (n / 2 - 30) (by omega)
    exact ⟨x, ⟨k, Or.inr ⟨by omega, by omega, hcx⟩⟩,
      y, ⟨k, Or.inr ⟨by omega, by omega, hcy⟩⟩, by omega, by omega, hxy⟩
  obtain ⟨x, y, hx, hx', hcx, hcy, hxy⟩ := interval_rep false c n (3 * t) (by omega)
  refine ⟨x, ⟨k, Or.inl ⟨by omega, by omega, hcx⟩⟩,
    y, ⟨k + 1, Or.inl ⟨?_, ?_, hcy⟩⟩, by omega, by omega, hxy⟩ <;> rw [scale] <;> omega

private theorem exists_scale {n : ℕ} (hn : 5 * scale 0 ≤ n) :
    ∃ k, 5 * scale k ≤ n ∧ n ≤ 500 * scale k := by
  have exists_upper (j : ℕ) (h : n ≤ 500 * scale j) :
      ∃ k, 5 * scale k ≤ n ∧ n ≤ 500 * scale k := by
    induction j with
    | zero => exact ⟨0, hn, h⟩
    | succ j ih =>
      by_cases hj : n ≤ 500 * scale j
      · exact ih hj
      · exact ⟨j + 1, by rw [scale]; omega, h⟩
  exact exists_upper n (by have := scale_large n; omega)

-- Stage pair(r,b) tests the pair (r,b) whenever its members have the right colours
-- and are comparable. Each fixed element occurs in only finitely many such pairs.
private def eligible (k : ℕ) : Prop :=
  k.unpair.1 ∈ core 0 ∧ k.unpair.2 ∈ core 1 ∧
    k.unpair.1 ≤ 500 * k.unpair.2 ∧ k.unpair.2 ≤ 500 * k.unpair.1

private def backup (k : ℕ) (c : Fin 2) : ℕ := 3 * scale k + (if c = 0 then 5 else 2)

private theorem backup_mem (k : ℕ) (c : Fin 2) : backup k c ∈ core c := by
  have ht := scale_large k
  obtain ⟨v, hv⟩ := scale_dvd k
  have hc : c = 0 ∨ c = 1 := by omega
  rcases hc with rfl | rfl
  · refine ⟨k, Or.inl ⟨by simp [backup]; omega, by simp [backup]; omega, ?_⟩⟩
    have h : backup k 0 % 61 = 5 := by simp [backup, hv]; omega
    unfold low
    rw [h]
    decide
  · refine ⟨k, Or.inl ⟨by simp [backup]; omega, by simp [backup]; omega, ?_⟩⟩
    have h : backup k 1 % 61 = 2 := by simp [backup, hv]; omega
    unfold low
    rw [h]
    decide

private noncomputable def anchor (k : ℕ) (c : Fin 2) : ℕ := by
  classical
  exact if eligible k then (if c = 0 then k.unpair.1 else k.unpair.2) else backup k c

private theorem anchor_mem (k : ℕ) (c : Fin 2) : anchor k c ∈ core c := by
  by_cases h : eligible k
  · have hc : c = 0 ∨ c = 1 := by omega
    rcases hc with rfl | rfl
    · simpa [anchor, h] using h.1
    · simpa [anchor, h] using h.2.1
  · simpa [anchor, h] using backup_mem k c

private theorem anchor_le (k : ℕ) (c : Fin 2) : anchor k c ≤ 4 * scale k := by
  have := scale_large k
  have := Nat.unpair_left_le k
  have := Nat.unpair_right_le k
  unfold anchor backup
  split_ifs <;> omega

private theorem anchors_escape (m : ℕ) : ∃ K, ∀ k ≥ K, ∀ c, m < anchor k c := by
  refine ⟨(500 * m + 1) ^ 2 + m + 1, ?_⟩
  intro k hk c
  by_cases h : eligible k
  · have ⟨_, _, h₁, h₂⟩ := h
    have hpair := Nat.pair_lt_max_add_one_sq k.unpair.1 k.unpair.2
    rw [Nat.pair_unpair] at hpair
    have hmax : 500 * m < max k.unpair.1 k.unpair.2 := by
      by_contra! small
      have : (max k.unpair.1 k.unpair.2 + 1) ^ 2 ≤ (500 * m + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.succ_le_succ small) 2
      omega
    simp [anchor, h]
    split <;> omega
  · have := scale_large k
    simp [anchor, h, backup]
    split <;> omega

private noncomputable def satellite (k : ℕ) (c : Fin 2) : ℕ := 200 * scale k - anchor k c

private theorem satellite_bounds (k : ℕ) (c : Fin 2) :
    196 * scale k ≤ satellite k c ∧ satellite k c ≤ 200 * scale k := by
  have := anchor_le k c
  unfold satellite
  omega

private noncomputable def colour (c : Fin 2) : Set ℕ := core c ∪ Set.range (fun k => satellite k c)

-- Earlier stages lie below 2t, and the next stage starts above 200t.
private theorem locate {k c x} (hx : x ∈ colour c) (h : x ≤ 200 * scale k) :
    x ≤ 2 * scale k ∨ block k c x ∨ x = satellite k c := by
  rcases hx with ⟨i, hi⟩ | ⟨i, rfl⟩
  · have := block_bounds hi
    rcases lt_trichotomy i k with e | rfl | e
    · have := scale_gap e
      exact Or.inl (by omega)
    · exact Or.inr (Or.inl hi)
    · have := scale_gap e
      omega
  · dsimp only at h ⊢
    have := satellite_bounds i c
    rcases lt_trichotomy i k with e | rfl | e
    · have := scale_gap e
      exact Or.inl (by omega)
    · exact Or.inr (Or.inr rfl)
    · have := scale_gap e
      have := scale_large k
      omega

private theorem satellite_colour {k c b} (hx : satellite k c ∈ colour b) : c = b := by
  have hs := satellite_bounds k c
  have := scale_large k
  rcases locate hx hs.2 with h | h | h
  · omega
  · have := block_bounds h
    omega
  · have ha := anchor_le k c
    have hb := anchor_le k b
    have eq : anchor k c = anchor k b := by unfold satellite at h; omega
    exact core_disjoint (anchor_mem k c) (eq ▸ anchor_mem k b)

private theorem colours_disjoint : Disjoint (colour 0) (colour 1) := by
  refine Set.disjoint_left.mpr ?_
  intro x hr hb
  rcases hr with h | ⟨k, rfl⟩
  · rcases hb with h' | ⟨k, rfl⟩
    · have := core_disjoint h h'
      contradiction
    · have := satellite_colour (b := 0) (Or.inl h)
      contradiction
  · have := satellite_colour hb
    contradiction

private theorem special_rep {k a b x y} (hx : x ∈ colour a) (hy : y ∈ colour b)
    (hs : x + y = 200 * scale k) :
    ∃ c, (x = anchor k c ∧ y = satellite k c) ∨ (y = anchor k c ∧ x = satellite k c) := by
  have := scale_large k
  have hax := anchor_le k a
  have hby := anchor_le k b
  by_cases sx : x = satellite k a
  · exact ⟨a, Or.inr ⟨by unfold satellite at sx; omega, sx⟩⟩
  by_cases sy : y = satellite k b
  · exact ⟨b, Or.inl ⟨by unfold satellite at sy; omega, sy⟩⟩
  obtain ⟨v, hv⟩ := scale_dvd k
  have clash {i j : Fin 2} {p q : ℕ} (hp : low i p) (hq : high j q)
      (he : p + q = 200 * scale k) : False := by
    have hm : (61 - q % 61) % 61 = p % 61 := by omega
    unfold low at hp
    unfold high at hq
    rw [hm] at hq
    omega
  rcases locate hx (by omega : x ≤ 200 * scale k) with h | h | h <;>
    rcases locate hy (by omega : y ≤ 200 * scale k) with h' | h' | h'
  all_goals try contradiction
  all_goals try obtain ⟨_, _, _⟩ | ⟨_, _, _⟩ := h
  all_goals try obtain ⟨_, _, _⟩ | ⟨_, _, _⟩ := h'
  all_goals first | omega | exact (clash ‹_› ‹_› hs).elim |
    exact (clash ‹_› ‹_› (by omega)).elim

private theorem colour_basis (c : Fin 2) : IsAdditiveBasisOrder2 (colour c) := by
  refine ⟨5 * scale 0, ?_⟩
  intro n hn
  obtain ⟨k, hk, hk'⟩ := exists_scale hn
  by_cases he : n = 200 * scale k
  · exact ⟨anchor k c, Or.inl (anchor_mem k c), satellite k c, Or.inr ⟨k, rfl⟩,
      by have := anchor_le k c; unfold satellite; omega⟩
  · obtain ⟨x, hx, y, hy, _, _, h⟩ := regular_rep k c hk hk' he
    exact ⟨x, Or.inl hx, y, Or.inl hy, h⟩

private theorem union_colour {D : Set ℕ} (hD : D ⊆ colour 0 ∪ colour 1) {x} (hx : x ∈ D) :
    ∃ c, x ∈ colour c := by
  rcases hD hx with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

private theorem hits_pair {D : Set ℕ} (hD : D ⊆ colour 0 ∪ colour 1) {N : ℕ}
    (basis : ∀ n ≥ N, n ∈ addSumset D) {r b : ℕ} (hr : r ∈ core 0) (hb : b ∈ core 1)
    (hrb : r ≤ 500 * b) (hbr : b ≤ 500 * r) (hN : N ≤ r) : r ∈ D ∨ b ∈ D := by
  let k := Nat.pair r b
  have hek : eligible k := by simpa [eligible, k] using And.intro hr ⟨hb, hrb, hbr⟩
  have hkr : anchor k 0 = r := by simp [anchor, hek, k]
  have hkb : anchor k 1 = b := by simp [anchor, hek, k]
  have hlarge : N ≤ 200 * scale k := by
    have : r ≤ k := Nat.left_le_pair r b
    have := scale_large k
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := basis _ hlarge
  obtain ⟨cx, hcx⟩ := union_colour hD hx
  obtain ⟨cy, hcy⟩ := union_colour hD hy
  obtain ⟨c, hc⟩ := special_rep hcx hcy hxy
  have hit : anchor k c ∈ D := by rcases hc with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
  have cases : c = 0 ∨ c = 1 := by omega
  rcases cases with rfl | rfl
  · exact Or.inl (hkr ▸ hit)
  · exact Or.inr (hkb ▸ hit)

-- All four cross-colour pairs of endpoints must be hit. Thus at least one of the two
-- monochromatic representations survives in D, with both summands large.
private theorem keep_regular {D : Set ℕ} (hD : D ⊆ colour 0 ∪ colour 1) {N a n k : ℕ}
    (basis : ∀ m ≥ N, m ∈ addSumset D) (ha : a < scale k) (hN : N ≤ scale k)
    (hn : 5 * scale k ≤ n) (hn' : n ≤ 500 * scale k) (he : n ≠ 200 * scale k) :
    n ∈ addSumset (D \ {a}) := by
  obtain ⟨x, hx, y, hy, sx, sy, hxy⟩ := regular_rep k 0 hn hn' he
  obtain ⟨z, hz, w, hw, sz, sw, hzw⟩ := regular_rep k 1 hn hn' he
  have hit {r b : ℕ} (hr : r ∈ core 0) (hb : b ∈ core 1)
      (rs : scale k ≤ r) (bs : scale k ≤ b) (rn : r ≤ n) (bn : b ≤ n) : r ∈ D ∨ b ∈ D :=
    hits_pair hD basis hr hb (by omega) (by omega) (by omega)
  have survives : (x ∈ D ∧ y ∈ D) ∨ (z ∈ D ∧ w ∈ D) := by
    have := hit hx hz sx sz (by omega) (by omega)
    have := hit hx hw sx sw (by omega) (by omega)
    have := hit hy hz sy sz (by omega) (by omega)
    have := hit hy hw sy sw (by omega) (by omega)
    tauto
  rcases survives with ⟨dx, dy⟩ | ⟨dz, dw⟩
  · exact ⟨x, ⟨dx, by simpa using (show x ≠ a by omega)⟩,
      y, ⟨dy, by simpa using (show y ≠ a by omega)⟩, hxy⟩
  · exact ⟨z, ⟨dz, by simpa using (show z ≠ a by omega)⟩,
      w, ⟨dw, by simpa using (show w ≠ a by omega)⟩, hzw⟩

private theorem erase_basis {D : Set ℕ} (hD : D ⊆ colour 0 ∪ colour 1)
    (basis : IsAdditiveBasisOrder2 D) (a : ℕ) : IsAdditiveBasisOrder2 (D \ {a}) := by
  obtain ⟨N, hN⟩ := basis
  obtain ⟨K, hK⟩ := anchors_escape a
  refine ⟨5 * scale 0 + 500 * (a + N + 1) + 200 * scale K, ?_⟩
  intro n hn
  obtain ⟨k, slo, shi⟩ := exists_scale (n := n) (by omega)
  by_cases he : n = 200 * scale k
  · have hKk : K ≤ k := by
      by_contra! h
      have := scale_gap h
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := hN n (by omega)
    obtain ⟨cx, hcx⟩ := union_colour hD hx
    obtain ⟨cy, hcy⟩ := union_colour hD hy
    obtain ⟨c, hc⟩ := special_rep hcx hcy (hxy.trans he)
    have := hK k hKk c
    have := satellite_bounds k c
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨_, ⟨hx, by change _ ≠ a; omega⟩, _, ⟨hy, by change _ ≠ a; omega⟩, hxy⟩
  · exact keep_regular hD hN (by omega) (by omega) slo shi he

/-- **Erdős Problem 869 is false (Larsen).** There are disjoint sets $A_1$ and $A_2$ of natural
numbers, both additive bases of order $2$, such that no subset of $A_1 \cup A_2$ is a minimal
additive basis of order $2$.

Source: Daniel Larsen, Three questions of Erdős–Nathanson
on asymptotic bases of order 2, arXiv:2603.03472 (2026), https://arxiv.org/abs/2603.03472; Lean
proof of the negative answer to Erdős Problem 869, pinned revision
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos869.lean#L3490.
Moved from `OpenConjectures/NumberTheory/ErdosProblem869`.
-/
public theorem Statement_refuted : ¬ Statement := by
  intro h
  obtain ⟨D, hD, hBasis, hMinimal⟩ :=
    h _ _ colours_disjoint (colour_basis 0) (colour_basis 1)
  obtain ⟨N, hN⟩ := hBasis
  obtain ⟨a, ha, _, _, _⟩ := hN N le_rfl
  obtain ⟨M, hM⟩ := erase_basis hD ⟨N, hN⟩ a
  apply hMinimal a ha
  refine (Set.finite_lt_nat M).subset ?_
  intro n hn
  change n < M
  exact lt_of_not_ge (fun hle => hn (hM n hle))

end MathlibExt.NumberTheory.ErdosProblem869Wanted
