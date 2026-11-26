/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.WythoffTerminalPositions
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The mex description of the P-positions of `K^1`

The mex pairs, in both orders, together with the terminal positions form a stable and
absorbing set for Wythoff's game with terminal positions of total at most one.
-/

namespace MetaMathlibExt

namespace wythoffTerminal_one_pPositions

local notation "a" => (wythoffMexA 1)
local notation "b" => (wythoffMexB 1)
local notation "P" => (wythoffTerminalPSet 1)

private theorem b_eq (n : ℕ) : b n = a n + n + 2 := rfl

private theorem a_lt_b (n : ℕ) : a n < b n := by
  rw [b_eq]
  omega

-- A number larger than every earlier `b i` also avoids every earlier `a i`.
private theorem mex_isLeast (n : ℕ) :
    IsLeast {m : ℕ | 1 < m ∧ ∀ i : Fin n, m ≠ a i ∧ m ≠ b i} (a n) := by
  let s : Set ℕ := {m : ℕ | 1 < m ∧ ∀ i : Fin n, m ≠ a i ∧ m ≠ b i}
  let M := (Finset.range n).sup b
  have hs : s.Nonempty := by
    refine ⟨M + 2, by omega, fun i => ?_⟩
    have hbound : b i ≤ M := Finset.le_sup (Finset.mem_range.mpr i.isLt)
    have ha := a_lt_b i
    exact ⟨by omega, by omega⟩
  have heq : a n = sInf s := by
    conv_lhs => rw [wythoffMexA]
    rfl
  change IsLeast s (a n)
  rw [heq]
  exact ⟨Nat.sInf_mem hs, fun _ hm => Nat.sInf_le hm⟩

private theorem one_lt_a (n : ℕ) : 1 < a n := (mex_isLeast n).1.1

private theorem mex_excludes {i n : ℕ} (hi : i < n) : a n ≠ a i ∧ a n ≠ b i :=
  (mex_isLeast n).1.2 ⟨i, hi⟩

private theorem a_strictMono : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  refine lt_of_le_of_ne ((mex_isLeast n).2 ?_) (mex_excludes (Nat.lt_succ_self n)).1.symm
  exact ⟨one_lt_a (n + 1), fun i => mex_excludes (i.isLt.trans (Nat.lt_succ_self n))⟩

private theorem b_strictMono : StrictMono b := by
  intro i j hij
  have ha := a_strictMono hij
  rw [b_eq, b_eq]
  omega

private theorem a_ne_b (i j : ℕ) : a i ≠ b j := by
  rcases lt_or_ge j i with h | h
  · exact (mex_excludes h).2
  · exact ne_of_lt ((a_strictMono.monotone h).trans_lt (a_lt_b j))

-- If `x` were never used, it would bound every mex term from above.
private theorem coordinate_cover {x : ℕ} (hx : 1 < x) : ∃ n, x = a n ∨ x = b n := by
  by_contra h
  have hxmem : x ∈ {m : ℕ | 1 < m ∧ ∀ i : Fin (x + 1), m ≠ a i ∧ m ≠ b i} :=
    ⟨hx, fun i => ⟨fun he => h ⟨i, Or.inl he⟩, fun he => h ⟨i, Or.inr he⟩⟩⟩
  exact (Nat.not_succ_le_self x) ((a_strictMono.id_le (x + 1)).trans
    ((mex_isLeast (x + 1)).2 hxmem))

private theorem mem_swap (x y : ℕ) : (x, y) ∈ P ↔ (y, x) ∈ P := by
  simp [wythoffTerminalPSet, Nat.add_comm, Prod.ext_iff, and_comm, or_comm]

private theorem move_swap (x y u v : ℕ) :
    wythoffTerminalMove 1 (x, y) (u, v) ↔ wythoffTerminalMove 1 (y, x) (v, u) := by
  simp only [wythoffTerminalMove, Nat.add_comm x y, @and_comm (u + _ = x)]
  tauto

-- A one-pile move preserves a coordinate, while a diagonal move preserves the signed difference.
private theorem stable_pair (n : ℕ) {x y : ℕ}
    (h : wythoffTerminalMove 1 (a n, b n) (x, y)) : (x, y) ∉ P := by
  obtain ⟨_, hm⟩ := h
  change (y = b n ∧ x < a n) ∨ (x = a n ∧ y < b n) ∨
    (∃ k, 0 < k ∧ x + k = a n ∧ y + k = b n) at hm
  have ha := one_lt_a n
  have hb := b_eq n
  rintro (ht | ⟨i, hi | hi⟩)
  · change x + y ≤ 1 at ht
    rcases hm with h | h | ⟨k, hk, hx, hy⟩ <;> omega
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hi
    rcases hm with ⟨he, hl⟩ | ⟨he, hl⟩ | ⟨k, hk, hx, hy⟩
    · exact hl.ne (congrArg a (b_strictMono.injective he))
    · exact hl.ne (congrArg b (a_strictMono.injective he))
    · have hbi := b_eq i
      have he : i = n := by omega
      subst i
      omega
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hi
    rcases hm with ⟨he, _⟩ | ⟨he, _⟩ | ⟨k, hk, hx, hy⟩
    · exact a_ne_b i n he
    · exact a_ne_b n i he.symm
    · have hai := a_lt_b i
      omega

private theorem stable (p q : ℕ × ℕ) (hp : p ∈ P) (hm : wythoffTerminalMove 1 p q) :
    q ∉ P := by
  obtain ⟨x, y⟩ := q
  rcases hp with ht | ⟨i, rfl | rfl⟩
  · exact (not_wythoffTerminalMove_of_terminal ht _ hm).elim
  · exact stable_pair i hm
  · exact fun hq => stable_pair i ((move_swap ..).mp hm) ((mem_swap ..).mp hq)

private theorem absorbing_sorted {x y : ℕ} (hxy : x ≤ y) (hp : (x, y) ∉ P) :
    ∃ q, wythoffTerminalMove 1 (x, y) q ∧ q ∈ P := by
  have htotal : 1 < x + y := lt_of_not_ge (fun h => hp (Or.inl h))
  by_cases hs : x ≤ 1
  · exact ⟨(x, 0), ⟨htotal, Or.inr (Or.inl ⟨rfl, by dsimp; omega⟩)⟩,
      Or.inl (by simpa)⟩
  by_cases hd : y ≤ x + 1
  · exact ⟨(0, y - x),
      ⟨htotal, Or.inr (Or.inr ⟨x, by omega, Nat.zero_add x, by dsimp; omega⟩)⟩,
      Or.inl (by dsimp; omega)⟩
  obtain ⟨n, rfl | rfl⟩ := coordinate_cover (show 1 < x by omega)
  · have hne : y ≠ b n := fun he => hp (Or.inr ⟨n, Or.inl (by rw [he])⟩)
    rcases lt_or_gt_of_ne hne with h | h
    · -- The pair with this difference has a smaller index and hence a smaller first pile.
      let i := y - a n - 2
      have hb := b_eq n
      have hin : i < n := by dsimp [i]; omega
      have ha := a_strictMono hin
      refine ⟨(a i, b i), ⟨htotal, Or.inr (Or.inr ?_)⟩, Or.inr ⟨i, Or.inl rfl⟩⟩
      refine ⟨a n - a i, by omega, by dsimp; omega, ?_⟩
      have hbi := b_eq i
      have hi : i = y - a n - 2 := rfl
      dsimp
      omega
    · exact ⟨(a n, b n), ⟨htotal, Or.inr (Or.inl ⟨rfl, h⟩)⟩, Or.inr ⟨n, Or.inl rfl⟩⟩
  · have h := (a_lt_b n).trans_le hxy
    exact ⟨(b n, a n), ⟨htotal, Or.inr (Or.inl ⟨rfl, h⟩)⟩, Or.inr ⟨n, Or.inr rfl⟩⟩

private theorem absorbing (p : ℕ × ℕ) (hp : p ∉ P) :
    ∃ q, wythoffTerminalMove 1 p q ∧ q ∈ P := by
  obtain ⟨x, y⟩ := p
  rcases le_total x y with h | h
  · exact absorbing_sorted h hp
  · obtain ⟨⟨v, u⟩, hm, hq⟩ := absorbing_sorted h (fun hy => hp ((mem_swap ..).mp hy))
    exact ⟨(u, v), (move_swap ..).mp hm, (mem_swap ..).mp hq⟩

end wythoffTerminal_one_pPositions

/-- **P-positions of $K^1$.** Let $a_n$ be the least natural number $m > 1$ with $m \ne a_i$ and
$m \ne b_i$ for all $i < n$, where $b_i = a_i + i + 2$; so $(a_0, b_0) = (2, 4)$. Let $P$ be the
set of positions $(x, y)$ with $x + y \le 1$, together with the pairs $(a_n, b_n)$ and
$(b_n, a_n)$ for $n \ge 0$. Then $P$ is stable, meaning no move of $K^1$ leads from a position
of $P$ to a position of $P$, and absorbing, meaning from every position outside $P$ some move
of $K^1$ leads into $P$.

This is the case $\ell = 1$ of Theorem 17. Since the move relation is well founded, a stable
and absorbing set is the set of P-positions, so $P$ is the set of P-positions of $K^1$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 15 (`jis-2026-26.1.6-prop-15`). -/
public theorem wythoffTerminal_one_pPositions :
    (∀ x y, x ∈ wythoffTerminalPSet 1 → wythoffTerminalMove 1 x y →
        y ∉ wythoffTerminalPSet 1) ∧
      ∀ x, x ∉ wythoffTerminalPSet 1 →
        ∃ y, wythoffTerminalMove 1 x y ∧ y ∈ wythoffTerminalPSet 1 :=
  ⟨wythoffTerminal_one_pPositions.stable, wythoffTerminal_one_pPositions.absorbing⟩

end MetaMathlibExt
