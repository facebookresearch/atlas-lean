/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.WythoffTerminalPositions
import Mathlib.NumberTheory.Rayleigh

/-!
# Blocking Wythoff Nim with one blocked option

In Larsson's set, every position has at most one Wythoff move back into the set.
Every position outside the set has at least two distinct moves into it.
-/

namespace MetaMathlibExt

namespace blockingWythoff_two_pPositions

open scoped goldenRatio

-- The even pairs have lower endpoint a(n) and difference 2n.
private noncomputable def a (n : ℕ) : ℕ := 2 * ⌊(n : ℝ) * φ⌋₊ + 2

private noncomputable def b (n : ℕ) : ℕ := a n + 2 * n

private theorem floor_sq (n : ℕ) : ⌊(n : ℝ) * φ ^ 2⌋₊ = ⌊(n : ℝ) * φ⌋₊ + n := by
  rw [Real.goldenRatio_sq, mul_add, mul_one, Nat.floor_add_natCast]
  exact mul_nonneg n.cast_nonneg Real.goldenRatio_pos.le

private theorem a_strictMono : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hφ := Real.one_lt_goldenRatio.le
  have h : (n : ℝ) * φ + 1 ≤ (n + 1 : ℕ) * φ := by
    push_cast
    linarith
  have hfloor := Nat.floor_le_floor h
  rw [Nat.floor_add_one (mul_nonneg n.cast_nonneg Real.goldenRatio_pos.le)] at hfloor
  unfold a
  omega

private theorem b_strictMono : StrictMono b := by
  intro m n h
  have := a_strictMono h
  unfold b
  omega

private theorem a_bounds (n : ℕ) : 2 * n + 2 ≤ a n ∧ a n % 2 = 0 := by
  have hf : n ≤ ⌊(n : ℝ) * φ⌋₊ := Nat.le_floor <| by
    simpa using mul_le_mul_of_nonneg_left Real.one_lt_goldenRatio.le n.cast_nonneg
  unfold a
  omega

-- Rayleigh's theorem partitions the positive integers between the two Beatty sequences.
private theorem beatty_partition (k : ℕ) (hk : 0 < k) :
    let hits (r : ℝ) := ∃ n : ℕ, 0 < n ∧ ⌊(n : ℝ) * r⌋₊ = k
    (hits φ ∧ ¬hits (φ ^ 2)) ∨ (hits (φ ^ 2) ∧ ¬hits φ) := by
  have hc : Real.HolderConjugate φ (φ ^ 2) := by
    refine Real.holderConjugate_iff.mpr ⟨Real.one_lt_goldenRatio, ?_⟩
    rw [← inv_pow, Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]
    ring
  have conv (r : ℝ) (hr : 0 ≤ r) :
      (k : ℤ) ∈ {beattySeq r i | i > 0} ↔ ∃ n : ℕ, 0 < n ∧ ⌊(n : ℝ) * r⌋₊ = k := by
    constructor
    · rintro ⟨i, hi, he⟩
      lift i to ℕ using hi.le
      refine ⟨i, by exact_mod_cast hi, ?_⟩
      simpa [beattySeq, Int.floor_toNat] using congrArg Int.toNat he
    · rintro ⟨n, hn, he⟩
      refine ⟨n, by exact_mod_cast hn, ?_⟩
      simpa [beattySeq, Int.natCast_floor_eq_floor (mul_nonneg n.cast_nonneg hr)] using
        congrArg (fun j : ℕ => (j : ℤ)) he
  have h := Real.goldenRatio_irrational.beattySeq_symmDiff_beattySeq_pos hc
  have hmem := h.ge (show (k : ℤ) ∈ {j : ℤ | 0 < j} from show 0 < (k : ℤ) by exact_mod_cast hk)
  simpa only [Set.mem_symmDiff, conv _ Real.goldenRatio_pos.le, conv _ (sq_nonneg φ)] using hmem

private theorem endpoints_coincide {m n : ℕ} (h : a m = b n) : m = 0 ∧ n = 0 := by
  have ha := (a_bounds m).1
  have hb := (a_bounds n).1
  by_cases hm : m = 0
  · subst m
    simp [a, b] at h
    omega
  by_cases hn : n = 0
  · subst n
    rw [show b 0 = 2 by simp [b, a]] at h
    omega
  have hk : 0 < ⌊(m : ℝ) * φ⌋₊ := by unfold a at ha; omega
  have he : ⌊(n : ℝ) * φ ^ 2⌋₊ = ⌊(m : ℝ) * φ⌋₊ := by
    unfold b a at h
    rw [floor_sq]
    omega
  rcases beatty_partition _ hk with ⟨_, hnot⟩ | ⟨_, hnot⟩
  · exact (hnot ⟨n, by omega, he⟩).elim
  · exact (hnot ⟨m, Nat.pos_of_ne_zero hm, rfl⟩).elim

private def Paired (x y : ℕ) : Prop :=
  ∃ n, (x = a n ∧ y = b n) ∨ (x = b n ∧ y = a n)

private theorem paired_symm {x y : ℕ} (h : Paired x y) : Paired y x := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩

private theorem paired_bounds {x y : ℕ} (h : Paired x y) :
    0 < x ∧ x % 2 = 0 ∧ y % 2 = 0 ∧ y ≤ 2 * x ∧ x ≤ 2 * y := by
  obtain ⟨n, h⟩ := h
  have := a_bounds n
  unfold b at h
  omega

private theorem paired_unique {x y z : ℕ} (hy : Paired x y) (hz : Paired x z) : y = z := by
  obtain ⟨m, hm⟩ := hy
  obtain ⟨n, hn⟩ := hz
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hn with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · rw [a_strictMono.injective h]
  · obtain ⟨rfl, rfl⟩ := endpoints_coincide h
    rfl
  · obtain ⟨rfl, rfl⟩ := endpoints_coincide h.symm
    rfl
  · rw [b_strictMono.injective h]

private theorem paired_exists {x : ℕ} (hx : 0 < x) (he : x % 2 = 0) : ∃ y, Paired x y := by
  let k := x / 2 - 1
  have hxk : x = 2 * k + 2 := by dsimp [k]; omega
  by_cases hk : k = 0
  · exact ⟨b 0, 0, Or.inl ⟨by simp [hxk, hk, a], rfl⟩⟩
  rcases beatty_partition k (by omega) with ⟨⟨n, _, hn⟩, _⟩ | ⟨⟨n, _, hn⟩, _⟩
  · exact ⟨b n, n, Or.inl ⟨by rw [a, hn, hxk], rfl⟩⟩
  · rw [floor_sq] at hn
    exact ⟨a n, n, Or.inr ⟨by unfold b a; omega, rfl⟩⟩

-- The origin and the two rays form the rest of Larsson's set.
private def OnRay (x y : ℕ) : Prop := (x = 0 ∧ y = 0) ∨ y = 2 * x + 1 ∨ x = 2 * y + 1

private theorem mem_iff {x y : ℕ} : (x, y) ∈ larssonSetTwo ↔ OnRay x y ∨ Paired x y := by
  simp only [larssonSetTwo, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, Prod.mk.injEq,
    OnRay, Paired, b, a, floor_sq, Nat.mul_add]
  grind

private theorem mem_swap {x y : ℕ} (h : (x, y) ∈ larssonSetTwo) : (y, x) ∈ larssonSetTwo := by
  rcases mem_iff.mp h with h | h
  · exact mem_iff.mpr (Or.inl (by unfold OnRay at *; omega))
  · exact mem_iff.mpr (Or.inr (paired_symm h))

private theorem move_iff {x y u v : ℕ} : wythoffTerminalMove 0 (x, y) (u, v) ↔
    (u = x ∧ v < y) ∨ (v = y ∧ u < x) ∨ (u < x ∧ x + v = u + y) := by
  simp only [wythoffTerminalMove]
  constructor
  · rintro ⟨_, h | h | ⟨k, hk, hu, hv⟩⟩ <;> omega
  · intro h
    refine ⟨by omega, ?_⟩
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨x - u, by omega, by omega, by omega⟩)

private def options (x y : ℕ) : Set (ℕ × ℕ) :=
  {q | wythoffTerminalMove 0 (x, y) q ∧ q ∈ larssonSetTwo}

private theorem options_finite (x y : ℕ) : (options x y).Finite := by
  apply ((Set.finite_Iic x).prod (Set.finite_Iic y)).subset
  rintro ⟨u, v⟩ ⟨hm, _⟩
  have := move_iff.mp hm
  change u ≤ x ∧ v ≤ y
  omega

private theorem options_swap {x y u v : ℕ} (h : (u, v) ∈ options x y) :
    (v, u) ∈ options y x := by
  have hm := move_iff.mp h.1
  exact ⟨move_iff.mpr (by omega), mem_swap h.2⟩

private theorem ncard_swap (x y : ℕ) : (options x y).ncard = (options y x).ncard := by
  apply Set.BijOn.ncard_eq (f := Prod.swap)
  refine ⟨fun ⟨_, _⟩ h => options_swap h, Prod.swap_injective.injOn, ?_⟩
  exact fun ⟨u, v⟩ h => ⟨(v, u), options_swap h, rfl⟩

-- Every column has precisely one member below its point on the upper ray.
private theorem column_below_ray (x : ℕ) :
    ∃! y, (x, y) ∈ larssonSetTwo ∧ y < 2 * x + 1 := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, ⟨larssonSetTwo_examples.1, by decide⟩, fun _ h => by omega⟩
  by_cases he : x % 2 = 0
  · obtain ⟨v, hv⟩ := paired_exists (Nat.pos_of_ne_zero hx) he
    have := paired_bounds hv
    refine ⟨v, ⟨mem_iff.mpr (Or.inr hv), by omega⟩, ?_⟩
    rintro y ⟨hy, hlt⟩
    rcases mem_iff.mp hy with hr | hp
    · unfold OnRay at hr
      omega
    · exact paired_unique hp hv
  · refine ⟨x / 2, ⟨mem_iff.mpr (Or.inl (by unfold OnRay; omega)), by omega⟩, ?_⟩
    rintro y ⟨hy, hlt⟩
    rcases mem_iff.mp hy with hr | hp
    · unfold OnRay at hr
      omega
    · have := paired_bounds hp
      omega

private theorem stable_ray (x : ℕ) : (options x (2 * x + 1)).ncard ≤ 1 := by
  obtain ⟨w, _, hw⟩ := column_below_ray x
  apply (Set.ncard_le_one_iff_subset_singleton (options_finite ..)).mpr
  refine ⟨(x, w), ?_⟩
  rintro ⟨u, v⟩ ⟨hm, hmem⟩
  have hmove := move_iff.mp hm
  have hu : u = x := by
    rcases mem_iff.mp hmem with hr | hp
    · unfold OnRay at hr
      omega
    · have := paired_bounds hp
      omega
  subst u
  exact Prod.ext rfl (hw v ⟨hmem, by omega⟩)

-- A horizontal or vertical move cannot connect two paired positions by uniqueness of the
-- partner. A diagonal move preserves the signed difference, which determines the pair.
private theorem no_move_paired {x y u v : ℕ} (hp : Paired x y) (hq : Paired u v) :
    ¬wythoffTerminalMove 0 (x, y) (u, v) := by
  intro hm
  rcases move_iff.mp hm with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩ | ⟨hlt, hdiag⟩
  · exact hlt.ne (paired_unique hq hp)
  · exact hlt.ne (paired_unique (paired_symm hq) (paired_symm hp))
  · obtain ⟨m, hm⟩ := hp
    obtain ⟨n, hn⟩ := hq
    unfold b at hm hn
    have hmn : m = n := by omega
    subst m
    omega

private theorem stable_paired {x y : ℕ} (hxy : x ≤ y) (hp : Paired x y) :
    (options x y).ncard ≤ 1 := by
  have hb := paired_bounds hp
  have diagonal {u v : ℕ} (h : (u, v) ∈ options x y) :
      OnRay u v ∧ x + v = u + y := by
    obtain ⟨hm, hmem⟩ := h
    rcases mem_iff.mp hmem with hr | hq
    · have := move_iff.mp hm
      refine ⟨hr, ?_⟩
      unfold OnRay at hr
      omega
    · exact (no_move_paired hp hq hm).elim
  apply (Set.ncard_le_one (options_finite ..)).mpr
  rintro ⟨u, v⟩ huv ⟨s, t⟩ hst
  have h₁ := diagonal huv
  have h₂ := diagonal hst
  unfold OnRay at h₁ h₂
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

-- From the region x ≤ y ≤ 2x, the diagonal always hits the origin or the upper ray.
private theorem diagonal_to_ray {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 2 * x) :
    ∃ u v, (u, v) ∈ options x y ∧ OnRay u v ∧ u < x ∧ v < y := by
  by_cases heq : x = y
  · exact ⟨0, 0, ⟨move_iff.mpr (by omega), larssonSetTwo_examples.1⟩,
      Or.inl ⟨rfl, rfl⟩, hx, by omega⟩
  let u := y - x - 1
  have hr : OnRay u (2 * u + 1) := Or.inr (Or.inl rfl)
  refine ⟨u, 2 * u + 1, ⟨move_iff.mpr ?_, mem_iff.mpr (Or.inl hr)⟩, hr, ?_, ?_⟩ <;>
    dsimp [u] <;> omega

-- If the partner in column x lies above y, move diagonally to the pair of gap y - x.
private theorem move_to_paired {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y)
    (hex : x % 2 = 0) (hey : y % 2 = 0) (hout : ¬Paired x y) :
    ∃ u v, wythoffTerminalMove 0 (x, y) (u, v) ∧ Paired u v := by
  obtain ⟨z, hz⟩ := paired_exists hx hex
  by_cases hlt : z < y
  · exact ⟨x, z, move_iff.mpr (Or.inl ⟨rfl, hlt⟩), hz⟩
  have hne : z ≠ y := fun he => hout (he ▸ hz)
  obtain ⟨n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hz
  · let k := (y - a n) / 2
    have hgap : y = a n + 2 * k := by dsimp [k]; omega
    have hkn : k < n := by unfold b at hlt hne; omega
    have := a_strictMono hkn
    refine ⟨a k, b k, move_iff.mpr (Or.inr (Or.inr ⟨this, ?_⟩)), k, Or.inl ⟨rfl, rfl⟩⟩
    unfold b
    omega
  · unfold b at hxy
    omega

private theorem absorbing {x y : ℕ} (hxy : x ≤ y) (hout : (x, y) ∉ larssonSetTwo) :
    2 ≤ (options x y).ncard := by
  apply (Set.one_lt_ncard (options_finite ..)).mpr
  have hr : (x, 2 * x + 1) ∈ larssonSetTwo := mem_iff.mpr (Or.inl (Or.inr (Or.inl rfl)))
  by_cases habove : 2 * x + 1 < y
  · obtain ⟨v, ⟨hv, hlt⟩, _⟩ := column_below_ray x
    exact ⟨(x, v), ⟨move_iff.mpr (by omega), hv⟩,
      (x, 2 * x + 1), ⟨move_iff.mpr (by omega), hr⟩, fun h => hlt.ne (Prod.mk.inj h).2⟩
  have hne : 2 * x + 1 ≠ y := fun he => hout (he ▸ hr)
  have hy : y ≤ 2 * x := by omega
  have hx : 0 < x := by
    by_contra! hz
    exact hout (mem_iff.mpr (Or.inl (Or.inl ⟨by omega, by omega⟩)))
  obtain ⟨u, v, hopt, hray, hu, hv⟩ := diagonal_to_ray hx hxy hy
  refine ⟨(u, v), hopt, ?_⟩
  by_cases hex : x % 2 = 0
  · by_cases hey : y % 2 = 0
    · obtain ⟨s, t, hm, hp⟩ := move_to_paired hx hxy hex hey (fun h => hout (mem_iff.mpr (.inr h)))
      refine ⟨(s, t), ⟨hm, mem_iff.mpr (.inr hp)⟩, ?_⟩
      rintro ⟨⟩
      have := paired_bounds hp
      unfold OnRay at hray
      omega
    · have hmem : OnRay (y / 2) y := Or.inr (Or.inl (by omega))
      exact ⟨(y / 2, y), ⟨move_iff.mpr (by omega), mem_iff.mpr (.inl hmem)⟩,
        fun h => hv.ne (Prod.mk.inj h).2⟩
  · have hmem : OnRay x (x / 2) := Or.inr (Or.inr (by omega))
    exact ⟨(x, x / 2), ⟨move_iff.mpr (by omega), mem_iff.mpr (.inl hmem)⟩,
      fun h => hu.ne (Prod.mk.inj h).1⟩

private theorem classify (x y : ℕ) : (x, y) ∈ larssonSetTwo ↔ (options x y).ncard ≤ 1 := by
  wlog hxy : x ≤ y generalizing x y
  · rw [ncard_swap, ← this y x (by omega)]
    exact ⟨mem_swap, mem_swap⟩
  constructor
  · intro h
    rcases mem_iff.mp h with (⟨rfl, rfl⟩ | rfl | h) | hp
    · apply (Set.ncard_le_one (options_finite ..)).mpr
      rintro ⟨u, v⟩ ⟨hm, _⟩
      exact (not_wythoffTerminalMove_of_terminal (p := (0, 0)) (by decide) _ hm).elim
    · exact stable_ray x
    · omega
    · exact stable_paired hxy hp
  · contrapose!
    exact absorbing hxy

end blockingWythoff_two_pPositions

/-- **Larsson's P-positions of Blocking Wythoff Nim with one blocked option.** Let $\varphi$ be
the golden ratio, and let $R_2$ consist of $(0, 0)$ and, for every $n \ge 0$, the positions
$(n, 2n + 1)$, $(2n + 1, n)$, $(2\lfloor n\varphi \rfloor + 2, 2\lfloor n\varphi^2 \rfloor + 2)$
and $(2\lfloor n\varphi^2 \rfloor + 2, 2\lfloor n\varphi \rfloor + 2)$. A Wythoff move from a
position of two piles removes a positive number of tokens from one pile, or the same positive
number from both. Then every position in $R_2$ has at most one Wythoff move to a position in
$R_2$, and every position outside $R_2$ has at least two Wythoff moves to positions in $R_2$.

Hence $R_2$ is the set of P-positions of $W^2$, Wythoff's game in which the previous player may
forbid one option.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 26 (`jis-2026-26.1.6-thm-26`). -/
public theorem blockingWythoff_two_pPositions :
    (∀ x ∈ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo}.ncard ≤ 1) ∧
      ∀ x ∉ larssonSetTwo, 2 ≤ {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo}.ncard := by
  constructor
  · rintro ⟨x, y⟩ h
    exact (blockingWythoff_two_pPositions.classify x y).mp h
  · rintro ⟨x, y⟩ h
    exact Nat.lt_of_not_ge (fun hc => h ((blockingWythoff_two_pPositions.classify x y).mpr hc))

end MetaMathlibExt
