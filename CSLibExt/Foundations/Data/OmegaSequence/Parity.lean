/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The max-parity condition on priority sequences
-/
module

public import Cslib.Foundations.Data.OmegaSequence.Init
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# The max-parity condition on priority sequences

Parity automata and parity games assign natural-number priorities to states, and an infinite
sequence of priorities is won by the even player iff the largest priority that occurs infinitely
often is even (the *max-parity* convention).

* `Cslib.ωSequence.IsMaxInfOcc ps n`: `n` occurs infinitely often in `ps` and every value occurring
  infinitely often is at most `n`; it is unique (`IsMaxInfOcc.unique`), exists for bounded
  sequences (`exists_isMaxInfOcc`), and then bounds the tail (`IsMaxInfOcc.eventually_le`). For
  unbounded sequences it may exist without a tail bound, or not exist at all.
* `Cslib.ωSequence.ParityEven`, `Cslib.ωSequence.ParityOdd`: the maximal infinitely occurring
  priority exists and is even, respectively odd. They exclude each other
  (`not_parityEven_and_parityOdd`), one of them holds for bounded sequences
  (`parityEven_or_parityOdd`), and both are prefix independent (`parityEven_drop_iff`,
  `parityOdd_drop_iff`).
* `Cslib.ωSequence.parityEven_iff_frequently_two`: with priorities in `{1, 2}`, the even
  condition is the Büchi condition "priority `2` occurs infinitely often".
-/

@[expose] public section

namespace Cslib.ωSequence

open Filter

/-- `n` is the largest value occurring infinitely often in `ps`: it occurs infinitely often, and
every value occurring infinitely often is at most `n`. Larger values may still occur, each finitely
often; for bounded sequences they eventually stop (`IsMaxInfOcc.eventually_le`). -/
def IsMaxInfOcc (ps : ωSequence ℕ) (n : ℕ) : Prop :=
  (∃ᶠ k in atTop, ps k = n) ∧ ∀ m, (∃ᶠ k in atTop, ps k = m) → m ≤ n

/-- The max-parity condition, won by the even player: the largest priority occurring infinitely
often exists and is even. -/
def ParityEven (ps : ωSequence ℕ) : Prop :=
  ∃ n, Even n ∧ IsMaxInfOcc ps n

/-- The max-parity condition, won by the odd player: the largest priority occurring infinitely
often exists and is odd. -/
def ParityOdd (ps : ωSequence ℕ) : Prop :=
  ∃ n, Odd n ∧ IsMaxInfOcc ps n

variable {ps : ωSequence ℕ}

theorem IsMaxInfOcc.le {n m : ℕ} (hn : IsMaxInfOcc ps n) (hm : ∃ᶠ k in atTop, ps k = m) :
    m ≤ n :=
  hn.2 m hm

theorem IsMaxInfOcc.unique {n m : ℕ} (hn : IsMaxInfOcc ps n) (hm : IsMaxInfOcc ps m) :
    n = m :=
  le_antisymm (hm.le hn.1) (hn.le hm.1)

/-- A sequence bounded by `d` has a largest infinitely occurring value, at most `d`. -/
theorem exists_isMaxInfOcc {d : ℕ} (hb : ∀ k, ps k ≤ d) : ∃ n ≤ d, IsMaxInfOcc ps n := by
  classical
  have hex : ∃ n, n ≤ d ∧ ∃ᶠ k in atTop, ps k = n := by
    have hall : ∃ᶠ k in atTop, ps k ∈ Set.Iic d := Frequently.of_forall hb
    obtain ⟨n, hn, hfreq⟩ :=
      (Set.finite_Iic d).frequently_exists (l := atTop) (p := fun n k => ps k = n) |>.mp
        (hall.mono fun k hk => ⟨ps k, hk, rfl⟩)
    exact ⟨n, hn, hfreq⟩
  obtain ⟨m₀, hm₀, hfreq₀⟩ := hex
  refine ⟨Nat.findGreatest (fun n => ∃ᶠ k in atTop, ps k = n) d, Nat.findGreatest_le d,
    Nat.findGreatest_spec (P := fun n => ∃ᶠ k in atTop, ps k = n) hm₀ hfreq₀, fun m hm => ?_⟩
  have hmd : m ≤ d := by
    obtain ⟨k, hk⟩ := hm.exists
    exact hk ▸ hb k
  exact Nat.le_findGreatest hmd hm

/-- For a bounded sequence, eventually every entry is at most its largest infinitely occurring
value. -/
theorem IsMaxInfOcc.eventually_le {n d : ℕ} (hn : IsMaxInfOcc ps n) (hb : ∀ k, ps k ≤ d) :
    ∀ᶠ k in atTop, ps k ≤ n := by
  have hfin : ∀ m ∈ Set.Ioc n d, ∀ᶠ k in atTop, ps k ≠ m := fun m hm =>
    not_frequently.mp fun hfreq => absurd (hn.le hfreq) (by have := hm.1; omega)
  have hall : ∀ᶠ k in atTop, ∀ m ∈ Set.Ioc n d, ps k ≠ m :=
    (Set.finite_Ioc n d).eventually_all.mpr hfin
  refine hall.mono fun k hk => ?_
  by_contra hlt
  exact hk (ps k) ⟨by omega, hb k⟩ rfl

theorem not_parityEven_and_parityOdd : ¬ (ParityEven ps ∧ ParityOdd ps) := by
  rintro ⟨⟨n, hn, hmax⟩, ⟨m, hm, hmax'⟩⟩
  rw [hmax.unique hmax'] at hn
  exact Nat.not_even_iff_odd.mpr hm hn

theorem parityEven_or_parityOdd {d : ℕ} (hb : ∀ k, ps k ≤ d) : ParityEven ps ∨ ParityOdd ps := by
  obtain ⟨n, -, hmax⟩ := exists_isMaxInfOcc hb
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl ⟨n, h, hmax⟩
  · exact Or.inr ⟨n, h, hmax⟩

/-- For bounded sequences, the odd condition is the negation of the even one. -/
theorem parityOdd_iff_not_parityEven {d : ℕ} (hb : ∀ k, ps k ≤ d) :
    ParityOdd ps ↔ ¬ ParityEven ps :=
  ⟨fun h h' => not_parityEven_and_parityOdd ⟨h', h⟩,
    fun h => (parityEven_or_parityOdd hb).resolve_left h⟩

/-- Priorities in `{1, 2}`: the max-parity condition holds iff priority `2` occurs infinitely
often. -/
theorem parityEven_iff_frequently_two {ps : ωSequence ℕ} (h : ∀ k, ps k = 1 ∨ ps k = 2) :
    ParityEven ps ↔ ∃ᶠ k in atTop, ps k = 2 := by
  constructor
  · rintro ⟨n, hn, hfreq, -⟩
    have hn2 : n = 2 := by
      obtain ⟨k, hk⟩ := hfreq.exists
      rcases h k with h1 | h2
      · rw [h1] at hk
        subst hk
        exact absurd hn (by decide)
      · omega
    exact hn2 ▸ hfreq
  · intro hfreq
    refine ⟨2, even_two, hfreq, fun m hm => ?_⟩
    obtain ⟨k, hk⟩ := hm.exists
    rcases h k with h' | h' <;> omega

/-! ## Prefix independence -/

theorem isMaxInfOcc_drop_iff (j n : ℕ) : IsMaxInfOcc (ps.drop j) n ↔ IsMaxInfOcc ps n := by
  have hmap : Filter.map (· + j) atTop = (atTop : Filter ℕ) := map_add_atTop_eq_nat j
  have hf' : ∀ m, (∃ᶠ k in atTop, ps.drop j k = m) ↔ ∃ᶠ k in atTop, ps k = m := fun m => by
    conv_rhs => rw [← hmap, frequently_map]
    simp only [get_drop, Nat.add_comm]
  simp only [IsMaxInfOcc, hf']

theorem parityEven_drop_iff (j : ℕ) : ParityEven (ps.drop j) ↔ ParityEven ps := by
  simp only [ParityEven, isMaxInfOcc_drop_iff]

theorem parityOdd_drop_iff (j : ℕ) : ParityOdd (ps.drop j) ↔ ParityOdd ps := by
  simp only [ParityOdd, isMaxInfOcc_drop_iff]

end Cslib.ωSequence
