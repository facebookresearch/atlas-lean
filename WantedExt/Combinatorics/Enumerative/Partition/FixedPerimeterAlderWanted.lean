/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max

/-!
# Alder-type inequalities for fixed perimeter partitions

Statements from Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of
Alder-Type Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024),
Article A102 (arXiv:2406.07655).

A partition is a multiset of positive parts; its perimeter is `α + λ - 1`, with `α` the largest
part and `λ` the number of parts (Section 1 of the paper). The paper's `h_d^(a)`, `f_d^(a)` and
`ℓ_d^(a)` are `perimeterDistinctCount`, `perimeterResidueCount` and `perimeterPMResidueCount`;
their refinements by largest part `α = m` and number of parts `λ = k` carry the suffix `ArmLeg`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Prepending a largest part `m` to a multiset of `k` parts, as an embedding
`Sym ℕ k ↪ Multiset ℕ`; it builds `fixedPerimeterPartitions` without deduplication.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1 (a partition is determined by its largest part and its remaining parts). -/
public def symConsEmbedding (m k : ℕ) : Sym ℕ k ↪ Multiset ℕ :=
  ⟨fun t => m ::ₘ (t : Multiset ℕ),
    fun _ _ h => Sym.coe_injective ((Multiset.cons_inj_right m).mp h)⟩

/-- The partitions with perimeter `n`, as multisets `s` of positive parts with
`max s + #s = n + 1`. They are generated directly: for `k = 1, …, n` parts the largest part is
`n + 1 - k`, prepended to a multiset of `k - 1` parts from `1, …, n + 1 - k`, so exactly the
`2 ^ (n - 1)` partitions are enumerated (for `n ≥ 1`), without filtering or deduplication.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1 (perimeter `Γ(π) = α(π) + λ(π) - 1`). -/
public def fixedPerimeterPartitions (n : ℕ) : Finset (Multiset ℕ) :=
  (Finset.Icc 1 n).disjiUnion
    (fun k => ((Finset.Icc 1 (n + 1 - k)).sym (k - 1)).map (symConsEmbedding (n + 1 - k) (k - 1)))
    (by
      intro k hk k' hk' hkk'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro s hs hs'
      simp only [Finset.mem_map] at hs hs'
      obtain ⟨t, -, rfl⟩ := hs
      obtain ⟨t', -, h⟩ := hs'
      change (n + 1 - k') ::ₘ (t' : Multiset ℕ) = (n + 1 - k) ::ₘ (t : Multiset ℕ) at h
      have := congrArg Multiset.card h
      simp only [Multiset.card_cons, Sym.card_coe] at this
      simp only [Finset.mem_coe, Finset.mem_Icc] at hk hk'
      omega)

/-- Membership in `fixedPerimeterPartitions n`: positive parts and perimeter `n`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1. -/
public theorem mem_fixedPerimeterPartitions {n : ℕ} {s : Multiset ℕ} :
    s ∈ fixedPerimeterPartitions n ↔ (∀ x ∈ s, 0 < x) ∧ s.sup + Multiset.card s = n + 1 := by
  rw [fixedPerimeterPartitions, Finset.mem_disjiUnion]
  simp only [Finset.mem_map, Finset.mem_Icc]
  constructor
  · rintro ⟨k, ⟨hk1, hkn⟩, t, ht, rfl⟩
    rw [Finset.mem_sym_iff] at ht
    have ht' : ∀ x ∈ (t : Multiset ℕ), 1 ≤ x ∧ x ≤ n + 1 - k := fun x hx =>
      Finset.mem_Icc.mp (ht x hx)
    have hsup : (t : Multiset ℕ).sup ≤ n + 1 - k :=
      Multiset.sup_le.mpr fun x hx => (ht' x hx).2
    change (∀ x ∈ (n + 1 - k) ::ₘ (t : Multiset ℕ), 0 < x) ∧
      ((n + 1 - k) ::ₘ (t : Multiset ℕ)).sup + Multiset.card ((n + 1 - k) ::ₘ (t : Multiset ℕ)) =
        n + 1
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases Multiset.mem_cons.mp hx with rfl | hx
      · omega
      · exact (ht' x hx).1
    · rw [Multiset.sup_cons, Multiset.card_cons, Sym.card_coe, max_eq_left hsup]
      omega
  · rintro ⟨hpos, hsum⟩
    have hne : s ≠ 0 := by rintro rfl; simp at hsum
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s.toFinset id
      (Multiset.toFinset_nonempty.mpr hne)
    rw [Multiset.mem_toFinset] at hm
    simp only [Multiset.mem_toFinset, id] at hmax
    have hmeq : s.sup = m :=
      le_antisymm (Multiset.sup_le.mpr fun x hx => hmax x hx) (Multiset.le_sup hm)
    have hc : 0 < Multiset.card s := Multiset.card_pos.mpr hne
    have hm1 : 0 < m := hpos m hm
    have hct : Multiset.card (s.erase m) = Multiset.card s - 1 := by
      rw [Multiset.card_erase_of_mem hm]; rfl
    refine ⟨Multiset.card s, ⟨hc, by omega⟩, Sym.mk (s.erase m) hct, ?_, ?_⟩
    · rw [Finset.mem_sym_iff]
      intro x hx
      have hx' : x ∈ s := Multiset.mem_of_mem_erase hx
      exact Finset.mem_Icc.mpr ⟨hpos x hx', by have := hmax x hx'; omega⟩
    · have : n + 1 - Multiset.card s = m := by omega
      change (n + 1 - Multiset.card s) ::ₘ s.erase m = s
      rw [this]
      exact Multiset.cons_erase hm

/-- There are four partitions with perimeter `3`: `3`, `2 + 1`, `2 + 2`, `1 + 1 + 1`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1. -/
public theorem card_fixedPerimeterPartitions_three : (fixedPerimeterPartitions 3).card = 4 := by
  decide

/-- A multiset of parts is `d`-distinct when any two parts differ by at least `d`: no part
repeats, and `x < y` forces `x + d ≤ y`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1 (`d`-distinct parts, as in Alder's `q_d(n)`). -/
public def IsDDistinctParts (d : ℕ) (s : Multiset ℕ) : Prop :=
  s.Nodup ∧ ∀ x ∈ s, ∀ y ∈ s, x < y → x + d ≤ y

/-- `IsDDistinctParts d` is decidable.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1. -/
public instance (d : ℕ) : DecidablePred (IsDDistinctParts d) := fun s => by
  unfold IsDDistinctParts; infer_instance

/-- `5 + 3` is `2`-distinct and `4 + 3` is not.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1. -/
public theorem isDDistinctParts_examples :
    IsDDistinctParts 2 {5, 3} ∧ ¬ IsDDistinctParts 2 {4, 3} := by
  decide

/-- `h_d^(a)(n)`: the number of partitions with perimeter `n` into `d`-distinct parts `≥ a`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Equation (1.1). -/
public def perimeterDistinctCount (d a n : ℕ) : ℕ :=
  ((fixedPerimeterPartitions n).filter fun s => IsDDistinctParts d s ∧ ∀ x ∈ s, a ≤ x).card

/-- `h_d^(a)(α, λ)`: the number of partitions into `d`-distinct parts `≥ a` with largest part
`m = α` and `k = λ` parts (perimeter `m + k - 1`).

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1.1 (refinement of (1.1)). -/
public def perimeterDistinctArmLegCount (d a m k : ℕ) : ℕ :=
  ((fixedPerimeterPartitions (m + k - 1)).filter fun s =>
    s.sup = m ∧ Multiset.card s = k ∧ IsDDistinctParts d s ∧ ∀ x ∈ s, a ≤ x).card

/-- `f_d^(a)(n)`: the number of partitions with perimeter `n` into parts `≡ a (mod d + 1)`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Equation (1.2). -/
public def perimeterResidueCount (d a n : ℕ) : ℕ :=
  ((fixedPerimeterPartitions n).filter fun s => ∀ x ∈ s, x ≡ a [MOD d + 1]).card

/-- `f_d^(a)(α, λ)`: the number of partitions into parts `≡ a (mod d + 1)` with largest part
`m = α` and `k = λ` parts.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1.1 (refinement of (1.2)). -/
public def perimeterResidueArmLegCount (d a m k : ℕ) : ℕ :=
  ((fixedPerimeterPartitions (m + k - 1)).filter fun s =>
    s.sup = m ∧ Multiset.card s = k ∧ ∀ x ∈ s, x ≡ a [MOD d + 1]).card

/-- `ℓ_d^(a)(n)`: the number of partitions with perimeter `n` into parts `≡ ±a (mod d + 3)`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Equation (1.3). -/
public def perimeterPMResidueCount (d a n : ℕ) : ℕ :=
  ((fixedPerimeterPartitions n).filter fun s => ∀ x : ℕ, x ∈ s →
    (x : ℤ) ≡ a [ZMOD d + 3] ∨ (x : ℤ) ≡ -a [ZMOD d + 3]).card

/-- `ℓ_d^(a)(α, λ)`: the number of partitions into parts `≡ ±a (mod d + 3)` with largest part
`m = α` and `k = λ` parts.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1.1 (refinement of (1.3)). -/
public def perimeterPMResidueArmLegCount (d a m k : ℕ) : ℕ :=
  ((fixedPerimeterPartitions (m + k - 1)).filter fun s =>
    s.sup = m ∧ Multiset.card s = k ∧ ∀ x : ℕ, x ∈ s →
      (x : ℤ) ≡ a [ZMOD d + 3] ∨ (x : ℤ) ≡ -a [ZMOD d + 3]).card

/-- Small values at `d = a = 1`, perimeter `3`: `h = f = ℓ = 2`; `h_1^(1)(2, 2) = 1`
(`2 + 1`), `f_1^(1)(3, 1) = 1` (`3`), `ℓ_1^(1)(1, 3) = 1` (`1 + 1 + 1`).

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Equations (1.1)–(1.3). -/
public theorem perimeterCounts_small_values :
    perimeterDistinctCount 1 1 3 = 2 ∧ perimeterResidueCount 1 1 3 = 2 ∧
      perimeterPMResidueCount 1 1 3 = 2 ∧ perimeterDistinctArmLegCount 1 1 2 2 = 1 ∧
      perimeterResidueArmLegCount 1 1 3 1 = 1 ∧ perimeterPMResidueArmLegCount 1 1 1 3 = 1 := by
  decide

/-- Theorem 1.4, first part: for `1 ≤ a ≤ d + 1`, `h_d^(a)(n) = f_d^(a)(n)`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 1. -/
public theorem_wanted perimeterDistinctCount_eq_perimeterResidueCount {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 1 ≤ a) (had : a ≤ d + 1) :
    perimeterDistinctCount d a n = perimeterResidueCount d a n

/-- Theorem 1.4, refinement: for `1 ≤ a ≤ d + 1`,
`h_d^(a)(α, λ) = f_d^(a)(a + (d + 1)(λ - 1), α - a - d(λ - 1) + 1)`. The second argument is
written `α + 1 - a - d(λ - 1)` in truncated subtraction, so it is `0` (and both sides vanish)
when the paper's value is not positive.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 1. -/
public theorem_wanted perimeterDistinctArmLegCount_eq_perimeterResidueArmLegCount
    {d a m k : ℕ} (hd : 0 < d) (ha : 1 ≤ a) (had : a ≤ d + 1) (hm : 0 < m) (hk : 0 < k) :
    perimeterDistinctArmLegCount d a m k =
      perimeterResidueArmLegCount d a (a + (d + 1) * (k - 1)) (m + 1 - a - d * (k - 1))

/-- Lemma 3.1: for positive `d, a, α, λ` with `a ≤ d + 1`, `h_d^(a)(α, λ) ≠ 0` iff
`α ≥ a + d(λ - 1)`, and then `h_d^(a)(α, λ) = C(α - a - (d - 1)(λ - 1), λ - 1)`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 1. -/
public theorem_wanted perimeterDistinctArmLegCount_ne_zero_iff_and_eq_choose {d a m k : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m) (hk : 0 < k) (had : a ≤ d + 1) :
    (perimeterDistinctArmLegCount d a m k ≠ 0 ↔ a + d * (k - 1) ≤ m) ∧
      (a + d * (k - 1) ≤ m →
        perimeterDistinctArmLegCount d a m k = (m - a - (d - 1) * (k - 1)).choose (k - 1))

/-- Lemma 3.2: for positive `d, a, α, λ` with `a ≤ d + 1`, `f_d^(a)(α, λ) ≠ 0` iff `α ≥ a` and
`α ≡ a (mod d + 1)`, and then `f_d^(a)(α, λ) = C((α - a)/(d + 1) + λ - 1, λ - 1)`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 2. -/
public theorem_wanted perimeterResidueArmLegCount_ne_zero_iff_and_eq_choose {d a m k : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m) (hk : 0 < k) (had : a ≤ d + 1) :
    (perimeterResidueArmLegCount d a m k ≠ 0 ↔ a ≤ m ∧ m ≡ a [MOD d + 1]) ∧
      (a ≤ m → m ≡ a [MOD d + 1] →
        perimeterResidueArmLegCount d a m k = ((m - a) / (d + 1) + k - 1).choose (k - 1))

/-- Lemma 4.2: for positive `d, a, n` with `a < (d + 3)/2` and `n ≥ a`,
`⌊⌊(n - a)/(d + 1)⌋ / 2⌋ ≤ ⌊(n - a)/(d + 3)⌋` and
`⌊(⌊(n - a)/(d + 1)⌋ + 1) / 2⌋ ≤ ⌊(n + a)/(d + 3)⌋`, in natural-number division (the lower
bounds `0 ≤ …` are automatic).

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 3. -/
public theorem_wanted floor_half_div_le_div_of_two_mul_lt {d a n : ℕ} (hd : 0 < d) (ha : 0 < a)
    (had : 2 * a < d + 3) (hn : a ≤ n) :
    (n - a) / (d + 1) / 2 ≤ (n - a) / (d + 3) ∧
      ((n - a) / (d + 1) + 1) / 2 ≤ (n + a) / (d + 3)

/-- Lemma 4.3: for positive `d, a, α, λ` with `a < (d + 3)/2`, `ℓ_d^(a)(α, λ) ≠ 0` iff `α ≥ a`
and `α ≡ ±a (mod d + 3)`; then `ℓ_d^(a)(α, λ) = C(2(α - a)/(d + 3) + λ - 1, λ - 1)` if
`α ≡ a`, and `C(2(α + a)/(d + 3) + λ - 2, λ - 1)` if `α ≡ -a`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 4. -/
public theorem_wanted perimeterPMResidueArmLegCount_ne_zero_iff_and_eq_choose {d a m k : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m) (hk : 0 < k) (had : 2 * a < d + 3) :
    (perimeterPMResidueArmLegCount d a m k ≠ 0 ↔
        a ≤ m ∧ ((m : ℤ) ≡ a [ZMOD d + 3] ∨ (m : ℤ) ≡ -a [ZMOD d + 3])) ∧
      (a ≤ m → (m : ℤ) ≡ a [ZMOD d + 3] →
        perimeterPMResidueArmLegCount d a m k =
          (2 * ((m - a) / (d + 3)) + k - 1).choose (k - 1)) ∧
      (a ≤ m → (m : ℤ) ≡ -a [ZMOD d + 3] →
        perimeterPMResidueArmLegCount d a m k =
          (2 * ((m + a) / (d + 3)) + k - 2).choose (k - 1))

/-- Theorem 1.5 (reverse Alder-type inequality): for positive `d, n, a` with `a < (d + 3)/2`,
`h_d^(a)(n) ≤ ℓ_d^(a)(n)`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 2. -/
public theorem_wanted perimeterDistinctCount_le_perimeterPMResidueCount {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 0 < a) (had : 2 * a < d + 3) :
    perimeterDistinctCount d a n ≤ perimeterPMResidueCount d a n

/-- Proposition 1.6, `h` part: for positive `d, n, a`, `h_d^(a+1)(n) ≤ h_d^(a)(n)`,
`h_{d+1}^(a)(n) ≤ h_d^(a)(n)` and `h_d^(a)(n) ≤ h_d^(a)(n + 1)`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 1. -/
public theorem_wanted perimeterDistinctCount_shift_inequalities {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 0 < a) :
    perimeterDistinctCount d (a + 1) n ≤ perimeterDistinctCount d a n ∧
      perimeterDistinctCount (d + 1) a n ≤ perimeterDistinctCount d a n ∧
      perimeterDistinctCount d a n ≤ perimeterDistinctCount d a (n + 1)

/-- Proposition 1.6, `ℓ` part: for positive `d, n, a` with `a < (d + 3)/2`,
`ℓ_d^(a)(n) ≤ ℓ_d^(a)(n + 1)` and `ℓ_{d+1}^(a)(n) ≤ ℓ_d^(a)(n)`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 1. -/
public theorem_wanted perimeterPMResidueCount_shift_inequalities {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 0 < a) (had : 2 * a < d + 3) :
    perimeterPMResidueCount d a n ≤ perimeterPMResidueCount d a (n + 1) ∧
      perimeterPMResidueCount (d + 1) a n ≤ perimeterPMResidueCount d a n

/-- Proposition 4.1 (degenerate case): for positive `n` and odd `d`,
`h_d^((d+3)/2)(n) ≥ ℓ_d^((d+3)/2)(n)`.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 2. -/
public theorem_wanted perimeterPMResidueCount_le_perimeterDistinctCount_of_odd {d n : ℕ}
    (hn : 0 < n) (hd : d % 2 = 1) :
    perimeterPMResidueCount d ((d + 3) / 2) n ≤ perimeterDistinctCount d ((d + 3) / 2) n

end

end MetaMathlibExt
