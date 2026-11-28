/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max

/-!
# Alder-type inequalities for fixed perimeter partitions

Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher study these counts in
*Analogues of Alder-Type Partition Inequalities for Fixed Perimeter Partitions*,
INTEGERS 24 (2024), Article A102 (arXiv:2406.07655).

A partition is a multiset of positive parts; its perimeter is `α + λ - 1`, with `α` the largest
part and `λ` the number of parts (Section 1 of the paper). The paper's `h_d^(a)`, `f_d^(a)` and
`ℓ_d^(a)` are `perimeterDistinctCount`, `perimeterResidueCount` and `perimeterPMResidueCount`;
their refinements by largest part `α = m` and number of parts `λ = k` carry the suffix `ArmLeg`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Prepending a part to a multiset.** For natural numbers $m$ and $k$, the map that sends a
multiset $t$ of $k$ natural numbers to the multiset obtained from $t$ by adding one copy of $m$
is injective, so it embeds the multisets of size $k$ into all multisets of natural numbers.

With $m$ the largest part, it builds the partitions of a given perimeter from their largest part
and their remaining parts.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1 (a partition is determined by its largest part and its remaining parts). -/
public def symConsEmbedding (m k : ℕ) : Sym ℕ k ↪ Multiset ℕ :=
  ⟨fun t => m ::ₘ (t : Multiset ℕ),
    fun _ _ h => Sym.coe_injective ((Multiset.cons_inj_right m).mp h)⟩

/-- **Partitions with fixed perimeter.** The perimeter of a partition is its largest part plus its
number of parts minus $1$. For a natural number $n$, the partitions with perimeter $n$ form the
finite set of all finite multisets $s$ of positive integers whose largest element plus number of
elements (counted with multiplicity) equals $n + 1$.

The set is enumerated directly: for each number of parts $k = 1, \dots, n$ the largest part is
$n + 1 - k$, and it is prepended to a multiset of $k - 1$ parts from $1, \dots, n + 1 - k$, so the
$2^{n-1}$ partitions with perimeter $n$ (for $n \ge 1$) are listed without filtering or
deduplication.

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

/-- **Membership in the partitions with fixed perimeter.** Let $n$ be a natural number and $s$ a
finite multiset of natural numbers. Then $s$ is a partition with perimeter $n$ if and only if
every element of $s$ is positive and the largest element of $s$ (taken to be $0$ if $s$ is empty)
plus the number of elements of $s$, counted with multiplicity, equals $n + 1$.

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

/-- **The partitions of perimeter three.** There are exactly four partitions with perimeter $3$,
that is, four finite multisets of positive integers whose largest element plus number of elements
(counted with multiplicity) equals $4$.

They are $3$, $2 + 1$, $2 + 2$ and $1 + 1 + 1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1. -/
public theorem card_fixedPerimeterPartitions_three : (fixedPerimeterPartitions 3).card = 4 := by
  decide

/-- **Partitions into d-distinct parts.** Let $d$ be a natural number. A finite multiset $s$ of
natural numbers has $d$-distinct parts when no element occurs in $s$ more than once and any two
elements $x < y$ of $s$ satisfy $x + d \le y$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1 (`d`-distinct parts, as in Alder's `q_d(n)`). -/
public def IsDDistinctParts (d : ℕ) (s : Multiset ℕ) : Prop :=
  s.Nodup ∧ ∀ x ∈ s, ∀ y ∈ s, x < y → x + d ≤ y

/-- `IsDDistinctParts d` is decidable.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1. -/
public instance instDecidablePredMultisetNatIsDDistinctParts (d : ℕ) :
    DecidablePred (IsDDistinctParts d) := fun s => by
  unfold IsDDistinctParts; infer_instance

/-- **Examples of 2-distinct partitions.** The partition $5 + 3$ has $2$-distinct parts, and the
partition $4 + 3$ does not.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1. -/
public theorem isDDistinctParts_examples :
    IsDDistinctParts 2 {5, 3} ∧ ¬ IsDDistinctParts 2 {4, 3} := by
  decide

/-- **Fixed perimeter partitions into $d$-distinct parts.** For natural numbers $d$, $a$ and $n$,
$h_d^{(a)}(n)$ is the number of partitions of perimeter $n$ into $d$-distinct parts that are all
at least $a$. Here the perimeter of a partition is its largest part plus its number of parts
minus $1$, and a partition has $d$-distinct parts when no part repeats and any two parts differ
by at least $d$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Equation (1.1). -/
public def perimeterDistinctCount (d a n : ℕ) : ℕ :=
  ((fixedPerimeterPartitions n).filter fun s => IsDDistinctParts d s ∧ ∀ x ∈ s, a ≤ x).card

/-- **Partitions into d-distinct parts by largest part and length.** For natural numbers $d$, $a$,
$m$ and $k$, $h_d^{(a)}(m, k)$ is the number of nonempty finite multisets of positive integers with
largest element $m$, exactly $k$ elements counted with multiplicity, all elements at least $a$,
and $d$-distinct parts. Such a partition has perimeter $m + k - 1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1.1 (refinement of (1.1)). -/
public def perimeterDistinctArmLegCount (d a m k : ℕ) : ℕ :=
  ((fixedPerimeterPartitions (m + k - 1)).filter fun s =>
    s.sup = m ∧ Multiset.card s = k ∧ IsDDistinctParts d s ∧ ∀ x ∈ s, a ≤ x).card

/-- **Fixed perimeter partitions into parts in one residue class.** For natural numbers $d$, $a$
and $n$, $f_d^{(a)}(n)$ is the number of partitions with perimeter $n$ all of whose parts are
congruent to $a$ modulo $d + 1$. Here a partition is a nonempty multiset of positive integers,
and its perimeter is its largest part plus its number of parts minus one.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Equation (1.2). -/
public def perimeterResidueCount (d a n : ℕ) : ℕ :=
  ((fixedPerimeterPartitions n).filter fun s => ∀ x ∈ s, x ≡ a [MOD d + 1]).card

/-- **Partitions into parts in one residue class, by largest part and length.** For natural
numbers $d$, $a$, $m$ and $k$, $f_d^{(a)}(m, k)$ is the number of nonempty multisets of positive
integers with largest part $m$ and exactly $k$ elements (counted with multiplicity), all of
which are congruent to $a$ modulo $d + 1$.

Such a partition has perimeter (largest part plus number of parts minus one) equal to
$m + k - 1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1.1 (refinement of (1.2)). -/
public def perimeterResidueArmLegCount (d a m k : ℕ) : ℕ :=
  ((fixedPerimeterPartitions (m + k - 1)).filter fun s =>
    s.sup = m ∧ Multiset.card s = k ∧ ∀ x ∈ s, x ≡ a [MOD d + 1]).card

/-- **Fixed perimeter partitions into parts $\equiv \pm a \pmod{d+3}$.** For natural numbers
$d$, $a$ and $n$, $\ell_d^{(a)}(n)$ is the number of partitions of perimeter $n$ into parts
congruent to $a$ or $-a$ modulo $d + 3$, where the perimeter of a partition is its largest part
plus its number of parts minus $1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Equation (1.3). -/
public def perimeterPMResidueCount (d a n : ℕ) : ℕ :=
  ((fixedPerimeterPartitions n).filter fun s => ∀ x : ℕ, x ∈ s →
    (x : ℤ) ≡ a [ZMOD d + 3] ∨ (x : ℤ) ≡ -a [ZMOD d + 3]).card

/-- **Partitions into parts $\equiv \pm a \pmod{d+3}$ by largest part and number of parts.** For
natural numbers $d$, $a$, $\alpha$ and $\lambda$, $\ell_d^{(a)}(\alpha, \lambda)$ is the number of
nonempty partitions into parts congruent to $a$ or $-a$ modulo $d + 3$ with largest part $\alpha$
and exactly $\lambda$ parts (so $\ell_d^{(a)}(0, 0) = 0$: the empty partition is not counted).

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Section 1.1 (refinement of (1.3)). -/
public def perimeterPMResidueArmLegCount (d a m k : ℕ) : ℕ :=
  ((fixedPerimeterPartitions (m + k - 1)).filter fun s =>
    s.sup = m ∧ Multiset.card s = k ∧ ∀ x : ℕ, x ∈ s →
      (x : ℤ) ≡ a [ZMOD d + 3] ∨ (x : ℤ) ≡ -a [ZMOD d + 3]).card

/-- **Small values of the fixed-perimeter partition counts.** Take $d = a = 1$. Among the
partitions with perimeter $3$, exactly two have $1$-distinct parts that are all at least $1$,
exactly two have all parts congruent to $1$ modulo $2$, and exactly two have all parts congruent
to $1$ or $-1$ modulo $4$. Moreover, exactly one partition with largest part $2$ and $2$ parts has
$1$-distinct parts that are all at least $1$, exactly one partition with largest part $3$ and $1$
part has all parts congruent to $1$ modulo $2$, and exactly one partition with largest part $1$
and $3$ parts has all parts congruent to $1$ or $-1$ modulo $4$.

The partitions counted in the last three cases are $2 + 1$, $3$ and $1 + 1 + 1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Equations (1.1)–(1.3). -/
public theorem perimeterCounts_small_values :
    perimeterDistinctCount 1 1 3 = 2 ∧ perimeterResidueCount 1 1 3 = 2 ∧
      perimeterPMResidueCount 1 1 3 = 2 ∧ perimeterDistinctArmLegCount 1 1 2 2 = 1 ∧
      perimeterResidueArmLegCount 1 1 3 1 = 1 ∧ perimeterPMResidueArmLegCount 1 1 1 3 = 1 := by
  decide

set_option linter.unusedVariables false in
/-- **A floor inequality for perimeter counts.** Let $d$, $a$ and $n$ be natural numbers with
$d \ge 1$, $a \ge 1$, $2a < d + 3$ and $a \le n$. Then
$\lfloor \lfloor (n - a)/(d + 1) \rfloor / 2 \rfloor \le \lfloor (n - a)/(d + 3) \rfloor$
and
$\lfloor (\lfloor (n - a)/(d + 1) \rfloor + 1) / 2 \rfloor \le \lfloor (n + a)/(d + 3) \rfloor$.

The lower bounds by $0$ in the source hold automatically and are not stated.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 3. -/
public theorem floor_half_div_le_div_of_two_mul_lt {d a n : ℕ} (hd : 0 < d) (ha : 0 < a)
    (had : 2 * a < d + 3) (hn : a ≤ n) :
    (n - a) / (d + 1) / 2 ≤ (n - a) / (d + 3) ∧
      ((n - a) / (d + 1) + 1) / 2 ≤ (n + a) / (d + 3) := by
  have hden : d + 3 ≤ 2 * (d + 1) := by omega
  constructor
  · rw [Nat.div_div_eq_div_mul, Nat.mul_comm (d + 1)]
    exact Nat.div_le_div_left hden (by omega)
  · let k := (n + a) / (d + 3)
    have hk : n + a < k * (d + 3) + (d + 3) := Nat.lt_div_mul_add (by omega)
    -- The next multiple of d + 3 bounds n + a, so (2k + 1)(d + 1) exceeds n - a.
    have hq : (n - a) / (d + 1) < k * 2 + 1 := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      rw [Nat.add_one_mul (k * 2), Nat.mul_assoc]
      have := Nat.mul_le_mul_left k hden
      omega
    change ((n - a) / (d + 1) + 1) / 2 ≤ k
    omega

end

end MetaMathlibExt
