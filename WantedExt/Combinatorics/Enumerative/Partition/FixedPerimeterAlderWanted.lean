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
public instance (d : ℕ) : DecidablePred (IsDDistinctParts d) := fun s => by
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

/-- **Fixed-perimeter identity for $d$-distinct parts.** Let $d$ and $n$ be positive integers and
let $a$ be an integer with $1 \le a \le d + 1$. Then the number $h_d^{(a)}(n)$ of partitions of
perimeter $n$ into $d$-distinct parts (no part repeats and any two parts differ by at least $d$),
all at least $a$, equals the number $f_d^{(a)}(n)$ of partitions of perimeter $n$ into parts
congruent to $a$ modulo $d + 1$. Here the perimeter of a partition is its largest part plus its
number of parts minus $1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 1. -/
public theorem_wanted perimeterDistinctCount_eq_perimeterResidueCount {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 1 ≤ a) (had : a ≤ d + 1) :
    perimeterDistinctCount d a n = perimeterResidueCount d a n

/-- **Refined equality of distinct-part and residue counts.** Let $d$, $a$, $m$ and $k$ be natural
numbers with $d \ge 1$, $1 \le a \le d + 1$, $m \ge 1$ and $k \ge 1$. Write $h_d^{(a)}(m, k)$ for
the number of partitions into $d$-distinct parts, all at least $a$, with largest part $m$ and $k$
parts, and $f_d^{(a)}(m, k)$ for the number of partitions into parts congruent to $a$ modulo
$d + 1$ with largest part $m$ and $k$ parts. Then
$h_d^{(a)}(m, k) = f_d^{(a)}(a + (d + 1)(k - 1), j)$, where $j = \max(m + 1 - a - d(k - 1), 0)$.

In the source the second argument is $m + 1 - a - d(k - 1)$; it is replaced by $0$ when it is not
positive, and then both sides vanish.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 1. -/
public theorem_wanted perimeterDistinctArmLegCount_eq_perimeterResidueArmLegCount
    {d a m k : ℕ} (hd : 0 < d) (ha : 1 ≤ a) (had : a ≤ d + 1) (hm : 0 < m) (hk : 0 < k) :
    perimeterDistinctArmLegCount d a m k =
      perimeterResidueArmLegCount d a (a + (d + 1) * (k - 1)) (m + 1 - a - d * (k - 1))

/-- **Counting d-distinct partitions by largest part and length.** Let $d$, $a$, $m$ and $k$ be
positive integers with $a \le d + 1$, and write $h_d^{(a)}(m, k)$ for the number of partitions into
$d$-distinct parts, all at least $a$, with largest part $m$ and $k$ parts. Then
$h_d^{(a)}(m, k) \ne 0$ if and only if $m \ge a + d(k - 1)$, and in that case
$h_d^{(a)}(m, k) = \binom{m - a - (d - 1)(k - 1)}{k - 1}$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 1. -/
public theorem_wanted perimeterDistinctArmLegCount_ne_zero_iff_and_eq_choose {d a m k : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m) (hk : 0 < k) (had : a ≤ d + 1) :
    (perimeterDistinctArmLegCount d a m k ≠ 0 ↔ a + d * (k - 1) ≤ m) ∧
      (a + d * (k - 1) ≤ m →
        perimeterDistinctArmLegCount d a m k = (m - a - (d - 1) * (k - 1)).choose (k - 1))

/-- **Nonvanishing and binomial count for parts $\equiv a \pmod{d+1}$.** Let $d$, $a$, $\alpha$
and $\lambda$ be positive integers with $a \le d + 1$, and let $f_d^{(a)}(\alpha, \lambda)$ be the
number of partitions into parts congruent to $a$ modulo $d + 1$ with largest part $\alpha$ and
exactly $\lambda$ parts. Then $f_d^{(a)}(\alpha, \lambda) \ne 0$ if and only if $\alpha \ge a$ and
$\alpha \equiv a \pmod{d + 1}$, and in that case
$f_d^{(a)}(\alpha, \lambda) = \binom{(\alpha - a)/(d + 1) + \lambda - 1}{\lambda - 1}$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 2. -/
public theorem_wanted perimeterResidueArmLegCount_ne_zero_iff_and_eq_choose {d a m k : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m) (hk : 0 < k) (had : a ≤ d + 1) :
    (perimeterResidueArmLegCount d a m k ≠ 0 ↔ a ≤ m ∧ m ≡ a [MOD d + 1]) ∧
      (a ≤ m → m ≡ a [MOD d + 1] →
        perimeterResidueArmLegCount d a m k = ((m - a) / (d + 1) + k - 1).choose (k - 1))

/-- **A floor inequality for perimeter counts.** Let $d$, $a$ and $n$ be natural numbers with
$d \ge 1$, $a \ge 1$, $2a < d + 3$ and $a \le n$. Then
$\lfloor \lfloor (n - a)/(d + 1) \rfloor / 2 \rfloor \le \lfloor (n - a)/(d + 3) \rfloor$
and
$\lfloor (\lfloor (n - a)/(d + 1) \rfloor + 1) / 2 \rfloor \le \lfloor (n + a)/(d + 3) \rfloor$.

The lower bounds by $0$ in the source hold automatically and are not stated.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 3. -/
public theorem_wanted floor_half_div_le_div_of_two_mul_lt {d a n : ℕ} (hd : 0 < d) (ha : 0 < a)
    (had : 2 * a < d + 3) (hn : a ≤ n) :
    (n - a) / (d + 1) / 2 ≤ (n - a) / (d + 3) ∧
      ((n - a) / (d + 1) + 1) / 2 ≤ (n + a) / (d + 3)

/-- **Nonvanishing and binomial count for parts $\equiv \pm a \pmod{d+3}$.** Let $d$, $a$,
$\alpha$ and $\lambda$ be positive integers with $a < (d + 3)/2$, and let
$\ell_d^{(a)}(\alpha, \lambda)$ be the number of partitions into parts congruent to $a$ or $-a$
modulo $d + 3$ with largest part $\alpha$ and exactly $\lambda$ parts. Then
$\ell_d^{(a)}(\alpha, \lambda) \ne 0$ if and only if $\alpha \ge a$ and
$\alpha \equiv \pm a \pmod{d + 3}$. Moreover, if $\alpha \ge a$ and $\alpha \equiv a \pmod{d + 3}$,
then $\ell_d^{(a)}(\alpha, \lambda) = \binom{2(\alpha - a)/(d + 3) + \lambda - 1}{\lambda - 1}$,
and if $\alpha \ge a$ and $\alpha \equiv -a \pmod{d + 3}$, then
$\ell_d^{(a)}(\alpha, \lambda) = \binom{2(\alpha + a)/(d + 3) + \lambda - 2}{\lambda - 1}$.

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

/-- **Reverse Alder-type inequality for fixed perimeter partitions.** Let $d$, $n$ and $a$ be
positive integers with $a < (d + 3)/2$. Then the number $h_d^{(a)}(n)$ of partitions of perimeter
$n$ into $d$-distinct parts (no part repeats and any two parts differ by at least $d$), all at
least $a$, is at most the number $\ell_d^{(a)}(n)$ of partitions of perimeter $n$ into parts
congruent to $a$ or $-a$ modulo $d + 3$. Here the perimeter of a partition is its largest part
plus its number of parts minus $1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 2. -/
public theorem_wanted perimeterDistinctCount_le_perimeterPMResidueCount {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 0 < a) (had : 2 * a < d + 3) :
    perimeterDistinctCount d a n ≤ perimeterPMResidueCount d a n

/-- **Monotonicity of fixed perimeter counts with $d$-distinct parts.** For natural numbers
$d$, $a$ and $n$, let $h_d^{(a)}(n)$ be the number of partitions of perimeter $n$ (largest part
plus number of parts minus $1$) into $d$-distinct parts, all at least $a$, where parts are
$d$-distinct when no part repeats and any two parts differ by at least $d$. If $d$, $n$ and $a$
are positive, then $h_d^{(a+1)}(n) \le h_d^{(a)}(n)$, $h_{d+1}^{(a)}(n) \le h_d^{(a)}(n)$ and
$h_d^{(a)}(n) \le h_d^{(a)}(n + 1)$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 1. -/
public theorem_wanted perimeterDistinctCount_shift_inequalities {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 0 < a) :
    perimeterDistinctCount d (a + 1) n ≤ perimeterDistinctCount d a n ∧
      perimeterDistinctCount (d + 1) a n ≤ perimeterDistinctCount d a n ∧
      perimeterDistinctCount d a n ≤ perimeterDistinctCount d a (n + 1)

/-- **Monotonicity of fixed perimeter counts with parts $\equiv \pm a \pmod{d+3}$.** For natural
numbers $d$, $a$ and $n$, let $\ell_d^{(a)}(n)$ be the number of partitions of perimeter $n$
(largest part plus number of parts minus $1$) into parts congruent to $a$ or $-a$ modulo $d + 3$.
If $d$, $n$ and $a$ are positive with $a < (d + 3)/2$, then
$\ell_d^{(a)}(n) \le \ell_d^{(a)}(n + 1)$ and $\ell_{d+1}^{(a)}(n) \le \ell_d^{(a)}(n)$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 1. -/
public theorem_wanted perimeterPMResidueCount_shift_inequalities {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 0 < a) (had : 2 * a < d + 3) :
    perimeterPMResidueCount d a n ≤ perimeterPMResidueCount d a (n + 1) ∧
      perimeterPMResidueCount (d + 1) a n ≤ perimeterPMResidueCount d a n

/-- **Alder-type inequality in the degenerate case $a = (d + 3)/2$.** Let $n$ be a positive
integer, let $d$ be an odd natural number and put $a = (d + 3)/2$. Then the number
$\ell_d^{(a)}(n)$ of partitions of perimeter $n$ into parts congruent to $a$ or $-a$ modulo
$d + 3$ is at most the number $h_d^{(a)}(n)$ of partitions of perimeter $n$ into $d$-distinct
parts (no part repeats and any two parts differ by at least $d$), all at least $a$. Here the
perimeter of a partition is its largest part plus its number of parts minus $1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 2. -/
public theorem_wanted perimeterPMResidueCount_le_perimeterDistinctCount_of_odd {d n : ℕ}
    (hn : 0 < n) (hd : d % 2 = 1) :
    perimeterPMResidueCount d ((d + 3) / 2) n ≤ perimeterDistinctCount d ((d + 3) / 2) n

end

end MetaMathlibExt
