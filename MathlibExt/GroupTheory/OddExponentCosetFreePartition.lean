/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Exponent
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Sqrt
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.WLOG

/-!
# Coset-free partitions of abelian groups of odd exponent (Kourovka Notebook Problem 13.46)

Kourovka Notebook, Archive of Solved Problems, Problem 13.46 (I. V. Protasov): can every uncountable
abelian group of finite odd exponent be partitioned into two subsets neither of which contains a
coset of an infinite subgroup?

We construct a two-coloring for which every such coset meets both cells. In each prime-torsion
subgroup we read the sign of a basis coefficient at the square-root rank of the support.
We extend these colorings across cosets and combine them modulo two.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.46 (I. V.
Protasov). UnsolvedMath record UM-00700964 (`KOU-13.46`), dataset ulamai/UnsolvedMath v1.8.0.

Finite odd exponent is `Monoid.exponent G ≠ 0` and odd. "Contains cosets of infinite subgroups" is
read as containing some coset `g H` of some infinite subgroup `H`, so the partition must avoid every
such coset in both cells.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.OddExponentCosetFreePartitionKourovka13Problem46Wanted

open scoped Pointwise

/-- **Kourovka Problem 13.46: coset-free partitions.** The proposition that every uncountable
abelian group $G$ of finite odd exponent can be written as $G = A_1 \cup A_2$ with $A_1$ and $A_2$
disjoint, so that for every infinite subgroup $H$ of $G$ and every $g \in G$, the coset $gH$ is
contained neither in $A_1$ nor in $A_2$. The problem is due to I. V. Protasov. -/
def oddExponentCosetFreePartition : Prop :=
  ∀ (G : Type) [CommGroup G], Uncountable G → Monoid.exponent G ≠ 0 →
    Odd (Monoid.exponent G) →
    ∃ A₁ A₂ : Set G, A₁ ∪ A₂ = Set.univ ∧ Disjoint A₁ A₂ ∧
      ∀ H : Subgroup G, (H : Set G).Infinite → ∀ g : G,
        ¬ g • (H : Set G) ⊆ A₁ ∧ ¬ g • (H : Set G) ⊆ A₂

/-- A coordinate's rank is its zero-based position in the sorted support. -/
private def rankBelow {ι : Type*} [LinearOrder ι] (s : Finset ι) (a : ι) : ℕ :=
  (s.filter (· < a)).card

private lemma exists_rank {ι : Type*} [LinearOrder ι] (s : Finset ι) (k : ℕ) (hk : k < s.card) :
    ∃ a ∈ s, rankBelow s a = k := by
  classical
  induction s using Finset.induction_on_max generalizing k with
  | empty => simp at hk
  | insert a s ha ih =>
    have hn : a ∉ s := fun h ↦ (ha _ h).false
    rw [Finset.card_insert_of_notMem hn] at hk
    by_cases h : k < s.card
    · obtain ⟨b, hb, he⟩ := ih k h
      exact ⟨b, Finset.mem_insert_of_mem hb,
        by simpa [rankBelow, Finset.filter_insert, (ha b hb).not_gt] using he⟩
    · have he : k = s.card := by omega
      exact ⟨a, Finset.mem_insert_self ..,
        by simp [rankBelow, Finset.filter_insert, Finset.filter_true_of_mem ha, he]⟩

/-- When a fixed number of old coordinates are inserted into a sufficiently large support,
the square-root rank changes by at most one. -/
private lemma sqrt_shift {n b : ℕ} (hb : b ≤ n.sqrt) :
    (n + b).sqrt ≤ n.sqrt + 1 := by
  have hn := Nat.lt_succ_sqrt n
  apply Nat.lt_succ_iff.mp
  apply Nat.sqrt_lt.mpr
  nlinarith

/-- No fixed finite set can supply the square-root rank in every finite union of disjoint
blocks. Here `size` counts a block and `before` counts its elements below an old coordinate.
After thinning the blocks each such count is either always positive or always zero. -/
private lemma escapes_old_ranks {ι : Type*} (a : Finset ι) (size : ℕ → ℕ)
    (before : ℕ → ι → ℕ) (old : ι → ℕ) (hs : ∀ i, 0 < size i)
    (ho : ∀ x, old x ≤ a.card)
    (hpattern : ∀ x ∈ a, (∀ i, before i x = 0) ∨ ∀ i, 0 < before i x) :
    ∃ s : Finset ℕ, 1 < a.card + ∑ i ∈ s, size i ∧
      ∀ x ∈ a, (a.card + ∑ i ∈ s, size i).sqrt ≠ old x + ∑ i ∈ s, before i x := by
  classical
  -- A large common tail fixes the square-root rank to within one, regardless of the prefix.
  let m := 2 * a.card
  let bound := ∑ i ∈ Finset.range m, size i
  let k := bound + a.card + 2
  let tail := Finset.Ico m (m + k * k)
  let base := a.card + ∑ i ∈ tail, size i
  have hlarge : k ≤ base.sqrt := by
    apply Nat.le_sqrt.mpr
    have h := Finset.sum_le_sum (s := tail) (f := fun _ ↦ 1) (g := size) (fun i _ ↦ hs i)
    simp [tail] at h
    dsimp [base, tail]
    omega
  let pref (j : ℕ) := Finset.range (2 * j)
  have hdis (j) (hj : j ≤ a.card) : Disjoint tail (pref j) := by
    apply Finset.disjoint_left.mpr
    simp only [tail, pref, Finset.mem_Ico, Finset.mem_range]
    unfold m
    omega
  have hbound (j) (hj : j ≤ a.card) : ∑ i ∈ pref j, size i ≤ bound := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by dsimp [m]; omega))
    simp
  by_contra! he
  have choose_old (j : Fin (a.card + 1)) : ∃ x : a,
      (base + ∑ i ∈ pref j, size i).sqrt =
        old x + (∑ i ∈ tail, before i x) + ∑ i ∈ pref j, before i x := by
    have hj : j.val ≤ a.card := by omega
    have hbig : 1 < base + ∑ i ∈ pref j, size i := by
      have := Nat.sqrt_le_self base
      dsimp [k] at hlarge
      omega
    have he' := he (tail ∪ pref j)
    simp only [Finset.sum_union (hdis j hj), ← Nat.add_assoc] at he'
    obtain ⟨x, hx, h⟩ := he' hbig
    exact ⟨⟨x, hx⟩, h⟩
  -- Two even-length prefixes would have to select the same old coordinate. Below it,
  -- either no block contributes, or the longer prefix contributes at least two more elements.
  choose f hf using choose_old
  obtain ⟨j, l, hne, hfl⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  wlog hjl : j < l generalizing j l
  · exact this l j (Ne.symm hne) hfl.symm (lt_of_le_of_ne (le_of_not_gt hjl) hne.symm)
  have eqj := hf j
  have eql := hf l
  rw [← hfl] at eql
  have hlow := Nat.sqrt_le_sqrt (Nat.le_add_right base (∑ i ∈ pref j, size i))
  have hupp := sqrt_shift (n := base) (b := ∑ i ∈ pref l, size i)
    ((hbound l (by omega)).trans (by dsimp [k] at hlarge; omega))
  rcases hpattern _ (f j).property with hz | hp
  · simp [hz] at eqj
    have := ho (f j)
    dsimp [k] at hlarge
    omega
  · have hgrowth (t : ℕ) :
        (∑ i ∈ pref t, before i (f j)) + 2 ≤ ∑ i ∈ pref (t + 1), before i (f j) := by
      simp only [pref, Nat.mul_add, Nat.mul_one, Finset.sum_range_succ]
      have := hp (2 * t)
      have := hp (2 * t + 1)
      omega
    have hm : Monotone (fun t ↦ ∑ i ∈ pref t, before i (f j)) :=
      monotone_nat_of_le_succ fun t ↦ by have := hgrowth t; omega
    have hgap := (hgrowth j).trans (hm (show j.val + 1 ≤ l.val from hjl))
    dsimp only at hgap
    omega

private noncomputable def selected {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (h : s.card.sqrt < s.card) : ι := (exists_rank s _ h).choose

private noncomputable def vectorColor {ι F : Type*} [LinearOrder ι] [AddCommGroup F]
    (sign : F → ZMod 2) (x : ι →₀ F) : ZMod 2 :=
  if h : x.support.card.sqrt < x.support.card then sign (x (selected x.support h)) else 0

private lemma support_blocks {ι F : Type*} [DecidableEq ι] [AddCommGroup F]
    (b : ℕ → ι →₀ F) (hd : Pairwise fun i j ↦ Disjoint (b i).support (b j).support)
    (s : Finset ℕ) : (∑ i ∈ s, b i).support = s.biUnion fun i ↦ (b i).support := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.biUnion_insert, Finsupp.support_add_eq, ih]
    rw [ih, Finset.disjoint_biUnion_right]
    exact fun j hj ↦ hd (by rintro rfl; contradiction)

/-- An infinite subgroup supplies nonzero disjoint blocks outside every prescribed finite set
of coordinates. Restriction to that set takes only finitely many values. -/
private lemma fresh_block {ι G F : Type*} [AddCommGroup G] [AddCommGroup F] [Finite F]
    (e : G →+ ι →₀ F) (he : Function.Injective e) (H : AddSubgroup G) [Infinite H]
    (s : Finset ι) : ∃ v : H, (e v).support.Nonempty ∧ Disjoint s (e v).support := by
  classical
  obtain ⟨x, y, hne, hxy⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun x : H ↦ fun i : s ↦ e x i)
  refine ⟨x - y, ?_, ?_⟩
  · apply Finset.nonempty_iff_ne_empty.mpr
    simpa [sub_eq_zero, he.eq_iff] using hne
  · apply Finset.disjoint_left.mpr
    intro i hi
    simpa [sub_eq_zero] using congrFun hxy ⟨i, hi⟩

/-- A coloring read at the square-root rank splits every coset in a vector space over a
finite field of odd characteristic. Only finite coordinates and opposite signs are used. -/
private lemma vector_splits {ι G F : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup F]
    [Finite F] (sign : F → ZMod 2) (hsign : ∀ x ≠ 0, sign x ≠ sign (-x))
    (e : G →+ ι →₀ F) (he : Function.Injective e) (H : AddSubgroup G) [Infinite H] (g : G) :
    ∃ h : H, vectorColor sign (e (g + h)) ≠ vectorColor sign (e (g - h)) := by
  classical
  let a := (e g).support
  let supp (h : H) := (e h).support
  obtain ⟨v, hv, hd⟩ := exists_seq_of_forall_finset_exists
    (fun h : H ↦ (supp h).Nonempty ∧ Disjoint a (supp h))
    (fun x y : H ↦ Disjoint (supp x) (supp y)) (by
      intro t _
      obtain ⟨h, hne, hdis⟩ := fresh_block e he H (a ∪ t.biUnion supp)
      rw [Finset.disjoint_union_left, Finset.disjoint_biUnion_left] at hdis
      exact ⟨h, ⟨hne, hdis.1⟩, hdis.2⟩)
  -- Thin by which old coordinates have some block element below them.
  let pat (i : ℕ) (x : a) := decide (0 < rankBelow (supp (v i)) x.val)
  obtain ⟨pattern, hinf⟩ := Finite.exists_infinite_fiber pat
  let seq := Infinite.natEmbedding (pat ⁻¹' {pattern})
  let w (i : ℕ) := v (seq i).val
  let b (i : ℕ) := supp (w i)
  have hpat (i : ℕ) (x : a) : decide (0 < rankBelow (b i) x.val) = pattern x :=
    congrFun (seq i).property x
  have hpatt (x) (hx : x ∈ a) :
      (∀ i, rankBelow (b i) x = 0) ∨ ∀ i, 0 < rankBelow (b i) x := by
    cases hb : pattern ⟨x, hx⟩
    · exact Or.inl fun i ↦ by simpa [hb] using hpat i ⟨x, hx⟩
    · exact Or.inr fun i ↦ by simpa [hb] using hpat i ⟨x, hx⟩
  have hpair : Pairwise fun i j ↦ Disjoint (b i) (b j) := by
    intro i j hij
    have hn : (seq i).val ≠ (seq j).val := fun h ↦ hij (seq.injective (Subtype.ext h))
    rcases lt_or_gt_of_ne hn with h | h
    · exact hd _ _ h
    · exact (hd _ _ h).symm
  obtain ⟨s, hcard, hescape⟩ := escapes_old_ranks a (fun i ↦ (b i).card)
    (fun i ↦ rankBelow (b i)) (rankBelow a) (fun i ↦ (hv _).1.card_pos)
    (fun _ ↦ Finset.card_filter_le ..) hpatt
  let h := ∑ i ∈ s, w i
  have hh : (e (h : G)).support = s.biUnion b := by
    simpa [h, b, supp] using support_blocks (fun i ↦ e (w i : G)) hpair s
  have hdg : Disjoint a (e (h : G)).support := by
    rw [hh, Finset.disjoint_biUnion_right]
    exact fun _ _ ↦ (hv _).2
  let t := a ∪ (e (h : G)).support
  have hplus : (e (g + h)).support = t := by rw [map_add, Finsupp.support_add_eq hdg]
  have hminus : (e (g - h)).support = t := by
    rw [sub_eq_add_neg, map_add, map_neg, Finsupp.support_add_eq, Finsupp.support_neg]
    rwa [Finsupp.support_neg]
  have htc : t.card = a.card + ∑ i ∈ s, (b i).card := by
    rw [Finset.card_union_of_disjoint hdg, hh, Finset.card_biUnion (fun _ _ _ _ hij ↦ hpair hij)]
  have hok : t.card.sqrt < t.card := Nat.sqrt_lt_self (htc ▸ hcard)
  let x := selected t hok
  obtain ⟨hxt, hrank⟩ : x ∈ t ∧ rankBelow t x = t.card.sqrt := (exists_rank t _ hok).choose_spec
  have hxa : x ∉ a := by
    intro hx
    apply hescape x hx
    rw [← htc, ← hrank]
    unfold rankBelow t
    rw [Finset.filter_union, Finset.card_union_of_disjoint (hdg.mono
      (Finset.filter_subset ..) (Finset.filter_subset ..)), hh, Finset.filter_biUnion,
      Finset.card_biUnion]
    exact fun _ _ _ _ hij ↦ (hpair hij).mono (Finset.filter_subset ..) (Finset.filter_subset ..)
  have hxg : e g x = 0 := Finsupp.notMem_support_iff.mp hxa
  have hxh : e (h : G) x ≠ 0 :=
    Finsupp.mem_support_iff.mp ((Finset.mem_union.mp hxt).resolve_left hxa)
  refine ⟨h, ?_⟩
  unfold vectorColor
  simp only [hplus, hminus, dite_eq_left hok]
  change sign (e (g + h) x) ≠ sign (e (g - h) x)
  simpa [hxg] using hsign _ hxh

/-- Coordinates on a coset, relative to a fixed representative. -/
private noncomputable def offset {G : Type*} [AddCommGroup G] (T : AddSubgroup G) (x : G) : T :=
  ⟨x - (x : G ⧸ T).out, QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.out_eq _).symm⟩

private lemma offset_add {G : Type*} [AddCommGroup G] (T : AddSubgroup G) (x : G) (t : T) :
    offset T (x + t) = offset T x + t := by
  have h : ((x + t : G) : G ⧸ T) = (x : G ⧸ T) := by
    rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr t.property, add_zero]
  apply Subtype.ext
  change x + t - _ = x - _ + t
  simp only [h]
  abel

/-- Use the same vector-space coloring on each coset of the subgroup killed by `p`. -/
private lemma prime_coloring (G : Type) [AddCommGroup G] (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ c : G → ZMod 2, ∀ (B : Type) [AddCommGroup B] [Infinite B] (f : B →+ G),
      Function.Injective f → (∀ y, p • f y = 0) → ∀ g, ∃ y, c (g + f y) ≠ c (g - f y) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let T := AddSubgroup.torsionBy G (p : ℤ)
  let : Module (ZMod p) T := AddSubgroup.torsionBy.zmodModule
  let basis := Module.Free.chooseBasis (ZMod p) T
  let := linearOrderOfSTO (WellOrderingRel (α := Module.Free.ChooseBasisIndex (ZMod p) T))
  let sign (z : ZMod p) : ZMod 2 := if z.val < (-z).val then 1 else 0
  have hsign (z : ZMod p) (hz : z ≠ 0) : sign z ≠ sign (-z) := by
    have htwo : (2 : ZMod p) ≠ 0 := by
      exact fun h ↦ hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)))
    have hne : z.val ≠ (-z).val := by
      intro h
      have hz' := ZMod.val_injective p h
      exact (mul_ne_zero htwo hz) (by rw [two_mul, ← eq_neg_iff_add_eq_zero]; exact hz')
    rcases lt_or_gt_of_ne hne with h | h <;> simp [sign, h, h.not_gt]
  let c (g : G) := vectorColor sign (basis.repr (offset T g))
  refine ⟨c, ?_⟩
  intro B _ _ f hf hpf g
  let u := f.codRestrict T fun y ↦ AddSubgroup.torsionBy.nsmul_iff.mpr (hpf y)
  have hu : Function.Injective u := fun _ _ h ↦ hf (congrArg Subtype.val h)
  let : Infinite u.range := Infinite.of_injective u.rangeRestrict
    (AddMonoidHom.rangeRestrict_injective_iff.mpr hu)
  obtain ⟨h, hh⟩ := vector_splits sign hsign basis.repr.toAddMonoidHom basis.repr.injective
    u.range (offset T g)
  obtain ⟨y, hy⟩ := h.property
  refine ⟨y, ?_⟩
  have h₁ := offset_add T g (u y)
  have h₂ := offset_add T g (-u y)
  change offset T (g + f y) = _ at h₁
  change offset T (g + -f y) = _ at h₂
  change vectorColor sign (basis.repr (offset T g + h.val)) ≠
    vectorColor sign (basis.repr (offset T g - h.val)) at hh
  simpa only [c, sub_eq_add_neg, h₁, h₂, hy] using hh

/-- In bounded exponent, finiteness of all prime-torsion subgroups implies finiteness of
the whole group killed by the exponent. -/
private lemma finite_torsion (G : Type) [AddCommGroup G] (n : ℕ) (hn : n ≠ 0)
    (hf : ∀ p ∈ n.primeFactors, Finite (AddSubgroup.torsionBy G (p : ℤ))) :
    Finite (AddSubgroup.torsionBy G (n : ℤ)) := by
  classical
  induction n using induction_on_primes with
  | zero => contradiction
  | one =>
    apply Finite.of_injective (fun _ ↦ PUnit.unit)
    intro x y _
    apply Subtype.ext
    have hx := AddSubgroup.torsionBy.nsmul_iff.mp x.property
    have hy := AddSubgroup.torsionBy.nsmul_iff.mp y.property
    simpa using (hx.trans hy.symm)
  | prime_mul p a hp ih =>
    let D := AddSubgroup.torsionBy G ((p * a : ℕ) : ℤ)
    let T := AddSubgroup.torsionBy G (a : ℤ)
    let u : D →+ T := (p • D.subtype).codRestrict T fun x ↦ by
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      change a • p • (x : G) = 0
      rw [← mul_nsmul]
      exact AddSubgroup.torsionBy.nsmul_iff.mp x.property
    have : Finite T := ih (right_ne_zero_of_mul hn) fun q hq ↦
      hf q ((Nat.primeFactors_mono (dvd_mul_left a p) hn) hq)
    have := hf p (hp.mem_primeFactors (dvd_mul_right p a) hn)
    apply u.finite_iff_finite_ker_range.mpr
    refine ⟨?_, inferInstance⟩
    let lift (x : u.ker) : AddSubgroup.torsionBy G (p : ℤ) :=
      ⟨(x : D), AddSubgroup.torsionBy.nsmul_iff.mpr (congrArg Subtype.val x.property)⟩
    exact Finite.of_injective lift fun _ _ h ↦
      Subtype.ext (Subtype.ext (congrArg (fun z : AddSubgroup.torsionBy G (p : ℤ) ↦ z.val) h))

private lemma infinite_prime (H : Type) [AddCommGroup H] [Infinite H] (n : ℕ) (hn : n ≠ 0)
    (hkill : ∀ x : H, n • x = 0) :
    ∃ p ∈ n.primeFactors, Infinite (AddSubgroup.torsionBy H (p : ℤ)) := by
  by_contra! hf
  have := finite_torsion H n hn hf
  let lift (x : H) : AddSubgroup.torsionBy H (n : ℤ) :=
    ⟨x, AddSubgroup.torsionBy.nsmul_iff.mpr (hkill x)⟩
  have := Finite.of_injective lift fun _ _ h ↦ congrArg Subtype.val h
  exact (not_finite H).elim

/-- Bézout coefficients give an integer acting identically on the `p`-torsion and as
zero on each of the other prime-torsion subgroups. -/
private lemma prime_multiplier {n p : ℕ} (hp : p ∈ n.primeFactors) :
    ∃ k : ℤ, (p : ℤ) ∣ k - 1 ∧ ∀ q ∈ n.primeFactors, q ≠ p → (q : ℤ) ∣ k := by
  let m := ∏ q ∈ n.primeFactors.erase p, q
  have hc : m.Coprime p := Nat.coprime_prod_left_iff.mpr fun q hq ↦
    (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hq).2)
      (Nat.prime_of_mem_primeFactors hp)).mpr (Finset.mem_erase.mp hq).1
  obtain ⟨u, v, huv⟩ := hc.isCoprime
  refine ⟨u * m, ⟨-v, by linarith⟩, ?_⟩
  intro q hq hqp
  have hd : q ∣ m := Finset.dvd_prod_of_mem id (Finset.mem_erase.mpr ⟨hqp, hq⟩)
  exact dvd_mul_of_dvd_right (by exact_mod_cast hd) u

private lemma multiple_kills {G : Type*} [AddCommGroup G] {p : ℕ} {k : ℤ} {x : G}
    (h : p • x = 0) (hk : (p : ℤ) ∣ k) : k • x = 0 := by
  obtain ⟨z, rfl⟩ := hk
  rw [mul_comm, mul_smul, natCast_zsmul, h, smul_zero]

/-- Sum the prime colors modulo two. In every infinite subgroup there is an infinite
prime-torsion subgroup on which just one summand varies. -/
private lemma bounded_coloring (G : Type) [AddCommGroup G] (n : ℕ) (hn : n ≠ 0) (ho : Odd n)
    (hkill : ∀ x : G, n • x = 0) :
    ∃ c : G → ZMod 2, ∀ (H : AddSubgroup G) [Infinite H] (g : G),
      ∃ h : H, c (g + h) ≠ c (g - h) := by
  classical
  let P := n.primeFactors
  choose c hc using fun p : P ↦ prime_coloring G p (Nat.prime_of_mem_primeFactors p.property)
    (fun he ↦ ho.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors p.property))
  choose k hk using fun p : P ↦ prime_multiplier p.property
  let color (g : G) := ∑ p : P, c p (k p • g)
  refine ⟨color, ?_⟩
  intro H _ g
  obtain ⟨p, hp, hi⟩ := infinite_prime H n hn fun x ↦ Subtype.ext (by simpa using hkill x)
  let i : P := ⟨p, hp⟩
  let B := AddSubgroup.torsionBy H (p : ℤ)
  let f : B →+ G := H.subtype.comp B.subtype
  have hpf (y : B) : p • f y = 0 := by
    exact congrArg H.subtype (AddSubgroup.torsionBy.nsmul_iff.mp y.property)
  obtain ⟨y, hy⟩ := hc i B f (H.subtype_injective.comp B.subtype_injective) hpf (k i • g)
  have hself : k i • f y = f y := by
    have hz := multiple_kills (hpf y) (hk i).1
    simpa [sub_smul, sub_eq_zero] using hz
  have hother (q : P) (hne : q ≠ i) : k q • f y = 0 :=
    multiple_kills (hpf y) ((hk q).2 p hp fun h ↦ hne (Subtype.ext h.symm))
  refine ⟨y.val, ?_⟩
  change (∑ q : P, c q (k q • (g + f y))) ≠ ∑ q : P, c q (k q • (g - f y))
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ (fun q : P ↦ c q (k q • (g - f y))) (Finset.mem_univ i)]
  have he : (∑ q ∈ Finset.univ.erase i, c q (k q • (g + f y))) =
      ∑ q ∈ Finset.univ.erase i, c q (k q • (g - f y)) := by
    apply Finset.sum_congr rfl
    intro q hq
    simp [smul_add, smul_sub, hother q (Finset.ne_of_mem_erase hq)]
  rw [he, ne_eq, add_right_inj]
  simpa only [smul_add, smul_sub, hself] using hy

/--
**Uncountable abelian groups of odd exponent have coset-free partitions.** Every uncountable
abelian group $G$ of finite odd exponent can be written as $G = A_1 \cup A_2$ with $A_1$ and $A_2$
disjoint, so that for every infinite subgroup $H$ of $G$ and every $g \in G$, the coset $gH$ is
contained neither in $A_1$ nor in $A_2$. This answers Kourovka Problem 13.46 in the affirmative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 13.46 (I. V. Protasov); resolution: E. G. Zelenyuk, Math. Notes 67 (2000), 599-602, Kourovka
Archive, Problem 13.46 (answer: Yes, it can).
-/
theorem oddExponentCosetFreePartition_holds : oddExponentCosetFreePartition := by
  classical
  intro G _ _ hn ho
  obtain ⟨c, hc⟩ := bounded_coloring (Additive G) (Monoid.exponent G) hn ho fun x ↦
    congrArg Additive.ofMul (Monoid.pow_exponent_eq_one x.toMul)
  let A : Set G := {x | c (Additive.ofMul x) = 0}
  refine ⟨A, Aᶜ, Set.union_compl_self A, disjoint_compl_right, ?_⟩
  intro H hi g
  have : Infinite H.toAddSubgroup := Set.infinite_coe_iff.mpr hi
  obtain ⟨h, hd⟩ := hc H.toAddSubgroup (Additive.ofMul g)
  let y : H := ⟨h.val.toMul, h.property⟩
  have h₁ : g * y.val ∈ g • (H : Set G) := Set.smul_mem_smul_set y.property
  have h₂ : g * y.val⁻¹ ∈ g • (H : Set G) := Set.smul_mem_smul_set (H.inv_mem y.property)
  rw [sub_eq_add_neg] at hd
  change c (Additive.ofMul (g * y.val)) ≠ c (Additive.ofMul (g * y.val⁻¹)) at hd
  have one_of_ne_zero : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  exact ⟨fun hA ↦ hd ((hA h₁).trans (hA h₂).symm), fun hA ↦
    hd ((one_of_ne_zero _ (hA h₁)).trans (one_of_ne_zero _ (hA h₂)).symm)⟩

end MathlibExt.GroupTheory.OddExponentCosetFreePartitionKourovka13Problem46Wanted
