/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring

/-!
# Restricted sumsets and restricted signed sumsets of integer finsets

`restrictedSumset h A` is `h^∧ A`, the sums of `h` distinct elements of `A` (defined for
finsets of any additive commutative monoid), and
`restrictedSignedSumset h A` is `h^∧_± A`, the sums `Σ λ_a a` with `λ_a ∈ {-1, 0, 1}` and
`Σ |λ_a| = h`. Both are computable, and the membership lemmas recover the coefficient
definitions.

## Main statements

* `MetaMathlibExt.mem_restrictedSumset_iff`
* `MetaMathlibExt.mem_restrictedSignedSumset_iff`
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Restricted sumset.** For a natural number $h$ and a finite subset $A$ of an additive
commutative monoid $G$, the restricted sumset $h^{\wedge} A$ is the set of all sums
$\sum_{a \in B} a$ with $B$ an $h$-element subset of $A$, that is, the sums of $h$ distinct
elements of $A$. In particular $0^{\wedge} A = \{0\}$.

The source works in the integers; here $G$ is an arbitrary additive commutative monoid.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of
restricted sumset. -/
public def restrictedSumset {G : Type*} [AddCommMonoid G] [DecidableEq G] (h : ℕ)
    (A : Finset G) : Finset G :=
  (A.powersetCard h).image (fun B => ∑ a ∈ B, a)

/-- **Restricted signed sumset.** For a natural number $h$ and a finite set $A$ of integers, the
restricted signed sumset $h^{\wedge}_{\pm} A$ is the set of all integers
$\sum_{a \in B} a - 2 \sum_{a \in N} a$, where $B$ ranges over the $h$-element subsets of $A$ and
$N$ ranges over the subsets of $B$. These are the sums of the elements of $B$ in which the
elements of $N$ are given a negative sign.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of
restricted signed sumset. -/
public def restrictedSignedSumset (h : ℕ) (A : Finset ℤ) : Finset ℤ :=
  ((A.powersetCard h).sigma (fun B => B.powerset)).image
    (fun p => ∑ a ∈ p.1, a - 2 * ∑ a ∈ p.2, a)


/-- **Coefficient description of the restricted sumset.** For a natural number $h$, a finite set
$A$ of integers and an integer $x$, $x$ lies in the restricted sumset $h^{\wedge} A$ if and only
if there is a function $c : \mathbb{Z} \to \mathbb{Z}$ with $c(a) \in \{0, 1\}$ for every
$a \in A$, $\sum_{a \in A} c(a) = h$ and $x = \sum_{a \in A} c(a)\, a$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of
restricted sumset. -/
public theorem mem_restrictedSumset_iff (h : ℕ) (A : Finset ℤ) (x : ℤ) :
    x ∈ restrictedSumset h A ↔
      ∃ c : ℤ → ℤ,
        (∀ a ∈ A, c a = 0 ∨ c a = 1) ∧
        ∑ a ∈ A, c a = (h : ℤ) ∧
        x = ∑ a ∈ A, c a * a := by
  constructor
  · simp only [restrictedSumset, Finset.mem_image, Finset.mem_powersetCard]
    rintro ⟨B, ⟨hBA, hcard⟩, rfl⟩
    refine ⟨fun a => if a ∈ B then 1 else 0, ?_, ?_, ?_⟩
    · intro a ha
      by_cases hab : a ∈ B <;> simp [hab]
    · have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
      simp [hAB, hcard]
    · have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
      simp [hAB]
  · rintro ⟨c, hc, hsum, rfl⟩
    let B := A.filter fun a => c a = 1
    have hBA : B ⊆ A := Finset.filter_subset _ _
    have hcoeff (a : ℤ) (ha : a ∈ A) : c a = if a ∈ B then 1 else 0 := by
      have := hc a ha
      simp only [B, Finset.mem_filter]
      rcases this with h0 | h1
      · simp [h0]
      · simp [h1, ha]
    have hcardZ : (B.card : ℤ) = h := by
      have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
      calc
        (B.card : ℤ) = ∑ a ∈ A, c a := by
          rw [Finset.sum_congr rfl fun a ha => hcoeff a ha]
          simp [hAB]
        _ = h := hsum
    have hcard : B.card = h := by exact_mod_cast hcardZ
    refine Finset.mem_image.mpr ⟨B, Finset.mem_powersetCard.mpr ⟨hBA, hcard⟩, ?_⟩
    have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
    symm
    rw [Finset.sum_congr rfl fun a ha => congrArg (fun z => z * a) (hcoeff a ha)]
    simp [hAB]

/-- **Coefficient description of the restricted signed sumset.** For a natural number $h$, a
finite set $A$ of integers and an integer $x$, $x$ lies in the restricted signed sumset
$h^{\wedge}_{\pm} A$ if and only if there is a function $c : \mathbb{Z} \to \mathbb{Z}$ with
$c(a) \in \{-1, 0, 1\}$ for every $a \in A$, $\sum_{a \in A} |c(a)| = h$ and
$x = \sum_{a \in A} c(a)\, a$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of
restricted signed sumset. -/
public theorem mem_restrictedSignedSumset_iff (h : ℕ) (A : Finset ℤ) (x : ℤ) :
    x ∈ restrictedSignedSumset h A ↔
      ∃ c : ℤ → ℤ,
        (∀ a ∈ A, c a = -1 ∨ c a = 0 ∨ c a = 1) ∧
        ∑ a ∈ A, |c a| = (h : ℤ) ∧
        x = ∑ a ∈ A, c a * a := by
  constructor
  · simp only [restrictedSignedSumset, Finset.mem_image, Finset.mem_sigma,
      Finset.mem_powersetCard, Finset.mem_powerset]
    rintro ⟨⟨B, N⟩, ⟨⟨hBA, hcard⟩, hNB⟩, rfl⟩
    let c : ℤ → ℤ := fun a => if a ∈ B then if a ∈ N then -1 else 1 else 0
    refine ⟨c, ?_, ?_, ?_⟩
    · intro a ha
      by_cases hab : a ∈ B
      · by_cases han : a ∈ N <;> simp [c, hab, han]
      · simp [c, hab]
    · have hone (a : ℤ) (ha : a ∈ B) : |c a| = 1 := by
        by_cases han : a ∈ N <;> simp [c, ha, han]
      have hzero (a : ℤ) (haA : a ∈ A) (haB : a ∉ B) : |c a| = 0 := by
        simp [c, haB]
      calc
        ∑ a ∈ A, |c a| = ∑ a ∈ B, |c a| :=
          (Finset.sum_subset hBA hzero).symm
        _ = ∑ _a ∈ B, (1 : ℤ) := Finset.sum_congr rfl hone
        _ = h := by simp [hcard]
    · have hcformula (a : ℤ) (ha : a ∈ B) :
          c a * a = a - 2 * (if a ∈ N then a else 0) := by
        by_cases han : a ∈ N
        · simp [c, ha, han]
          ring
        · simp [c, ha, han]
      have hout (a : ℤ) (haA : a ∈ A) (haB : a ∉ B) : c a * a = 0 := by
        simp [c, haB]
      have hNB' : B ∩ N = N := Finset.inter_eq_right.mpr hNB
      symm
      calc
        ∑ a ∈ A, c a * a = ∑ a ∈ B, c a * a :=
          (Finset.sum_subset hBA hout).symm
        _ = ∑ a ∈ B, (a - 2 * (if a ∈ N then a else 0)) :=
          Finset.sum_congr rfl hcformula
        _ = ∑ a ∈ B, a - 2 * ∑ a ∈ N, a := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          simp [hNB']
  · rintro ⟨c, hc, hsum, rfl⟩
    let B := A.filter fun a => c a ≠ 0
    let N := B.filter fun a => c a = -1
    have hBA : B ⊆ A := Finset.filter_subset _ _
    have hNB : N ⊆ B := Finset.filter_subset _ _
    have hcB (a : ℤ) (ha : a ∈ A) : |c a| = if a ∈ B then 1 else 0 := by
      rcases hc a ha with hm | h0 | h1
      · simp [B, ha, hm]
      · simp [B, ha, h0]
      · simp [B, ha, h1]
    have hcardZ : (B.card : ℤ) = h := by
      have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
      calc
        (B.card : ℤ) = ∑ a ∈ A, |c a| := by
          rw [Finset.sum_congr rfl fun a ha => hcB a ha]
          simp [hAB]
        _ = h := hsum
    have hcard : B.card = h := by exact_mod_cast hcardZ
    refine Finset.mem_image.mpr ⟨⟨B, N⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨hBA, hcard⟩,
        Finset.mem_powerset.mpr hNB⟩
    · have hcformula (a : ℤ) (ha : a ∈ B) :
          c a * a = a - 2 * (if a ∈ N then a else 0) := by
        have haA := hBA ha
        rcases hc a haA with hm | h0 | h1
        · simp [N, ha, hm]
          ring
        · have : a ∉ B := by simp [B, haA, h0]
          exact (this ha).elim
        · simp [N, ha, h1]
      have hout (a : ℤ) (haA : a ∈ A) (haB : a ∉ B) : c a * a = 0 := by
        have hzero : c a = 0 := by
          simpa only [B, Finset.mem_filter, haA, true_and, not_not] using haB
        simp [hzero]
      have hNB' : B ∩ N = N := Finset.inter_eq_right.mpr hNB
      symm
      calc
        ∑ a ∈ A, c a * a = ∑ a ∈ B, c a * a :=
          (Finset.sum_subset hBA hout).symm
        _ = ∑ a ∈ B, (a - 2 * (if a ∈ N then a else 0)) :=
          Finset.sum_congr rfl hcformula
        _ = ∑ a ∈ B, a - 2 * ∑ a ∈ N, a := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          simp [hNB']

end

private theorem mem_restrictedSignedSumset_support {h : ℕ} {A : Finset ℤ} {x : ℤ} :
    x ∈ restrictedSignedSumset h A ↔
      ∃ B ⊆ A, B.card = h ∧ ∃ N ⊆ B, (∑ y ∈ B, y) - 2 * ∑ y ∈ N, y = x := by
  simp only [restrictedSignedSumset, Finset.mem_image, Finset.mem_sigma,
    Finset.mem_powersetCard, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨B, N⟩, ⟨⟨hBA, hB⟩, hNB⟩, he⟩
    exact ⟨B, hBA, hB, N, hNB, he⟩
  · rintro ⟨B, hBA, hB, N, hNB, he⟩
    exact ⟨⟨B, N⟩, ⟨⟨hBA, hB⟩, hNB⟩, he⟩

/-- Adjoining a new largest element adds at least `2 * h` distinct signed sums. -/
private theorem card_restrictedSignedSumset_insert {h : ℕ} {A : Finset ℤ} {b : ℤ}
    (hA : ∀ x ∈ A, 0 ≤ x) (hb : ∀ x ∈ A, x < b)
    (hS : (restrictedSignedSumset h A).Nonempty) :
    (restrictedSignedSumset h A).card + 2 * h ≤
      (restrictedSignedSumset h (insert b A)).card := by
  let S := restrictedSignedSumset h A
  let T := restrictedSignedSumset h (insert b A)
  have hST : S ⊆ T := by
    intro x hx
    obtain ⟨B, hBA, hB, N, hNB, he⟩ := mem_restrictedSignedSumset_support.mp hx
    exact mem_restrictedSignedSumset_support.mpr
      ⟨B, hBA.trans (Finset.subset_insert _ _), hB, N, hNB, he⟩
  -- Take the support of a maximal signed sum. Making every sign positive
  -- does not decrease it, so the unsigned sum `M` still bounds all old sums.
  obtain ⟨B, hBA, hB, N, hNB, he⟩ :=
    mem_restrictedSignedSumset_support.mp (S.max'_mem hS)
  let M := ∑ x ∈ B, x
  have hM : 0 ≤ M := Finset.sum_nonneg fun x hx => hA x (hBA hx)
  have hmax : S.max' hS ≤ M := by
    have hN : 0 ≤ ∑ x ∈ N, x := Finset.sum_nonneg fun x hx => hA x (hBA (hNB hx))
    change _ ≤ ∑ x ∈ B, x
    omega
  have hbound {y : ℤ} (hy : y ∈ S) : -M ≤ y ∧ y ≤ M := by
    obtain ⟨D, hDA, hD, E, hED, hDE⟩ := mem_restrictedSignedSumset_support.mp hy
    have hE : 0 ≤ ∑ x ∈ E, x := Finset.sum_nonneg fun x hx => hA x (hDA (hED hx))
    have hsum : ∑ x ∈ E, x ≤ ∑ x ∈ D, x :=
      Finset.sum_le_sum_of_subset_of_nonneg hED fun x hx _ => hA x (hDA hx)
    have hmem : (∑ x ∈ D, x) ∈ S := mem_restrictedSignedSumset_support.mpr
      ⟨D, hDA, hD, ∅, Finset.empty_subset _, by simp⟩
    have hDM := (S.le_max' _ hmem).trans hmax
    omega
  -- Replacing each `x ∈ B` by `b` gives `h` distinct sums above `M`.
  -- Their negatives give another `h` below `-M`.
  let f (x : ℤ) := M + (b - x)
  have hf {x : ℤ} (hx : x ∈ B) : M < f x := by
    have := hb x (hBA hx)
    dsimp [f]
    omega
  have hnew {x : ℤ} (hx : x ∈ B) : f x ∈ T ∧ -f x ∈ T := by
    let D := insert b (B.erase x)
    have hbe : b ∉ B.erase x := fun hm =>
      (lt_irrefl b) (hb b (hBA (Finset.mem_of_mem_erase hm)))
    have hDA : D ⊆ insert b A :=
      Finset.insert_subset_insert _ ((Finset.erase_subset _ _).trans hBA)
    have hD : D.card = h := by
      dsimp [D]
      rw [Finset.card_insert_of_notMem hbe, Finset.card_erase_add_one hx, hB]
    have hsum : ∑ y ∈ D, y = f x := by
      dsimp [D, f, M]
      rw [Finset.sum_insert hbe]
      have he := Finset.sum_erase_add B (fun y => y) hx
      omega
    exact ⟨mem_restrictedSignedSumset_support.mpr
      ⟨D, hDA, hD, ∅, Finset.empty_subset _, by simp [hsum]⟩,
      mem_restrictedSignedSumset_support.mpr
        ⟨D, hDA, hD, D, by intro y hy; exact hy, by rw [hsum]; ring⟩⟩
  let P := B.image f
  let Q := B.image fun x => -f x
  have hf_inj : Function.Injective f := by
    intro x y hxy
    dsimp [f] at hxy
    omega
  have hP : P.card = h := (Finset.card_image_of_injective B hf_inj).trans hB
  have hQ : Q.card = h :=
    (Finset.card_image_of_injective B fun _ _ hxy => hf_inj (neg_injective hxy)).trans hB
  have hPmem {y : ℤ} (hy : y ∈ P) : y ∈ T ∧ M < y := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨(hnew hx).1, hf hx⟩
  have hQmem {y : ℤ} (hy : y ∈ Q) : y ∈ T ∧ y < -M := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨(hnew hx).2, neg_lt_neg (hf hx)⟩
  have hPQ : Disjoint P Q := Finset.disjoint_left.mpr fun _ hp hq => by
    have := (hPmem hp).2
    have := (hQmem hq).2
    omega
  have hsub : P ∪ Q ⊆ T \ S := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨hyT, hlt⟩ := hPmem hy
      exact Finset.mem_sdiff.mpr ⟨hyT, fun hyS => (not_lt_of_ge (hbound hyS).2) hlt⟩
    · obtain ⟨hyT, hlt⟩ := hQmem hy
      exact Finset.mem_sdiff.mpr ⟨hyT, fun hyS => (not_lt_of_ge (hbound hyS).1) hlt⟩
  have hgrow := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hPQ, hP, hQ] at hgrow
  have hcount := Finset.card_sdiff_add_card_eq_card hST
  change S.card + 2 * h ≤ T.card
  omega

@[expose] public section

/-- **Set of values of a finite integer sequence.** For a sequence $a_0, \dots, a_{k-1}$ of
integers, this is the finite set $\{a_i : 0 \le i < k\}$ of its values.

No order or injectivity is assumed; the statements that use it assume what they need.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, notation for
ordered finite sets. -/
public def orderedFinset {k : ℕ} (a : Fin k → ℤ) : Finset ℤ :=
  Finset.univ.image a

/-- **Initial segment of a finite integer sequence.** For a sequence $a_0, \dots, a_{k-1}$ of
integers and a natural number $n$, the initial segment of length $n$ is the set
$\{a_i : 0 \le i < k,\ i < n\}$ of the values at indices below $n$; it is the set of all values
of the sequence when $n \ge k$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, notation for
initial subsets. -/
public def initialSegment {k : ℕ} (a : Fin k → ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.univ.filter fun i : Fin k => (i : ℕ) < n).image a

/-- **Extending a restricted signed sumset bound from the first $h+1$ elements.** Let $h \ge 3$
and $k \ge h + 1$, let $a_1 < a_2 < \dots < a_k$ be positive integers, and let $t \ge 0$ be an
integer. Put $A = \{a_1, \dots, a_k\}$ and $A_{h+1} = \{a_1, \dots, a_{h+1}\}$, and write
$h^{\wedge}_{\pm} B$ for the restricted signed $h$-fold sumset of a finite set $B$. If
$|h^{\wedge}_{\pm} A_{h+1}| \ge (h+1)^2 + t$, then $|h^{\wedge}_{\pm} A| \ge 2hk - h^2 + 1 + t$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 1. -/
public theorem card_restrictedSignedSumset_ge_of_initialSegment
    (h k : ℕ) (hh : 3 ≤ h) (hk : h ≤ k - 1) (a : Fin k → ℤ) (t : ℤ)
    (ha : StrictMono a) (hpos : ∀ i, 0 < a i) (ht : 0 ≤ t)
    (hinitial : ((restrictedSignedSumset h (initialSegment a (h + 1))).card : ℤ) ≥
      ((h + 1 : ℕ) : ℤ) ^ 2 + t) :
    ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1 + t := by
  let S₀ := restrictedSignedSumset h (initialSegment a (h + 1))
  have hsq : (0 : ℤ) < ((h + 1 : ℕ) : ℤ) ^ 2 :=
    pow_pos (by exact_mod_cast Nat.succ_pos h) _
  change (S₀.card : ℤ) ≥ _ at hinitial
  have hS₀ : 0 < S₀.card := by omega
  have grow (n : ℕ) (hn : h + 1 + n ≤ k) :
      S₀.card + 2 * h * n ≤ (restrictedSignedSumset h (initialSegment a (h + 1 + n))).card := by
    induction n with
    | zero => simp [S₀]
    | succ n ih =>
      let m := h + 1 + n
      have hm : m < k := by dsimp [m]; omega
      let b := a ⟨m, hm⟩
      let A := initialSegment a m
      have hold : S₀.card + 2 * h * n ≤ (restrictedSignedSumset h A).card := ih (by omega)
      have hS : (restrictedSignedSumset h A).Nonempty := Finset.card_pos.mp (by omega)
      have hA {x : ℤ} (hx : x ∈ A) : ∃ i : Fin k, (i : ℕ) < m ∧ a i = x := by
        simpa only [A, initialSegment, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and] using hx
      have hstep := card_restrictedSignedSumset_insert (b := b)
        (fun x hx => by obtain ⟨i, _, rfl⟩ := hA hx; exact (hpos i).le)
        (fun x hx => by obtain ⟨i, hi, rfl⟩ := hA hx; exact ha hi) hS
      have hnext : initialSegment a (m + 1) = insert b A := by
        ext x
        simp only [A, b, initialSegment, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨i, hi, rfl⟩
          by_cases hi' : (i : ℕ) < m
          · exact Or.inr ⟨i, hi', rfl⟩
          · have he : (i : ℕ) = m := by omega
            exact Or.inl (congrArg a (Fin.ext he))
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨⟨m, hm⟩, by simp, rfl⟩
          · exact ⟨i, by omega, rfl⟩
      change _ ≤ (restrictedSignedSumset h (initialSegment a (m + 1))).card
      rw [hnext, Nat.mul_succ, ← Nat.add_assoc]
      exact (Nat.add_le_add_right hold _).trans hstep
  have hfull : initialSegment a k = orderedFinset a := by
    simp [initialSegment, orderedFinset, Fin.is_lt]
  let n := k - (h + 1)
  have hn : h + 1 + n = k := by dsimp [n]; omega
  have hcount := grow n hn.le
  rw [hn, hfull] at hcount
  have hcountZ : (S₀.card : ℤ) + 2 * (h : ℤ) * (n : ℤ) ≤
      ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) := by exact_mod_cast hcount
  have hnZ : ((h + 1 : ℕ) : ℤ) + (n : ℤ) = (k : ℤ) := by exact_mod_cast hn
  have hrhs : 2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1 + t =
      ((h + 1 : ℕ) : ℤ) ^ 2 + t + 2 * (h : ℤ) * (n : ℤ) := by
    rw [← hnZ, Nat.cast_add, Nat.cast_one]
    ring
  rw [hrhs]
  omega

end

end MetaMathlibExt
