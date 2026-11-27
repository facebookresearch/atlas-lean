/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Antichain
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Homomesy of antichain cardinality under type-A rowmotion

We prove that every periodic antichain under type-A rowmotion has average cardinality
half the rank. The change in the sum of the antichain's interval lengths gives a
telescoping proof.
-/

namespace MathlibExt.Combinatorics.RootPosetRowmotionHomomesyWanted

@[expose] public section

open scoped BigOperators

/-- **Homomesy.** Let $X$ be a type, $\sigma \colon X \to X$ a map, $f \colon X \to \mathbb{Q}$ a
function and $c \in \mathbb{Q}$. Then $f$ is homomesic under $\sigma$ with average $c$ when $X$ is
finite, $\sigma$ is bijective, and for every $x \in X$ and every $k > 0$ with $\sigma^k(x) = x$
the average $\frac{1}{k} \sum_{i=0}^{k-1} f(\sigma^i(x))$ equals $c$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsHomomesic {α : Type*} (σ : α → α) (f : α → ℚ) (c : ℚ) : Prop :=
  Finite α ∧
  Function.Bijective σ ∧
  ∀ (x : α) (k : ℕ), 0 < k → Nat.iterate σ k x = x →
    (Finset.sum (Finset.range k) (fun i => f (Nat.iterate σ i x))) / (k : ℚ) = c

/-- **Finite antichains of a poset.** For a partially ordered set $P$, the finite antichains of
$P$ are the finite subsets $A \subseteq P$ in which no element is below a different element.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def PosetAntichain (P : Type*) [PartialOrder P] :=
  { s : Finset P // IsAntichain (· ≤ ·) (s : Set P) }

/-- **Antichain cardinality statistic.** For a partially ordered set $P$, a function $f$ from the
finite antichains of $P$ to $\mathbb{Q}$ is the antichain cardinality statistic when
$f(A) = |A|$ for every finite antichain $A$ of $P$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsAntichainCardinality (P : Type*) [PartialOrder P]
    (f : PosetAntichain P → ℚ) : Prop :=
  ∀ A : PosetAntichain P, f A = (A.val.card : ℚ)

/-- **Rowmotion on antichains.** For a partially ordered set $P$, a map $\rho$ from the finite
antichains of $P$ to themselves is antichain rowmotion when $\rho$ is bijective and, for every
finite antichain $A$, $\rho(A)$ is the set of minimal elements of the complement of the down-set
of $A$: an element $x \in P$ lies in $\rho(A)$ exactly when $x \not\le a$ for all $a \in A$ and
every $y \le x$ with $y \not\le a$ for all $a \in A$ equals $x$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsAntichainRowmotion (P : Type*) [PartialOrder P]
    (rhoPrime : PosetAntichain P → PosetAntichain P) : Prop :=
  Function.Bijective rhoPrime ∧
  ∀ (A : PosetAntichain P) (x : P),
    x ∈ (rhoPrime A).val ↔
      ((¬ ∃ a ∈ A.val, x ≤ a) ∧
        ∀ (y : P), (¬ ∃ a ∈ A.val, y ≤ a) → y ≤ x → y = x)

/-- **Type-A root poset.** A partially ordered set $P$ is a type-A root poset of rank $n$, for a
natural number $n$, when there is a bijection $a \mapsto (i_a, j_a)$ from $P$ onto the set of
pairs $(i, j)$ of integers with $0 \le i \le j < n$ such that $a \le b$ holds exactly when the
interval $[i_a, j_a]$ is contained in $[i_b, j_b]$, that is, $i_b \le i_a$ and $j_a \le j_b$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsTypeARootPoset (P : Type*) [PartialOrder P] (n : ℕ) : Prop :=
  ∃ e : P ≃ { p : Fin n × Fin n // p.1 ≤ p.2 },
    ∀ (a b : P), a ≤ b ↔
      ((e b).val.1 ≤ (e a).val.1 ∧ (e a).val.2 ≤ (e b).val.2)

/-- **Type-A rowmotion homomesy conjecture.** The proposition that for every natural number $n$,
every finite partially ordered set $P$ that is a type-A root poset of rank $n$ (there is a
bijection $a \mapsto (i_a, j_a)$ from $P$ onto the set of pairs $(i, j)$ of integers with
$0 \le i \le j < n$ such that $a \le b$ holds exactly when $i_b \le i_a$ and $j_a \le j_b$), and
every bijection $\rho$ of the set of finite antichains of $P$ that sends each antichain $A$ to the
set of minimal elements of the complement of the down-set of $A$, the set of finite antichains of
$P$ is finite, $\rho$ is bijective, and for every antichain $A$ and every $k > 0$ with
$\rho^k(A) = A$ the average $\frac{1}{k} \sum_{i=0}^{k-1} |\rho^i(A)|$ equals $n/2$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def conjecture : Prop :=
  ∀ (n : ℕ) (P : Type*) [PartialOrder P] [Finite P]
    (rhoPrime : PosetAntichain P → PosetAntichain P) (f : PosetAntichain P → ℚ),
    IsTypeARootPoset P n →
      IsAntichainRowmotion P rhoPrime →
        IsAntichainCardinality P f →
          IsHomomesic rhoPrime f ((n : ℚ) / 2)

end

section IntervalCoordinates

variable {n : ℕ} {P : Type*}
  (e : P ≃ {p : Fin n × Fin n // p.1 ≤ p.2})

private def left (x : P) : ℕ := (e x).val.1
private def right (x : P) : ℕ := (e x).val.2

private theorem left_le_right (x : P) : left e x ≤ right e x := (e x).prop
private theorem right_lt_rank (x : P) : right e x < n := (e x).val.2.isLt

private def interval (i j : ℕ) (hij : i ≤ j) (hj : j < n) : P :=
  e.symm ⟨(⟨i, hij.trans_lt hj⟩, ⟨j, hj⟩), hij⟩

@[simp] private theorem left_interval (i j : ℕ) (hij : i ≤ j) (hj : j < n) :
    left e (interval e i j hij hj) = i := by simp [left, interval]

@[simp] private theorem right_interval (i j : ℕ) (hij : i ≤ j) (hj : j < n) :
    right e (interval e i j hij hj) = j := by simp [right, interval]

variable [PartialOrder P]
  (he : ∀ a b : P, a ≤ b ↔ left e b ≤ left e a ∧ right e a ≤ right e b)
  (A : PosetAntichain P)

include he in
private theorem left_injOn : Set.InjOn (left e) (A.val : Set P) := by
  intro a ha b hb hab
  rcases le_total (right e a) (right e b) with h | h
  · exact A.prop.eq ha hb ((he a b).2 ⟨hab.ge, h⟩)
  · exact A.prop.eq' ha hb ((he b a).2 ⟨hab.le, h⟩)

/-- At boundary index `i`, take the largest right endpoint plus one among intervals
starting before `i`, using `i - 1` as the lower bound. -/
private def height (i : ℕ) : ℕ :=
  max (i - 1) ((A.val.filter fun a => left e a < i).sup fun a => right e a + 1)

private theorem pred_le_height (i : ℕ) : i - 1 ≤ height e A i :=
  le_max_left ..

private theorem right_succ_le_height {a : P} (ha : a ∈ A.val) {i : ℕ}
    (hi : left e a < i) : right e a + 1 ≤ height e A i :=
  (Finset.le_sup (f := fun a => right e a + 1) (Finset.mem_filter.2 ⟨ha, hi⟩)).trans
    (le_max_right ..)

private theorem height_le_rank {i : ℕ} (hi : i ≤ n + 1) : height e A i ≤ n := by
  refine max_le (by omega) (Finset.sup_le fun a _ => ?_)
  exact right_lt_rank e a

private theorem height_mono : Monotone (height e A) := by
  intro i j hij
  refine max_le ?_ (Finset.sup_le ?_)
  · exact (Nat.sub_le_sub_right hij 1).trans (pred_le_height e A j)
  · intro a ha
    obtain ⟨ha, hi⟩ := Finset.mem_filter.1 ha
    exact right_succ_le_height e A ha (hi.trans_le hij)

private theorem lt_height_succ_iff {i j : ℕ} (hij : i ≤ j) :
    j < height e A (i + 1) ↔ ∃ a ∈ A.val, left e a ≤ i ∧ j ≤ right e a := by
  simp only [height, Nat.add_sub_cancel, lt_max_iff, not_lt_of_ge hij, false_or,
    Finset.lt_sup_iff, Finset.mem_filter, Nat.lt_succ_iff]
  constructor
  · rintro ⟨a, ⟨ha, hai⟩, haj⟩
    exact ⟨a, ha, hai, haj⟩
  · rintro ⟨a, ha, hai, haj⟩
    exact ⟨a, ⟨ha, hai⟩, haj⟩

include he

private theorem mem_downset_iff (x : P) :
    (∃ a ∈ A.val, x ≤ a) ↔ right e x < height e A (left e x + 1) := by
  simp only [he, lt_height_succ_iff e A (left_le_right e x)]

private theorem height_of_mem {a : P} (ha : a ∈ A.val) :
    height e A (left e a + 1) = right e a + 1 := by
  apply le_antisymm _ (right_succ_le_height e A ha (Nat.lt_succ_self _))
  refine max_le ?_ (Finset.sup_le ?_)
  · simpa using (left_le_right e a).trans (Nat.le_succ _)
  · intro b hb
    obtain ⟨hb, hl⟩ := Finset.mem_filter.1 hb
    by_contra! h
    have hab : a = b := A.prop.eq ha hb ((he _ _).2 ⟨Nat.lt_succ_iff.1 hl, by omega⟩)
    subst b
    exact (lt_irrefl _) h

private theorem height_lt_height_succ_of_mem {a : P} (ha : a ∈ A.val) :
    height e A (left e a) < height e A (left e a + 1) := by
  rw [height_of_mem e he A ha]
  apply Nat.lt_succ_of_le
  refine max_le ((Nat.sub_le ..).trans (left_le_right e a)) (Finset.sup_le ?_)
  intro b hb
  obtain ⟨hb, hl⟩ := Finset.mem_filter.1 hb
  by_contra! h
  have hab : a = b := A.prop.eq ha hb ((he _ _).2 ⟨hl.le, by omega⟩)
  exact hl.ne (congrArg (left e) hab.symm)

private theorem exists_left_mem_iff (i : ℕ) :
    (∃ a ∈ A.val, left e a = i) ↔
      height e A i < height e A (i + 1) ∧ i < height e A (i + 1) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨height_lt_height_succ_of_mem e he A ha,
      (left_le_right e a).trans_lt (by rw [height_of_mem e he A ha]; omega)⟩
  · rintro ⟨hstep, hi⟩
    let j := height e A (i + 1) - 1
    have hij : i ≤ j := by omega
    have hj : j < height e A (i + 1) := by omega
    obtain ⟨a, ha, hleft, hright⟩ := (lt_height_succ_iff e A hij).1 hj
    refine ⟨a, ha, le_antisymm hleft ?_⟩
    by_contra! h
    have := right_succ_le_height e A ha h
    omega

variable {rho : PosetAntichain P → PosetAntichain P} (hrho : IsAntichainRowmotion P rho)

include hrho

private theorem mem_rowmotion_iff (x : P) :
    x ∈ (rho A).val ↔ right e x = height e A (left e x + 1) ∧
      height e A (left e x + 1) < height e A (left e x + 2) := by
  simp only [hrho.2, mem_downset_iff e he A, not_lt]
  constructor
  · rintro ⟨hout, hmin⟩
    let y := interval e (left e x) (height e A (left e x + 1))
      (by simpa using pred_le_height e A (left e x + 1)) (hout.trans_lt (right_lt_rank e x))
    have hy : y = x := hmin y (by simp [y]) ((he _ _).2 (by simpa [y] using hout))
    have hright : right e x = height e A (left e x + 1) := by
      simpa [y] using congrArg (right e) hy.symm
    refine ⟨hright, ?_⟩
    by_cases hs : left e x = right e x
    · have := pred_le_height e A (left e x + 2)
      omega
    · let z := interval e (left e x + 1) (right e x)
        (by have := left_le_right e x; omega) (right_lt_rank e x)
      by_contra! h
      have hz : z = x := hmin z (by simpa [z, ← hright, Nat.add_assoc] using h)
        ((he _ _).2 (by simp [z]))
      simpa [z] using congrArg (left e) hz
  · rintro ⟨hright, hstep⟩
    refine ⟨hright.ge, fun y hout hy => ?_⟩
    obtain ⟨hleft, hright'⟩ := (he _ _).1 hy
    have hh := height_mono e A (Nat.add_le_add_right hleft 1)
    have hr : right e y = right e x := by omega
    have hl : left e y = left e x := by
      by_contra! h
      have hm := height_mono e A (show left e x + 2 ≤ left e y + 1 by omega)
      omega
    exact le_antisymm hy ((he _ _).2 ⟨hl.le, hr.ge⟩)

private theorem exists_left_succ_mem_rowmotion_iff (i : ℕ) (hi : i ≤ n) :
    (∃ x ∈ (rho A).val, left e x + 1 = i) ↔
      0 < i ∧ height e A i < height e A (i + 1) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Nat.succ_pos _, (mem_rowmotion_iff e he A hrho x).1 hx |>.2⟩
  · rintro ⟨hpos, hstep⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hr : height e A (j + 1) < n :=
      hstep.trans_le (height_le_rank e A (by omega))
    let x := interval e j (height e A (j + 1))
      (by simpa using pred_le_height e A (j + 1)) hr
    exact ⟨x, (mem_rowmotion_iff e he A hrho x).2 (by simpa [x] using hstep), by simp [x]⟩

omit [PartialOrder P] he hrho in
private theorem sum_by_key {X : Finset P} {key : P → ℕ}
    (hinj : Set.InjOn key (X : Set P)) {m : ℕ} (hm : ∀ x ∈ X, key x < m)
    {f : P → ℚ} {g : ℕ → ℚ} (hf : ∀ x ∈ X, f x = g (key x)) :
    (∑ x ∈ X, f x) = ∑ i ∈ Finset.range m, if ∃ x ∈ X, key x = i then g i else 0 := by
  classical
  calc
    (∑ x ∈ X, f x) = ∑ i ∈ X.image key, g i := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl hf
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hm x hx, ⟨x, hx, rfl⟩⟩
      · exact And.right

/-- The inclusive length of an interval, used as a rational-valued weight. -/
private def intervalLength (x : P) : ℚ := (right e x : ℚ) - left e x + 1

omit hrho in
private theorem sum_length_eq (A : PosetAntichain P) :
    (∑ x ∈ A.val, intervalLength e x) =
      ∑ i ∈ Finset.range (n + 1),
        if height e A i < height e A (i + 1) then (height e A (i + 1) : ℚ) - i else 0 := by
  classical
  have hkey (x : P) (hx : x ∈ A.val) :
      intervalLength e x = (height e A (left e x + 1) : ℚ) - left e x := by
    rw [height_of_mem e he A hx]
    simp only [intervalLength, Nat.cast_add, Nat.cast_one]
    ring
  rw [sum_by_key (left_injOn e he A)
    (g := fun i => (height e A (i + 1) : ℚ) - i) (m := n + 1)
    (fun x _ => ((left_le_right e x).trans_lt (right_lt_rank e x)).trans_le (Nat.le_succ n)) hkey]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [exists_left_mem_iff e he A]
  by_cases hstep : height e A i < height e A (i + 1)
  · by_cases hi : i < height e A (i + 1)
    · simp [hstep, hi]
    · have heq : height e A (i + 1) = i :=
        le_antisymm (Nat.le_of_not_gt hi) (by simpa using pred_le_height e A (i + 1))
      simp [heq]
  · simp [hstep]

omit he hrho in
private theorem height_zero : height e A 0 = 0 := by
  simp [height]

private theorem sum_rowmotion_length_sub_two_eq :
    (∑ x ∈ (rho A).val, (intervalLength e x - 2)) =
      ∑ i ∈ Finset.range (n + 1),
        if height e A i < height e A (i + 1) then (height e A i : ℚ) - i else 0 := by
  classical
  have hinj : Set.InjOn (fun x => left e x + 1) ((rho A).val : Set P) :=
    fun _ hx _ hy h => left_injOn e he (rho A) hx hy (Nat.add_right_cancel h)
  have hkey (x : P) (hx : x ∈ (rho A).val) :
      intervalLength e x - 2 = (height e A (left e x + 1) : ℚ) - (↑(left e x + 1) : ℚ) := by
    simp only [intervalLength, (mem_rowmotion_iff e he A hrho x).1 hx |>.1,
      Nat.cast_add, Nat.cast_one]
    ring
  rw [sum_by_key hinj
    (g := fun i => (height e A i : ℚ) - i) (m := n + 1)
    (fun x _ => Nat.succ_lt_succ ((left_le_right e x).trans_lt (right_lt_rank e x))) hkey]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [exists_left_succ_mem_rowmotion_iff e he A hrho i hin]
  cases i with
  | zero => simp [height_zero e A]
  | succ i => simp

/-- The two weighted sums are indexed by jumps of the same boundary. At each
jump their difference is the height increment. -/
private theorem length_step :
    (∑ x ∈ (rho A).val, intervalLength e x) - (∑ x ∈ A.val, intervalLength e x) =
      2 * ((rho A).val.card : ℚ) - n := by
  classical
  have hn : height e A (n + 1) = n := by
    exact le_antisymm (height_le_rank e A le_rfl)
      (by simpa using pred_le_height e A (n + 1))
  have hdiff :
      (∑ x ∈ A.val, intervalLength e x) -
        (∑ x ∈ (rho A).val, (intervalLength e x - 2)) = (n : ℚ) := by
    rw [sum_length_eq e he A, sum_rowmotion_length_sub_two_eq e he A hrho,
      ← Finset.sum_sub_distrib]
    calc
      _ = ∑ i ∈ Finset.range (n + 1), ((height e A (i + 1) : ℚ) - height e A i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hstep : height e A i < height e A (i + 1)
        · simp only [ite_eq_left hstep]
          ring
        · have heq : height e A (i + 1) = height e A i :=
            le_antisymm (Nat.le_of_not_gt hstep) (height_mono e A (Nat.le_succ _))
          simp [heq]
      _ = _ := by
        rw [Finset.sum_range_sub (fun i => (height e A i : ℚ)), hn, height_zero e A]
        simp
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hdiff
  linear_combination -hdiff

end IntervalCoordinates

/--
**Antichain size is homomesic under type-A rowmotion.** Let $n$ be a natural number and let $P$
be a finite partially ordered set that is a type-A root poset of rank $n$: there is a bijection
$a \mapsto (i_a, j_a)$ from $P$ onto the set of pairs $(i, j)$ of integers with $0 \le i \le j < n$
such that $a \le b$ holds exactly when $[i_a, j_a] \subseteq [i_b, j_b]$, that is, $i_b \le i_a$
and $j_a \le j_b$. Let $\rho$ be a bijection of the set of finite antichains of $P$ such that,
for every antichain $A$, $\rho(A)$ is the set of minimal elements of the complement of the
down-set of $A$. Then the set of finite antichains of $P$ is finite, $\rho$ is bijective, and for
every antichain $A$ and every $k > 0$ with $\rho^k(A) = A$,
$$\frac{1}{k} \sum_{i=0}^{k-1} |\rho^i(A)| = \frac{n}{2}.$$

This is the type-A case of Panyushev's conjecture on antichain orbits in root posets, which
Armstrong, Stump, and Thomas proved for all crystallographic root systems.

Source: D. Armstrong, C. Stump, and H. Thomas, A
uniform bijection between nonnesting and noncrossing partitions, Transactions of the American
Mathematical Society 365 (2013). Moved from
`OpenConjectures/Combinatorics/RootPosetRowmotionHomomesy`.
-/
public theorem conjecture_holds : conjecture := by
  classical
  intro n P _ _ rhoPrime f hP hrho hf
  obtain ⟨e, he⟩ := hP
  let _ := Fintype.ofFinite P
  refine ⟨inferInstanceAs (Finite {s : Finset P // IsAntichain (· ≤ ·) (s : Set P)}),
    hrho.1, ?_⟩
  intro A k hk hreturn
  let size (i : ℕ) := f (Nat.iterate rhoPrime i A)
  let length (i : ℕ) := ∑ x ∈ (Nat.iterate rhoPrime i A).val, intervalLength e x
  change (∑ i ∈ Finset.range k, size i) / (k : ℚ) = (n : ℚ) / 2
  have hstep (i : ℕ) : length (i + 1) - length i = 2 * size (i + 1) - n := by
    have hcard := hf (rhoPrime (Nat.iterate rhoPrime i A))
    simpa only [length, size, Function.iterate_succ_apply', hcard] using
      length_step e he (Nat.iterate rhoPrime i A) hrho
  have hsum : (∑ i ∈ Finset.range k, (2 * size (i + 1) - n)) = 0 := by
    simp_rw [← hstep]
    rw [Finset.sum_range_sub, show length k = length 0 by simp [length, hreturn], sub_self]
  have hshift : (∑ i ∈ Finset.range k, size (i + 1)) = ∑ i ∈ Finset.range k, size i := by
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub,
      show size k = size 0 by simp [size, hreturn], sub_self]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hshift] at hsum
  apply (div_eq_iff (by exact_mod_cast hk.ne')).2
  linear_combination hsum / 2

end MathlibExt.Combinatorics.RootPosetRowmotionHomomesyWanted
