/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Arndt compositions with fixed last part

A descending pair of parts has the unique form `(g + j + 2, j + 1)`. Removing the
minimum weight three leaves two parameters of weights one and two. We use this encoding
to enumerate the paired prefix before a fixed last part and then apply Binet's formula.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Arndt compositions by last part.** An Arndt composition of $n$ is a composition
$(\sigma_1, \ldots, \sigma_\ell)$ of $n$ into positive parts such that $\sigma_{2i-1} > \sigma_{2i}$
for every $i$ with $2i \le \ell$. For natural numbers $n$ and $j$, $b(n, j)$ is the number of
Arndt compositions of $n$, with any number of parts, whose last part is $j$. The empty
composition of $0$ counts as having last part $0$, so $b(0, 0) = 1$ and $b(0, j) = 0$ for
$j \ge 1$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 3 (definition of `b(n, m)` and Table 2). -/
def arndtLastPartCount (n j : ℕ) : ℕ :=
  if n = 0 then (if j = 0 then 1 else 0) else
    ∑ m ∈ Finset.range n,
      ((Finset.Nat.antidiagonalTuple (m + 1) n).filter fun c =>
        (∀ i, 0 < c i) ∧
          (∀ i i' : Fin (m + 1), (i : ℕ) % 2 = 0 → (i' : ℕ) = i + 1 → c i' < c i) ∧
            c (Fin.last m) = j).card

/-- **Arndt compositions of 6 by last part.** Let $b(n, j)$ be the number of Arndt compositions
of $n$ with last part $j$. Then $b(6, 1) = 4$, $b(6, 2) = 2$, $b(6, 3) = 1$ and $b(6, 6) = 1$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 3, Table 2. -/
theorem arndtLastPartCount_six :
    arndtLastPartCount 6 1 = 4 ∧ arndtLastPartCount 6 2 = 2 ∧ arndtLastPartCount 6 3 = 1 ∧
      arndtLastPartCount 6 6 = 1 := by
  decide +kernel

namespace arndtLastPartCount_isEquivalent

private abbrev Pairs := List (ℕ × ℕ)

private def weight : Pairs → ℕ
  | [] => 0
  | (g, j) :: ps => g + 2 * j + 3 + weight ps

-- A nonempty sequence of pairs with the initial weight three removed.
private abbrev State := (ℕ × ℕ) × Pairs

private def mass (s : State) := s.1.1 + 2 * s.1.2 + weight s.2

private def addOne : State ↪ State where
  toFun := fun ((g, j), ps) => ((g + 1, j), ps)
  inj' := by rintro ⟨⟨g, j⟩, ps⟩ ⟨⟨h, k⟩, qs⟩; simp

-- If the gap vanishes, increase both parts by one. Otherwise start a new minimum pair
-- and decrease the old gap by one. The first gap of the result is zero in both cases.
private def addTwo : State → State
  | ((0, j), ps) => ((0, j + 1), ps)
  | ((g + 1, j), ps) => ((0, 0), (g, j) :: ps)

private lemma addTwo_injective : Function.Injective addTwo := by
  rintro ⟨⟨_ | g, j⟩, ps⟩ ⟨⟨_ | h, k⟩, qs⟩ <;> simp [addTwo]

private lemma mass_addTwo (s : State) : mass (addTwo s) = mass s + 2 := by
  obtain ⟨⟨_ | g, j⟩, ps⟩ := s <;> simp [addTwo, mass, weight] <;> omega

-- Every positive-mass state with a positive first gap has a unique predecessor under addOne.
-- At mass at least two, every state with first gap zero has a unique predecessor under addTwo.
private def states : ℕ → Finset State
  | 0 => {((0, 0), [])}
  | 1 => {((1, 0), [])}
  | n + 2 => (states (n + 1)).map addOne ∪ (states n).map ⟨addTwo, addTwo_injective⟩

private lemma mem_states (n : ℕ) (s : State) : s ∈ states n ↔ mass s = n := by
  induction n using Nat.twoStepInduction generalizing s with
  | zero | one =>
    obtain ⟨⟨g, j⟩, ps⟩ := s
    cases ps with
    | nil => grind [mass, weight, states]
    | cons p ps => obtain ⟨h, k⟩ := p; simp +arith [mass, weight, states]
  | more n ih₀ ih₁ =>
    rw [states, Finset.mem_union]
    constructor
    · rintro (hs | hs)
      · obtain ⟨⟨⟨g, j⟩, ps⟩, h, rfl⟩ := Finset.mem_map.mp hs
        change g + 1 + 2 * j + weight ps = n + 2
        have := (ih₁ _).mp h
        dsimp [mass] at this
        omega
      · obtain ⟨t, h, rfl⟩ := Finset.mem_map.mp hs
        exact (mass_addTwo t).trans (by rw [(ih₀ _).mp h])
    · obtain ⟨⟨_ | g, j⟩, ps⟩ := s
      · cases j with
        | zero =>
          cases ps with
          | nil => simp [mass, weight]
          | cons p ps =>
            obtain ⟨g, j⟩ := p
            intro h
            right
            refine Finset.mem_map.mpr ⟨((g + 1, j), ps), (ih₀ _).mpr ?_, rfl⟩
            simp [mass, weight] at h ⊢
            omega
        | succ j =>
          intro h
          right
          refine Finset.mem_map.mpr ⟨((0, j), ps), (ih₀ _).mpr ?_, rfl⟩
          simp [mass] at h ⊢
          omega
      · intro h
        left
        refine Finset.mem_map.mpr ⟨((g, j), ps), (ih₁ _).mpr ?_, rfl⟩
        simp [mass] at h ⊢
        omega

private lemma card_states (n : ℕ) : (states n).card = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero | one => rfl
  | more n ih₀ ih₁ =>
    rw [states, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map, ih₀, ih₁,
      Nat.fib_add_two (n := n + 1), add_comm]
    rw [Finset.disjoint_left]
    intro s h₁ h₂
    obtain ⟨⟨⟨g, j⟩, ps⟩, _, rfl⟩ := Finset.mem_map.mp h₁
    obtain ⟨⟨⟨_ | h, k⟩, qs⟩, _, he⟩ := Finset.mem_map.mp h₂ <;>
      exact Nat.zero_ne_add_one _ (congrArg (fun s : State => s.1.1) he)

private def pairs : ℕ → Finset Pairs
  | 0 => {[]}
  | 1 | 2 => ∅
  | n + 3 => (states n).image fun s => s.1 :: s.2

private lemma mem_pairs (n : ℕ) (ps : Pairs) : ps ∈ pairs n ↔ weight ps = n := by
  match n, ps with
  | 0, [] | 1, [] | 2, [] | n + 3, [] => simp [pairs, weight]
  | 0, (g, j) :: ps | 1, (g, j) :: ps | 2, (g, j) :: ps => simp +arith [pairs, weight]
  | n + 3, (g, j) :: ps =>
    simp [pairs, Finset.mem_image, Prod.exists, mem_states, mass, weight]
    omega

private lemma card_pairs (n : ℕ) : (pairs (n + 3)).card = Nat.fib (n + 1) := by
  rw [pairs, Finset.card_image_of_injective, card_states]
  rintro ⟨p, ps⟩ ⟨q, qs⟩
  simp

-- An unpaired excess in the penultimate part, together with a prefix of complete pairs.
private def excess : ℕ → Finset (ℕ × Pairs)
  | 0 => {(0, [])}
  | n + 1 =>
    ((excess n).image fun p => (p.1 + 1, p.2)) ∪
      (pairs (n + 1)).image fun ps => (0, ps)

private lemma mem_excess (n k : ℕ) (ps : Pairs) :
    (k, ps) ∈ excess n ↔ k + weight ps = n := by
  induction n generalizing k ps with
  | zero =>
    cases ps with
    | nil => simp [excess, weight]
    | cons p ps => obtain ⟨g, j⟩ := p; simp [excess, weight]
  | succ n ih =>
    cases k <;> simp [excess, Finset.mem_image, Prod.exists, ih, mem_pairs]
    omega

private lemma card_excess (n : ℕ) : (excess (n + 1)).card = Nat.fib (n + 1) := by
  have step (i : ℕ) : (excess (i + 1)).card = (excess i).card + (pairs (i + 1)).card := by
    rw [excess, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
      Finset.card_image_of_injective]
    · exact fun _ _ h => congrArg Prod.snd h
    · rintro ⟨k, ps⟩ ⟨l, qs⟩
      simp
    · simp [Finset.disjoint_left, Finset.mem_image, Prod.exists]
      grind
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [step, ih]
    cases n with
    | zero => rfl
    | succ n => rw [card_pairs, Nat.fib_add_two (n := n + 1), add_comm]

-- The terminal block is either the singleton m or the pair (m + k + 1, m).
private def unpack (m : ℕ) : Pairs → Option ℕ → List ℕ
  | [], none => [m]
  | [], some k => [m + k + 1, m]
  | (g, j) :: ps, e => (g + j + 2) :: (j + 1) :: unpack m ps e

private lemma unpack_ne_nil (m : ℕ) (ps : Pairs) (e : Option ℕ) :
    unpack m ps e ≠ [] := by cases ps <;> cases e <;> simp [unpack]

private lemma unpack_inj (m : ℕ) (ps qs : Pairs) (e f : Option ℕ)
    (h : unpack m ps e = unpack m qs f) : ps = qs ∧ e = f := by
  induction ps generalizing qs with
  | nil =>
    cases qs <;> cases e <;> cases f <;> simp_all [unpack, unpack_ne_nil, eq_comm (a := [])]
  | cons p ps ih =>
    obtain ⟨g, j⟩ := p
    cases qs with
    | nil => cases f <;> simp [unpack, unpack_ne_nil] at h
    | cons q qs =>
      obtain ⟨g', j'⟩ := q
      simp only [unpack, List.cons.injEq, Nat.add_right_cancel_iff] at h
      obtain ⟨h₁, rfl, h₂⟩ := h
      obtain rfl : g = g' := by omega
      obtain ⟨rfl, rfl⟩ := ih qs h₂
      exact ⟨rfl, rfl⟩

private lemma sum_unpack (m : ℕ) (ps : Pairs) (e : Option ℕ) :
    (unpack m ps e).sum = weight ps + (match e with | none => m | some k => 2 * m + 1 + k) := by
  induction ps with
  | nil => cases e <;> simp [unpack, weight]; omega
  | cons p ps ih => obtain ⟨g, j⟩ := p; simp [unpack, weight, ih]; omega

private def descending : List ℕ → Prop
  | a :: b :: xs => b < a ∧ descending xs
  | _ => True

private def valid (m : ℕ) (xs : List ℕ) : Prop :=
  (∀ x ∈ xs, 0 < x) ∧ descending xs ∧ xs.getLast? = some m

private lemma valid_unpack {m : ℕ} (hm : 0 < m) (ps : Pairs) (e : Option ℕ) :
    valid m (unpack m ps e) := by
  induction ps with
  | nil => cases e <;> simp [valid, unpack, descending, hm]
  | cons p ps ih =>
    obtain ⟨g, j⟩ := p
    obtain ⟨hp, hd, hl⟩ := ih
    simpa [valid, unpack, descending, hd, List.getLast?_cons, hl] using hp

private lemma exists_unpack {m : ℕ} (xs : List ℕ) (h : valid m xs) :
    ∃ ps e, unpack m ps e = xs := by
  match xs with
  | [] => simp [valid] at h
  | [a] =>
    obtain rfl : a = m := by simpa [valid] using h.2.2
    exact ⟨[], none, rfl⟩
  | [a, b] =>
    have hb : b = m := by simpa using h.2.2
    subst b
    have hlt : m < a := h.2.1.1
    exact ⟨[], some (a - m - 1), by simp [unpack]; omega⟩
  | a :: b :: c :: cs =>
    have hb : 0 < b := h.1 _ (by simp)
    have hab : b < a := h.2.1.1
    obtain ⟨ps, e, he⟩ := exists_unpack (c :: cs)
      ⟨fun x hx => h.1 x (by simp [hx]), h.2.1.2, by simpa using h.2.2⟩
    exact ⟨(a - b - 1, b - 1) :: ps, e, by simp [unpack, he]; omega⟩

private lemma descending_ofFn {k : ℕ} (f : Fin k → ℕ) :
    descending (List.ofFn f) ↔
      ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → f j < f i := by
  induction k using Nat.twoStepInduction with
  | zero => simp [descending]
  | one => simp [List.ofFn_succ, descending]
  | more k ih₀ _ =>
    rw [List.ofFn_succ, List.ofFn_succ, descending, ih₀]
    simp [Fin.forall_fin_succ, Fin.val_succ, Nat.add_assoc]

private lemma valid_ofFn (m k : ℕ) (f : Fin (k + 1) → ℕ) :
    valid m (List.ofFn f) ↔ (∀ i, 0 < f i) ∧
      (∀ i j : Fin (k + 1), (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → f j < f i) ∧
        f (Fin.last k) = m := by
  rw [valid, descending_ofFn, List.getLast?_eq_getLast_of_ne_nil (by simp),
    List.getLast_ofFn_succ]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, Option.some.injEq]

private abbrev Ending := Pairs ⊕ (ℕ × Pairs)

private def parts (m : ℕ) : Ending → List ℕ
  | .inl ps => unpack m ps none
  | .inr (k, ps) => unpack m ps (some k)

private lemma parts_injective (m : ℕ) : Function.Injective (parts m) := by
  rintro (ps | ⟨k, ps⟩) (qs | ⟨l, qs⟩) h <;> obtain ⟨h₁, h₂⟩ := unpack_inj m _ _ _ _ h <;>
    simp_all

-- An odd-length composition ends in [m]. An even-length composition ends in [m + k + 1, m].
-- In both cases the remaining parts form a sequence of complete descending pairs.
private def endings (n m : ℕ) : Finset Ending :=
  (pairs (n - m)).disjSum (if 2 * m + 1 ≤ n then excess (n - 2 * m - 1) else ∅)

private lemma mem_endings {n m : ℕ} (hm : 0 < m) (hn : m ≤ n) (e : Ending) :
    e ∈ endings n m ↔ (parts m e).sum = n ∧ valid m (parts m e) := by
  cases e with
  | inl ps =>
    simp [endings, parts, mem_pairs, sum_unpack, valid_unpack hm]
    omega
  | inr p =>
    obtain ⟨k, ps⟩ := p
    by_cases h : 2 * m + 1 ≤ n <;>
      simp [endings, h, parts, mem_excess, sum_unpack, valid_unpack hm] <;> omega

private lemma count_eq_card {n m : ℕ} (hm : 0 < m) (hn : m ≤ n) :
    arndtLastPartCount n m = (endings n m).card := by
  let index := fun e : Ending => (parts m e).length - 1
  have bounded : (endings n m : Set Ending).MapsTo index (Finset.range n) := by
    intro e he
    obtain ⟨hs, hv⟩ := (mem_endings hm hn e).mp he
    have hlen := List.length_le_sum_of_one_le _ hv.1
    apply Finset.mem_range.mpr
    change (parts m e).length - 1 < n
    omega
  have hn₀ : n ≠ 0 := by omega
  simp only [arndtLastPartCount, hn₀, ↓reduceIte, Finset.card_eq_sum_card_fiberwise bounded]
  refine Finset.sum_congr rfl fun k _ => Eq.symm ?_
  let fiber := (endings n m).filter (index · = k)
  have length_eq (e) (he : e ∈ fiber) : (parts m e).length = k + 1 := by
    have hk := (Finset.mem_filter.mp he).2
    have hne : parts m e ≠ [] := by cases e <;> exact unpack_ne_nil _ _ _
    have := List.length_pos_iff.mpr hne
    dsimp [index] at hk
    omega
  let tuple (e) (he : e ∈ fiber) (i : Fin (k + 1)) :=
    (parts m e)[i.val]'(by rw [length_eq e he]; exact i.isLt)
  have ofFn_tuple (e) (he : e ∈ fiber) : List.ofFn (tuple e he) = parts m e := by
    apply List.ext_getElem
    · rw [List.length_ofFn, length_eq e he]
    · intro i h₁ h₂
      rw [List.getElem_ofFn]
  apply Finset.card_bij tuple
  · intro e he
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, ← List.sum_ofFn, ← valid_ofFn,
      ofFn_tuple e he]
    exact (mem_endings hm hn _).mp (Finset.mem_filter.mp he).1
  · intro e he f hf h
    apply parts_injective m
    rw [← ofFn_tuple e he, ← ofFn_tuple f hf, h]
  · intro f hf
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, ← List.sum_ofFn, ← valid_ofFn] at hf
    obtain ⟨ps, e, h⟩ := exists_unpack _ hf.2
    obtain ⟨c, hc⟩ : ∃ c : Ending, parts m c = List.ofFn f := by
      cases e with
      | none => exact ⟨.inl ps, h⟩
      | some k => exact ⟨.inr (k, ps), h⟩
    have hmem : c ∈ fiber := Finset.mem_filter.mpr
      ⟨(mem_endings hm hn _).mpr (hc ▸ hf), by simp [index, hc]⟩
    exact ⟨c, hmem, List.ofFn_injective ((ofFn_tuple c hmem).trans hc)⟩

end arndtLastPartCount_isEquivalent

open arndtLastPartCount_isEquivalent in
/-- Let $n,m$ be natural numbers with $0 < m \le n$. The number $b(n,m)$ of Arndt compositions
of $n$ with last part $m$ is the sum of the contributions from a terminal singleton and a
terminal descending pair, respectively.

$$
b(n,m) =
\begin{cases} 1 & n=m, \\ F_{n-m-2} & \text{otherwise} \end{cases}
+
\begin{cases} 1 & n=2m+1, \\ F_{n-2m-1} & \text{otherwise} \end{cases}.
$$

Here $F_j$ is the Fibonacci number with $F_0=0$ and $F_1=1$, and subtraction in its index
is truncated at zero. At each terminal block's minimum weight, only the empty prefix occurs. -/
theorem arndtLastPart_atMost_atLeast.count_by_terminal_block {n m : ℕ}
    (hm : 0 < m) (hn : m ≤ n) :
    arndtLastPartCount n m =
      (if n = m then 1 else Nat.fib (n - m - 2)) +
        (if n = 2 * m + 1 then 1 else Nat.fib (n - 2 * m - 1)) := by
  rw [count_eq_card hm hn, endings, Finset.card_disjSum]
  congr 1
  · generalize hd : n - m = d
    match d with
    | 0 => simp [pairs, show n = m by omega]
    | 1 | 2 => simp [pairs, show n ≠ m by omega]
    | d + 3 => simp [card_pairs, show n ≠ m by omega]
  · by_cases h : 2 * m + 1 ≤ n
    · simp only [h, ↓reduceIte]
      generalize hd : n - 2 * m - 1 = d
      cases d with
      | zero => simp [excess, show n = 2 * m + 1 by omega]
      | succ d => simp [card_excess, show n ≠ 2 * m + 1 by omega]
    · simp [h, show n ≠ 2 * m + 1 by omega, show n - 2 * m - 1 = 0 by omega]

namespace arndtLastPartCount_isEquivalent

private lemma count_large {n m : ℕ} (hm : 0 < m) (hn : 2 * m + 3 ≤ n) :
    arndtLastPartCount n m = Nat.fib (n - (m + 2)) + Nat.fib (n - (2 * m + 1)) := by
  simp [arndtLastPart_atMost_atLeast.count_by_terminal_block hm (show m ≤ n by omega),
    show n ≠ m by omega, show n ≠ 2 * m + 1 by omega, Nat.sub_sub]

open Filter Asymptotics
open scoped Topology goldenRatio

private lemma fib_equivalent :
    (fun n : ℕ => (Nat.fib n : ℝ)) ~[atTop] (fun n : ℕ => φ ^ n / Real.sqrt 5) := by
  have hφ := Real.goldenRatio_pos
  have h₅ : 0 < Real.sqrt 5 := by positivity
  have h : |ψ / φ| < 1 := by
    rw [abs_div, abs_of_neg Real.goldenConj_neg, abs_of_pos hφ, div_lt_one hφ]
    linarith [Real.neg_one_lt_goldenConj, Real.one_lt_goldenRatio]
  apply (isEquivalent_iff_tendsto_one (.of_forall fun n =>
    div_ne_zero (pow_ne_zero n hφ.ne') h₅.ne')).2
  have ht := tendsto_const_nhds (x := (1 : ℝ)) |>.sub (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h)
  rw [sub_zero] at ht
  apply ht.congr
  intro n
  simp only [Pi.div_apply, Real.coe_fib_eq, div_pow]
  field_simp

end arndtLastPartCount_isEquivalent

open Filter Asymptotics
open scoped goldenRatio
open arndtLastPartCount_isEquivalent

/-- **Asymptotics of Arndt compositions with a fixed last part.** Let $b(n, m)$ be the number of
Arndt compositions of $n$ with last part $m$, and let $\varphi$ be the golden ratio. For every
fixed integer $m \ge 1$,
$b(n, m) \sim \frac{\varphi^{n-m-2}}{\sqrt{5}} \left(1 + \frac{1}{\varphi^{m-1}}\right)$ as
$n \to \infty$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 10 (`integers-2024-A35-thm-10`). -/
theorem arndtLastPartCount_isEquivalent (m : ℕ) (hm : 0 < m) :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (arndtLastPartCount n m : ℝ))
      (fun n : ℕ => Real.goldenRatio ^ ((n : ℤ) - m - 2) / Real.sqrt 5 *
        (1 + 1 / Real.goldenRatio ^ ((m : ℤ) - 1))) := by
  have hφ := Real.goldenRatio_pos
  have shifted (k : ℕ) := fib_equivalent.comp_tendsto (tendsto_sub_atTop_nat k)
  have h := IsEquivalent.add_add_of_nonneg (fun n => by dsimp; positivity)
    (fun n => by dsimp; positivity) (shifted (m + 2)) (shifted (2 * m + 1))
  apply h.congr_left (by
    filter_upwards [eventually_ge_atTop (2 * m + 3)] with n hn
    simp [count_large hm hn]) |>.congr_right
  filter_upwards [eventually_ge_atTop (2 * m + 3)] with n hn
  change φ ^ (n - (m + 2)) / Real.sqrt 5 + φ ^ (n - (2 * m + 1)) / Real.sqrt 5 = _
  have h₁ : (n : ℤ) - m - 2 = (n - (m + 2) : ℕ) := by omega
  have h₂ : ((n - (2 * m + 1) : ℕ) : ℤ) = (n - (m + 2) : ℕ) - ((m : ℤ) - 1) := by omega
  rw [h₁, ← zpow_natCast φ (n - (2 * m + 1)), h₂, zpow_sub₀ hφ.ne', zpow_natCast]
  ring

end

end MetaMathlibExt
