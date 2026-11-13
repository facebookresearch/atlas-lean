/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Parallel.PrefixSum

/-!
# Work-efficient parallel prefix sums (Blelloch's scan)

Blelloch's scan (Blelloch, *Prefix sums and their applications*, CMU-CS-90-190, 1990; JáJá,
*An Introduction to Parallel Algorithms*, Chapter 2) computes the exclusive prefix products
`x 0 * ⋯ * x (j - 1)` of `n = 2 ^ k` values in an associative monoid with `O(n)` work and
`O(log n)` span, against the `O(n log n)` work of the Kogge-Stone scan (`PrefixSum.lean`): combine
adjacent pairs, scan the `n / 2` pair products recursively, and fill in the odd positions
(`blelloch`). The order of the factors is kept, so the monoid need not be commutative.

Main results:

* `blelloch_eq_seg`: **position `j < 2 ^ k` holds the exclusive prefix product** `seg x 0 j`
  (via `seg_pairUp`: prefix products of the pair products are the even prefix products).
* `blellochListT_work_eq`: on inputs of length `2 ^ k`, the instrumented list scan performs
  `2 ^ (k + 1) - 2` multiplications, fewer than `2 n`.
* `blellochListT_rounds_eq`: on inputs of length `2 ^ k`, it schedules `2 * k` rounds.
* `ret_blellochListT`: erasing the instrumentation gives `blellochList` on every input.
* `blellochList` (`pairList`, `expand`): the scan on lists in `O(n)` time, proved equal
  (`getD_blellochList`, `getD_blellochList_eq_seg`).

## Cost model

`blellochListT` uses upstream `TimeM (ℕ × ℕ)`, with one work tick per monoid multiplication
and one round tick per scheduled pair or expansion phase. Traversal, allocation, copying, and
recursive calls are free. Work includes multiplication by the identity. Each phase's products
are independent, although the list evaluator traverses them sequentially. The compatibility name
`blellochSpan` counts scheduled rounds, not a task DAG's longest path. The exact work recurrence
requires the input length to be `2 ^ k`; erasure holds for arbitrary lists. `blelloch` is the
recursion used for the proofs; evaluated directly it recomputes the pair products (sequential
cost quadratic in `n`); `blellochList` is the linear-time implementation.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Parallel.PrefixSum

variable {M : Type*} [Monoid M]

/-- Adjacent pairs combined: position `i` holds `x (2 i) * x (2 i + 1)`. -/
def pairUp (x : ℕ → M) : ℕ → M := fun i => x (2 * i) * x (2 * i + 1)

/-- Blelloch's scan on `2 ^ k` positions, as a recursion: scan the pair products, then position
`2 i` takes the `i`-th result and position `2 i + 1` multiplies it by `x (2 i)`. -/
def blelloch : ℕ → (ℕ → M) → ℕ → M
  | 0, _ => fun _ => 1
  | k + 1, x => fun j =>
      if j % 2 = 0 then blelloch k (pairUp x) (j / 2) else blelloch k (pairUp x) (j / 2) * x (j - 1)

theorem seg_succ (x : ℕ → M) (j : ℕ) : seg x 0 (j + 1) = seg x 0 j * x j := by
  rw [← seg_mul_seg x (Nat.zero_le j) (Nat.le_succ j)]
  simp [seg]

theorem seg_pairUp (x : ℕ → M) : ∀ i, seg (pairUp x) 0 i = seg x 0 (2 * i)
  | 0 => by simp [seg]
  | i + 1 => by
      rw [seg_succ, seg_pairUp x i, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, seg_succ, seg_succ,
        pairUp, mul_assoc]

/-- **Blelloch's scan computes the exclusive prefix products**: position `j < 2 ^ k` holds
`x 0 * ⋯ * x (j - 1)`. -/
theorem blelloch_eq_seg : ∀ (k : ℕ) (x : ℕ → M) (j : ℕ), j < 2 ^ k → blelloch k x j = seg x 0 j
  | 0, x, j, hj => by
      have : j = 0 := by simpa using hj
      subst this; simp [blelloch, seg]
  | k + 1, x, j, hj => by
      have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      simp only [blelloch]
      rw [blelloch_eq_seg k (pairUp x) (j / 2) (by omega), seg_pairUp]
      split_ifs with h
      · congr 1; omega
      · rw [show j = 2 * (j / 2) + 1 by omega, seg_succ]
        congr 2
        omega

/-! ## Work and scheduled rounds -/

/-- The combinations Blelloch's scan performs on `2 ^ k` positions: `2 ^ (k - 1)` pair products,
the recursive scan, and `2 ^ (k - 1)` products for the odd positions. -/
def blellochWork : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ k + blellochWork k + 2 ^ k

/-- The scheduled rounds: one pair round, the recursive scan, then one expansion round.
This counts idle rounds too and is not a task DAG longest-path calculation. -/
def blellochSpan : ℕ → ℕ
  | 0 => 0
  | k + 1 => blellochSpan k + 2

/-- The work recurrence plus two is `2 ^ (k + 1)`. It counts `blellochListT` multiplications
on lists of length `2 ^ k` by `time_blellochListT`. -/
theorem blellochWork_eq : ∀ k, blellochWork k + 2 = 2 ^ (k + 1)
  | 0 => rfl
  | k + 1 => by
      have := blellochWork_eq k
      simp only [blellochWork, Nat.pow_succ] at *
      omega

/-- The scheduled round recurrence is `2 * k`. -/
theorem blellochSpan_eq : ∀ k, blellochSpan k = 2 * k
  | 0 => rfl
  | k + 1 => by rw [blellochSpan, blellochSpan_eq k]; omega

/-! ## The scan on lists -/

/-- Adjacent pairs of a list combined. -/
def pairList : List M → List M
  | a :: b :: xs => (a * b) :: pairList xs
  | _ => []

/-- Interleave the scanned pair products `zs` with the inputs `xs`: `z, z * x₀, z', z' * x₂, …`. -/
def expand : List M → List M → List M
  | z :: zs, a :: _ :: xs => z :: (z * a) :: expand zs xs
  | _, _ => []

/-- Blelloch's scan of a list of length `2 ^ k`, in `O(2 ^ k)` time. -/
def blellochList : ℕ → List M → List M
  | 0, _ => [1]
  | k + 1, xs => expand (blellochList k (pairList xs)) xs

theorem length_pairList : ∀ xs : List M, (pairList xs).length = xs.length / 2
  | [] => by simp [pairList]
  | [_] => by simp [pairList]
  | a :: b :: xs => by
      simp only [pairList, List.length_cons, length_pairList xs]
      omega

theorem getD_pairList : ∀ (xs : List M) (i : ℕ), 2 * i + 1 < xs.length →
    (pairList xs).getD i 1 = xs.getD (2 * i) 1 * xs.getD (2 * i + 1) 1
  | [], _, h => absurd h (by simp)
  | [_], _, h => absurd h (by simp)
  | a :: b :: xs, 0, _ => by simp [pairList]
  | a :: b :: xs, i + 1, h => by
      simp only [pairList, List.getD_cons_succ, List.length_cons] at h ⊢
      rw [getD_pairList xs i (by omega)]
      congr 1

theorem length_expand : ∀ (zs xs : List M), xs.length = 2 * zs.length →
    (expand zs xs).length = 2 * zs.length
  | [], _, _ => by simp [expand]
  | _ :: _, [], h => by simp at h
  | _ :: _, [_], h => by simp at h; omega
  | z :: zs, a :: b :: xs, h => by
      simp only [expand, List.length_cons] at h ⊢
      rw [length_expand zs xs (by omega)]
      omega

theorem getD_expand : ∀ (zs xs : List M), xs.length = 2 * zs.length → ∀ j, j < 2 * zs.length →
    (expand zs xs).getD j 1 =
      if j % 2 = 0 then zs.getD (j / 2) 1 else zs.getD (j / 2) 1 * xs.getD (j - 1) 1
  | [], _, _, j, hj => absurd hj (by simp)
  | _ :: _, [], h, _, _ => by simp at h
  | _ :: _, [_], h, _, _ => by simp at h; omega
  | z :: zs, a :: b :: xs, h, j, hj => by
      simp only [List.length_cons] at h hj
      match j with
      | 0 => simp [expand]
      | 1 => simp [expand]
      | j + 2 =>
          simp only [expand, List.getD_cons_succ]
          rw [getD_expand zs xs (by omega) j (by omega)]
          have e1 : (j + 2) % 2 = j % 2 := by omega
          have e2 : (j + 2) / 2 = j / 2 + 1 := by omega
          rw [e1, e2, List.getD_cons_succ]
          split_ifs with hj2
          · rfl
          · rw [show j + 2 - 1 = (j - 1) + 2 by omega, List.getD_cons_succ, List.getD_cons_succ]

theorem length_blellochList : ∀ (k : ℕ) (xs : List M), xs.length = 2 ^ k →
    (blellochList k xs).length = 2 ^ k
  | 0, _, _ => rfl
  | k + 1, xs, h => by
      have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      have hp : (pairList xs).length = 2 ^ k := by rw [length_pairList]; omega
      rw [blellochList, length_expand _ _ (by rw [length_blellochList k _ hp]; omega),
        length_blellochList k _ hp, hk]

/-- **The list implementation computes Blelloch's scan.** -/
theorem getD_blellochList : ∀ (k : ℕ) (xs : List M), xs.length = 2 ^ k → ∀ j, j < 2 ^ k →
    (blellochList k xs).getD j 1 = blelloch k (fun i => xs.getD i 1) j
  | 0, _, _, j, hj => by
      have : j = 0 := by simpa using hj
      subst this; rfl
  | k + 1, xs, h, j, hj => by
      have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      have hp : (pairList xs).length = 2 ^ k := by rw [length_pairList]; omega
      have hz := length_blellochList k _ hp
      rw [blellochList, getD_expand _ _ (by omega) j (by omega), blelloch]
      have hrec : ∀ i, i < 2 ^ k → (blellochList k (pairList xs)).getD i 1 =
          blelloch k (pairUp fun i => xs.getD i 1) i := by
        intro i hi
        rw [getD_blellochList k _ hp i hi]
        congr 1
        funext i'
        by_cases hi' : 2 * i' + 1 < xs.length
        · rw [getD_pairList xs i' hi', pairUp]
        · rw [List.getD_eq_default _ _ (by omega), pairUp,
            List.getD_eq_default _ _ (by omega), one_mul]
          by_cases h2 : 2 * i' < xs.length
          · omega
          · rw [List.getD_eq_default _ _ (by omega)]
      simp only [hrec (j / 2) (by omega)]

/-- **The list implementation computes the exclusive prefix products.** -/
theorem getD_blellochList_eq_seg (k : ℕ) (xs : List M) (h : xs.length = 2 ^ k) (j : ℕ)
    (hj : j < 2 ^ k) : (blellochList k xs).getD j 1 = seg (fun i => xs.getD i 1) 0 j := by
  rw [getD_blellochList k xs h j hj, blelloch_eq_seg k _ j hj]

/-! ## Instrumented work and scheduled rounds -/

/-- Combine adjacent pairs, charging one work tick per multiplication and no rounds.
An unmatched final element is discarded, as in `pairList`. -/
def pairListT : List M → TimeM (ℕ × ℕ) (List M)
  | a :: b :: xs => do
      TimeM.tick (1, 0)
      let ys ← pairListT xs
      pure ((a * b) :: ys)
  | _ => pure []

/-- Erasing adjacent-pair instrumentation gives the original pair products. -/
@[simp] theorem ret_pairListT : ∀ xs : List M, (pairListT xs).ret = pairList xs
  | [] => rfl
  | [_] => rfl
  | a :: b :: xs => by simp [pairListT, ret_pairListT xs, pairList]

/-- The pair phase performs one multiplication per complete input pair. -/
@[simp] theorem time_pairListT : ∀ xs : List M,
    (pairListT xs).time = (xs.length / 2, 0)
  | [] => by
      change (0, 0) = ((0 : ℕ) / 2, 0)
      decide
  | [_] => by
      change (0, 0) = ((1 : ℕ) / 2, 0)
      decide
  | a :: b :: xs => by
      simp [pairListT, time_pairListT xs]
      omega

/-- Interleave the scanned pairs and odd-position products, charging each multiplication.
The cost counts work only; the caller records the scheduled round. -/
def expandT : List M → List M → TimeM (ℕ × ℕ) (List M)
  | z :: zs, a :: _ :: xs => do
      TimeM.tick (1, 0)
      let ys ← expandT zs xs
      pure (z :: (z * a) :: ys)
  | _, _ => pure []

/-- Erasing expansion instrumentation gives the original interleaving on all inputs. -/
@[simp] theorem ret_expandT : ∀ zs xs : List M, (expandT zs xs).ret = expand zs xs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: _, [_] => rfl
  | z :: zs, a :: b :: xs => by simp [expandT, ret_expandT zs xs, expand]

/-- Expansion charges one multiplication per scanned pair with a complete input pair. -/
@[simp] theorem time_expandT : ∀ zs xs : List M,
    (expandT zs xs).time = (min zs.length (xs.length / 2), 0)
  | [], _ => rfl
  | _ :: zs, [] => by
      change (0, 0) = (min (zs.length + 1) ((0 : ℕ) / 2), 0)
      rw [show (0 : ℕ) / 2 = 0 from by decide, Nat.min_zero]
  | _ :: zs, [_] => by
      change (0, 0) = (min (zs.length + 1) ((1 : ℕ) / 2), 0)
      rw [show (1 : ℕ) / 2 = 0 from by decide, Nat.min_zero]
  | z :: zs, a :: b :: xs => by
      simp [expandT, time_expandT zs xs]
      omega

/-- The tabulated Blelloch scan instrumented with multiplication work and scheduled rounds.
Each recursive level schedules one pair round and one expansion round, even if idle. -/
def blellochListT : ℕ → List M → TimeM (ℕ × ℕ) (List M)
  | 0, _ => pure [1]
  | k + 1, xs => do
      TimeM.tick (0, 1)
      let ps ← pairListT xs
      let zs ← blellochListT k ps
      TimeM.tick (0, 1)
      expandT zs xs

/-- Erasing the instrumentation preserves Blelloch's list result on every input. -/
@[simp] theorem ret_blellochListT : ∀ (k : ℕ) (xs : List M),
    (blellochListT k xs).ret = blellochList k xs
  | 0, _ => rfl
  | k + 1, xs => by
      simp [blellochListT, ret_blellochListT k (pairList xs), blellochList]

/-- On a list of length `2 ^ k`, timed Blelloch work equals `blellochWork` and its
scheduled round count equals `blellochSpan`. -/
@[simp] theorem time_blellochListT : ∀ (k : ℕ) (xs : List M), xs.length = 2 ^ k →
    (blellochListT k xs).time = (blellochWork k, blellochSpan k)
  | 0, _, _ => rfl
  | k + 1, xs, h => by
      have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      have hs : xs.length / 2 = 2 ^ k := by omega
      have hp : (pairList xs).length = 2 ^ k := by rw [length_pairList, hs]
      have hz := length_blellochList k (pairList xs) hp
      simp [blellochListT, time_blellochListT k (pairList xs) hp, hs, hz,
        blellochWork, blellochSpan]
      omega

/-- On `2 ^ k` inputs the instrumented scan performs exactly `2 ^ (k + 1) - 2`
multiplications. -/
theorem blellochListT_work_eq (k : ℕ) (xs : List M) (h : xs.length = 2 ^ k) :
    (blellochListT k xs).time.1 = 2 ^ (k + 1) - 2 := by
  rw [time_blellochListT k xs h]
  have := blellochWork_eq k
  change blellochWork k = 2 ^ (k + 1) - 2
  omega

/-- On `2 ^ k` inputs the instrumented scan schedules exactly `2 * k` parallel rounds. -/
theorem blellochListT_rounds_eq (k : ℕ) (xs : List M) (h : xs.length = 2 ^ k) :
    (blellochListT k xs).time.2 = 2 * k := by
  rw [time_blellochListT k xs h]
  exact blellochSpan_eq k

end Cslib.Algorithms.Lean.Parallel.PrefixSum
