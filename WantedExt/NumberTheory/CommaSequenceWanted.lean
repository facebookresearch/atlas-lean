/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Logic.Relation
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.NumberTheory.CommaSequence

namespace MetaMathlibExt

@[expose] public section

/-- Comma sequences with arbitrary positive initial values terminate in every
base from 3 through 633 inclusive.

This is statement `commaSequence_terminates_of_base_le_633` from lines 134–137 of
Dougherty, *Comma Sequences*, JIS 28, with the sequence semantics defined in
`MathlibExt.NumberTheory.CommaSequence`. -/
public theorem_wanted commaSequence_terminates_of_base_le_633
    (b v : ℕ) (hb1 : 3 ≤ b) (hb2 : b ≤ 633) (hv : 0 < v) :
    IsCommaTerminating b v

/-- The set `U(b, d)` of minimal `u`'s: `u = (r, s)_b = r b + s` with digits `r, s < b`,
`0 < s` and `r + s < b`, or `r + s = b` and `s < d`; for `d = 1` the condition is
`r + s ≤ b`, `0 < s`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5, Lemma 6 (c), (d). -/
public def commaDangerFinalSet (b d : ℕ) : Finset ℕ :=
  ((Finset.range b ×ˢ Finset.range b).filter fun p =>
      if d = 1 then p.1 + p.2 ≤ b ∧ 0 < p.2
      else (p.1 + p.2 < b ∧ 0 < p.2) ∨ (p.1 + p.2 = b ∧ p.2 < d)).image
    fun p => p.1 * b + p.2

/-- Characteristic values: `U(3, 1) = {1, 2, 4, 5, 7}` and `U(3, 2) = {1, 2, 4, 7}`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5, the example after Lemma 6. -/
public theorem commaDangerFinalSet_three :
    commaDangerFinalSet 3 1 = {1, 2, 4, 5, 7} ∧ commaDangerFinalSet 3 2 = {1, 2, 4, 7} := by
  decide

/-- The sum `∑ S_b(d, u)` of the arithmetic-progression cycle
`S_b(d, u) = ⟨((m d - u) mod b) b + d : 0 ≤ m < b / gcd(b, d)⟩` of comma differences.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5, display (3). -/
public def commaCycleSum (b d u : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (b / Nat.gcd b d), (((((m * d : ℕ) : ℤ) - u) % b).toNat * b + d)

/-- Characteristic value: in base `10` from `997 = 1 · 10³ - 3` the differences cycle through
`71, 81, 91, 1, 11, …, 61`, with sum `460`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5, Section 3.1 and display (3). -/
public theorem commaCycleSum_ten_one_three : commaCycleSum 10 1 3 = 460 := by
  decide

/-- The comma map `(d, u, k) → (d', u', k')` as a relation: starting from `d b^k - u`, the comma
sequence reaches `d' b^{k'} - u'`, the final value of the next danger interval
`[d' b^{k'} - b², d' b^{k'})` (final: terminal, or its successor is at least `d' b^{k'}`), where
`(d', k') = (d + 1, k)` if `d < b - 1` and `(1, k + 1)` otherwise.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5, Section 3.3. -/
public def commaIntervalStep (b d u k u' : ℕ) : Prop :=
  let top := if d < b - 1 then (d + 1) * b ^ k else b ^ (k + 1)
  0 < u' ∧ u' ≤ b ^ 2 ∧ Relation.ReflTransGen (IsCommaSucc b) (d * b ^ k - u) (top - u') ∧
    (IsCommaTerminal b (top - u') ∨ ∀ m, IsCommaSucc b (top - u') m → top ≤ m)

/-- Characteristic property: a comma-map image `u'` satisfies `0 < u' ≤ b²`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5, Section 3.3. -/
public theorem commaIntervalStep_bounds {b d u k u' : ℕ} (h : commaIntervalStep b d u k u') :
    0 < u' ∧ u' ≤ b ^ 2 :=
  ⟨h.1, h.2.1⟩

/-- The edge relation of the finite digraph `G_b'`. Vertices are `(d, u, κ)` with `1 ≤ d < b`,
`u ∈ U(b, d)` and `κ < L(b)`, where `L(b)` is the lcm, over `1 ≤ d < b` and
`u ∈ U(b, d) ∪ {0}`, of the eventual period `l(d, u)` of `k ↦ b^k mod ∑ S_b(d, u)`; there is an
edge `(d, u, κ) → (d', u', κ')` when `d'` and `κ'` are the next digit and residue and
`(d, u, k) → (d', u', k')` is a comma-map step for all sufficiently large `k ≡ κ (mod L(b))`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
display (5) and the definition of `G_b'` in Section 3.4. -/
public def commaReducedGraphEdge (b : ℕ) (v w : ℕ × ℕ × ℕ) : Prop :=
  let l : ℕ → ℕ → ℕ := fun d u => sInf {p | 0 < p ∧ ∃ k₀, ∀ k ≥ k₀,
    b ^ k % commaCycleSum b d u = b ^ (k + p) % commaCycleSum b d u}
  let L : ℕ :=
    ((Finset.Ico 1 b).sigma fun d => insert 0 (commaDangerFinalSet b d)).lcm fun p => l p.1 p.2
  let valid : ℕ × ℕ × ℕ → Prop := fun x =>
    1 ≤ x.1 ∧ x.1 < b ∧ x.2.1 ∈ commaDangerFinalSet b x.1 ∧ x.2.2 < L
  valid v ∧ valid w ∧ w.1 = (if v.1 < b - 1 then v.1 + 1 else 1) ∧
    w.2.2 = (if v.1 < b - 1 then v.2.2 else (v.2.2 + 1) % L) ∧
    ∃ K, ∀ k ≥ K, k % L = v.2.2 → commaIntervalStep b v.1 v.2.1 k w.2.1

/-- Characteristic property: an edge of `G_b'` leaves a vertex `(d, u, κ)` with `1 ≤ d < b` and
`u ∈ U(b, d)`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5, Section 3.4. -/
public theorem commaReducedGraphEdge_source {b : ℕ} {v w : ℕ × ℕ × ℕ}
    (h : commaReducedGraphEdge b v w) :
    1 ≤ v.1 ∧ v.1 < b ∧ v.2.1 ∈ commaDangerFinalSet b v.1 :=
  ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩

open Classical in
/-- For `m ≥ 3`, the number `D(b)` of initial values in the danger interval `[b^m - b², b^m)`
whose base-`b` comma sequence never reaches `b^m` is independent of `m` and has generating
function `∑ D(b) t^b = (1 - t)⁻¹ (∑_{n ≥ 1} t^{n(n+3)/2} / (1 - t^n) - t²)`; stated through the
coefficient of `t^b`: `D(b) + 1 = #{(n, j) : n ≥ 1, j ≥ 0, n(n + 3)/2 + j n ≤ b}`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
Theorem 2 (`jis-2025-25.5.5-thm-2`). -/
public theorem_wanted commaDangerInterval_card_not_reach (b m : ℕ) (hb : 2 ≤ b) (hm : 3 ≤ m) :
    ((Finset.Ico (b ^ m - b ^ 2) (b ^ m)).filter fun v =>
        ∀ t, Relation.ReflTransGen (IsCommaSucc b) v t → t < b ^ m).card + 1 =
      ((Finset.Icc 1 b ×ˢ Finset.range (b + 1)).filter fun p =>
        p.1 * (p.1 + 3) / 2 + p.2 * p.1 ≤ b).card

/-- For `1 ≤ d < b` and `k > 2`, the values `u` with `0 < u ≤ b²` such that `d b^k - u` is the
final value of a comma sequence in the interval `[d b^k - b², d b^k)` (it is terminal or its
successor is at least `d b^k`) are exactly `U(b, d)`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
Lemma 6 (`jis-2025-25.5.5-lem-6`). -/
public theorem_wanted commaDanger_final_iff_mem (b d k u : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d)
    (hdb : d < b) (hk : 2 < k) :
    (0 < u ∧ u ≤ b ^ 2 ∧ (IsCommaTerminal b (d * b ^ k - u) ∨
        ∀ m, IsCommaSucc b (d * b ^ k - u) m → d * b ^ k ≤ m)) ↔
      u ∈ commaDangerFinalSet b d

/-- For each base `b ≥ 2` there are `L(b) > 0` and a threshold `K` such that, for `k ≥ K`, the
comma map `(d, u, k) → (d', u', k')` depends on `k` only through `k mod L(b)`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
Proposition 8 (`jis-2025-25.5.5-prop-8`). -/
public theorem_wanted commaIntervalStep_eventually_periodic (b : ℕ) (hb : 2 ≤ b) :
    ∃ L, 0 < L ∧ ∃ K, ∀ d u u' k k₂, 1 ≤ d → d < b → 0 < u → u ≤ b ^ 2 → K ≤ k → K ≤ k₂ →
      k % L = k₂ % L → (commaIntervalStep b d u k u' ↔ commaIntervalStep b d u k₂ u')

/-- `G_b'` has in- and out-degree at most `1`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
Lemma 10 (`jis-2025-25.5.5-lem-10`). -/
public theorem_wanted commaReducedGraphEdge_degree_le_one (b : ℕ) (hb : 2 ≤ b) :
    (∀ v w w', commaReducedGraphEdge b v w → commaReducedGraphEdge b v w' → w = w') ∧
      ∀ v v' w, commaReducedGraphEdge b v w → commaReducedGraphEdge b v' w → v = v'

/-- All base-`b` comma sequences with positive initial values terminate if and only if `G_b'`
has no cycle.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
Proposition 11 (`jis-2025-25.5.5-prop-11`). -/
public theorem_wanted commaTerminating_iff_no_cycle (b : ℕ) (hb : 2 ≤ b) :
    (∀ v, 0 < v → IsCommaTerminating b v) ↔
      ¬ ∃ x, Relation.TransGen (commaReducedGraphEdge b) x x

/-- If no vertex `(d, u, 0)` of `G_b'` lies on a cycle, all base-`b` comma sequences with
positive initial values terminate.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
Proposition 12 (`jis-2025-25.5.5-prop-12`). -/
public theorem_wanted commaTerminating_of_no_cycle_through_zero (b : ℕ) (hb : 2 ≤ b)
    (h : ∀ d u, ¬ Relation.TransGen (commaReducedGraphEdge b) (d, u, 0) (d, u, 0)) :
    ∀ v, 0 < v → IsCommaTerminating b v

/-- For `y > 0`, writing `overline{(x, y)}_c = c^k - c² + x c + y` (the base-`c` numeral
`(c - 1, …, c - 1, x, y)_c` with `k` digits), `overline{(x, y)}_{b-1}` has comma successor
`overline{(r, s)}_{b-1}` in base `b - 1` if and only if `overline{(x + 1, y)}_b` has comma
successor `overline{(r + 1, s)}_b` in base `b`. Stated for `k ≥ 3`, so that the leading digit is
`c - 1` as the proof uses; the paper's standing `k ≥ 2` fails at `k = 2`: for `b = 4`, `x = 0`,
`y = 1`, `r = 1`, `s = 2`, the base-`3` successor of `1` is `5 = overline{(1, 2)}_3`, but the
base-`4` successor of `5 = overline{(1, 1)}_4` is `11`, not `10 = overline{(2, 2)}_4`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
Lemma 14 (`jis-2025-25.5.5-lem-14`). -/
public theorem_wanted commaSucc_overline_iff (b k x y r s : ℕ) (hb : 3 ≤ b) (hk : 3 ≤ k)
    (hx : x < b - 1) (hy : 0 < y) (hyb : y < b - 1) (hr : r < b - 1) (hs : s < b - 1) :
    IsCommaSucc (b - 1) ((b - 1) ^ k - (b - 1) ^ 2 + x * (b - 1) + y)
        ((b - 1) ^ k - (b - 1) ^ 2 + r * (b - 1) + s) ↔
      IsCommaSucc b (b ^ k - b ^ 2 + (x + 1) * b + y) (b ^ k - b ^ 2 + (r + 1) * b + s)

/-- With `I_k(c)` the initial values in `[c^k - c², c^k)` whose base-`c` comma sequence never
reaches `c^k` (`k ≥ 3`), the map `f(overline{(r, s)}_{b-1}) = overline{(r + 1, s)}_b` sends
`I_k(b - 1)` injectively into `I_k(b)`, and every element of `I_k(b)` outside its image is
`overline{(1, b - 2)}_b` or some `overline{(0, y)}_b` with `0 < y < b - 1`.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
Lemma 15 (`jis-2025-25.5.5-lem-15`). -/
public theorem_wanted commaNotReach_shift_injection (b k : ℕ) (hb : 3 ≤ b) (hk : 3 ≤ k) :
    let I : ℕ → Set ℕ := fun c =>
      {v | c ^ k - c ^ 2 ≤ v ∧ v < c ^ k ∧
        ∀ t, Relation.ReflTransGen (IsCommaSucc c) v t → t < c ^ k}
    (∀ r s, r < b - 1 → s < b - 1 → (b - 1) ^ k - (b - 1) ^ 2 + r * (b - 1) + s ∈ I (b - 1) →
      b ^ k - b ^ 2 + (r + 1) * b + s ∈ I b) ∧
    (∀ r s r' s', r < b - 1 → s < b - 1 → r' < b - 1 → s' < b - 1 →
      b ^ k - b ^ 2 + (r + 1) * b + s = b ^ k - b ^ 2 + (r' + 1) * b + s' → r = r' ∧ s = s') ∧
    ∀ w ∈ I b, (¬ ∃ r s, r < b - 1 ∧ s < b - 1 ∧
        (b - 1) ^ k - (b - 1) ^ 2 + r * (b - 1) + s ∈ I (b - 1) ∧
        w = b ^ k - b ^ 2 + (r + 1) * b + s) →
      w = b ^ k - b ^ 2 + b + (b - 2) ∨ ∃ y, 0 < y ∧ y < b - 1 ∧ w = b ^ k - b ^ 2 + y

open Classical in
/-- The elements of `I_k(b)` (`k ≥ 3`) not covered by the injection of Lemma 15 are in bijection
with the representations `b = T(i) - T(j)`, `i > j ≥ 1`, as a difference of two positive
triangular numbers `T(n) = n(n + 1)/2`; stated as equality of cardinalities.

Source: Robert Dougherty-Bliss and Natalya Ter-Saakov, *The Comma Sequence is Finite in Other
Bases*, Journal of Integer Sequences 28 (2025), Article 25.5.5,
Lemma 16 (`jis-2025-25.5.5-lem-16`). -/
public theorem_wanted commaNotReach_uncovered_card (b k : ℕ) (hb : 3 ≤ b) (hk : 3 ≤ k) :
    let notReach : ℕ → ℕ → Prop := fun c v =>
      c ^ k - c ^ 2 ≤ v ∧ v < c ^ k ∧ ∀ t, Relation.ReflTransGen (IsCommaSucc c) v t → t < c ^ k
    ((Finset.Ico (b ^ k - b ^ 2) (b ^ k)).filter fun w => notReach b w ∧
        ¬ ∃ r < b - 1, ∃ s < b - 1, notReach (b - 1) ((b - 1) ^ k - (b - 1) ^ 2 + r * (b - 1) + s) ∧
          w = b ^ k - b ^ 2 + (r + 1) * b + s).card =
      ((Finset.range (b + 1) ×ˢ Finset.range (b + 1)).filter fun p =>
        1 ≤ p.2 ∧ p.2 < p.1 ∧ p.1 * (p.1 + 1) / 2 - p.2 * (p.2 + 1) / 2 = b).card

end

end MetaMathlibExt
