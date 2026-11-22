/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Squarefree.Basic
public import MathlibExt.Combinatorics.Additive.WeightedDavenport

namespace MetaMathlibExt

@[expose] public section

open Pointwise

/-! This file formalizes statements, not proofs, from Paul and Paul. -/

/-- `unitSet n` is the paper's `U(n)`, represented as the elements of `ZMod n`
that satisfy `IsUnit`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def unitSet (n : ℕ) : Set (ZMod n) := {x | IsUnit x}

/-- `unitSquareSet n` is the paper's `U(n)²`: its existential records a unit
`u` and the equation `x = u ^ 2`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def unitSquareSet (n : ℕ) : Set (ZMod n) := {x | ∃ u, IsUnit u ∧ x = u ^ 2}

/-- `squareSet n` is the paper's `S(n)`: the conjunction says that `x` is
nonzero and is the square of an element of `ZMod n`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def squareSet (n : ℕ) : Set (ZMod n) := {x | x ≠ 0 ∧ ∃ y, x = y ^ 2}

/-- `HasWeightedZeroSum A S` says that every term of the finite sequence `S`
gets a coefficient in `A` and that the resulting full weighted sum is zero.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasWeightedZeroSum {n k : ℕ} (A : Set (ZMod n)) (S : Fin k → ZMod n) : Prop :=
  ∃ a : Fin k → ZMod n, (∀ i, a i ∈ A) ∧ ∑ i, a i * S i = 0

/-- `HasWeightedZeroSumSubseq A S` represents a subsequence by a nonempty
finset `J` of indices; only indices in `J` receive constrained weights and
contribute to the zero sum.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasWeightedZeroSumSubseq {n k : ℕ} (A : Set (ZMod n))
    (S : Fin k → ZMod n) : Prop :=
  ∃ J : Finset (Fin k), J.Nonempty ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ J, a i ∈ A) ∧ ∑ i ∈ J, a i * S i = 0

/-- `HasConsecutiveWeightedZeroSumSubseq A S` adds the clause that the chosen
index finset is exactly an interval `[lo, hi]` in the natural values of `Fin k`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasConsecutiveWeightedZeroSumSubseq {n k : ℕ} (A : Set (ZMod n))
    (S : Fin k → ZMod n) : Prop :=
  ∃ J : Finset (Fin k), J.Nonempty ∧
    (∃ lo hi : ℕ, J = Finset.univ.filter fun i => lo ≤ i.1 ∧ i.1 ≤ hi) ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ J, a i ∈ A) ∧ ∑ i ∈ J, a i * S i = 0

/-- `zmodWeightReps A` is the set of representatives `a ∈ [0, n)` whose residue lies in
`A ⊆ ℤ_n`. Natural weights act on `ZMod n` by `a • x = (a : ZMod n) * x`, so the
MathlibExt constant `weightedDavenport (zmodWeightReps A) (ZMod n)` is the paper's `D_A`
for `n ≥ 1`: every residue has exactly one representative in `[0, n)`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public noncomputable def zmodWeightReps {n : ℕ} (A : Set (ZMod n)) : Finset ℕ :=
  open Classical in (Finset.range n).filter fun a => (a : ZMod n) ∈ A

/-- Membership in `zmodWeightReps A`: a representative below `n` whose residue is in `A`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public theorem mem_zmodWeightReps {n : ℕ} {A : Set (ZMod n)} {a : ℕ} :
    a ∈ zmodWeightReps A ↔ a < n ∧ (a : ZMod n) ∈ A := by
  classical
  simp [zmodWeightReps]

/-- The defining set for the consecutive constant replaces arbitrary
subsequences by `HasConsecutiveWeightedZeroSumSubseq`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def weightedConsecutiveDefiningSet (n : ℕ) (A : Set (ZMod n)) : Set ℕ :=
  {k | 0 < k ∧ ∀ S : Fin k → ZMod n, HasConsecutiveWeightedZeroSumSubseq A S}

/-- `weightedConsecutiveConstant n A` is the paper's `C_A`, the infimum of
positive lengths forcing a consecutive weighted zero-sum subsequence.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public noncomputable def weightedConsecutiveConstant (n : ℕ) (A : Set (ZMod n)) : ℕ :=
  sInf (weightedConsecutiveDefiningSet n A)

/-- Weighted zero-sum subsequences are monotone in the weight set: the same
index set and weights witness the conclusion after replacing `A` by a superset
`B`. This is a characteristic lemma for the new predicate.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public theorem HasWeightedZeroSumSubseq.mono {n k : ℕ} {A B : Set (ZMod n)}
    {S : Fin k → ZMod n} (hAB : A ⊆ B) (h : HasWeightedZeroSumSubseq A S) :
    HasWeightedZeroSumSubseq B S := by
  rcases h with ⟨J, hJ, a, ha, hsum⟩
  exact ⟨J, hJ, a, fun i hi => hAB (ha i hi), hsum⟩

/-- The one-term zero sequence has a `squareSet n`-weighted zero sum, witnessed
by weight one. The added `2 ≤ n` makes one nonzero in `ZMod n` and follows the
paper's ambient convention `n ≥ 2`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public theorem zeroSingleton_hasWeightedZeroSum (n : ℕ) (hn : 2 ≤ n) :
    HasWeightedZeroSum (squareSet n) (fun _ : Fin 1 => 0) := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro i
    refine ⟨?_, 1, by simp⟩
    intro h
    have h' : ((1 : ℕ) : ZMod n) = 0 := by simpa only [Nat.cast_one] using h
    have hd : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp h'
    have hle : n ≤ 1 := Nat.le_of_dvd (by omega) hd
    omega
  · simp

/-- Lemma 4: for prime `p` and positive `r`, with `l = (r - 1) / 2`, the first
clause is `S(p^r) = ⋃ k, p^(2k)U(p^r)^2`; the second says those pieces are
pairwise disjoint. `Fin (l+1)` is the integer interval `[0,l]`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 4. -/
public theorem_wanted squareSet_primePower_decomposition (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    let l := (r - 1) / 2
    let pieces : Fin (l + 1) → Set (ZMod (p ^ r)) := fun k =>
      ((p : ZMod (p ^ r)) ^ (2 * (k : ℕ))) • unitSquareSet (p ^ r)
    squareSet (p ^ r) = ⋃ k, pieces k ∧ Set.PairwiseDisjoint Set.univ pieces

/-- Lemma 5: for prime `p`, natural `r`, and every `k` in
`[0,(r-1)/2]`, the scaled square-unit set modulo `p^r` and the square-unit set
modulo `p^(r-2k)` have equal finite cardinality. No positivity of `r` is added.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 5. -/
public theorem_wanted ncard_scale_unitSquares_primePower (p r k : ℕ) (hp : p.Prime)
    (hk : k ≤ (r - 1) / 2) :
    (((p : ZMod (p ^ r)) ^ (2 * k)) • unitSquareSet (p ^ r)).ncard =
      (unitSquareSet (p ^ (r - 2 * k))).ncard

/-- Theorem 6: the first implication is the even-`r` cardinality sum and the
second is the odd-`r` sum. The displayed ellipses are encoded by ranges of
length `r/2` and `(r+1)/2`. Prime and positive hypotheses are made explicit
from the surrounding text.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 6. -/
public theorem_wanted ncard_squareSet_primePower (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    (Even r → (squareSet (p ^ r)).ncard =
      ∑ k ∈ Finset.range (r / 2), (unitSquareSet (p ^ (r - 2 * k))).ncard) ∧
    (Odd r → (squareSet (p ^ r)).ncard =
      ∑ k ∈ Finset.range ((r + 1) / 2), (unitSquareSet (p ^ (r - 2 * k))).ncard)

/-- Lemma 7: `p` is prime, divides `n`, and has factorization exponent `r`;
if the full image sequence modulo `p^r` has an `S(p^r)`-weighted zero sum,
then the original full sequence has an `S(n)`-weighted zero sum. The sequence
length `k` is an explicit binder required by the `Fin k` encoding, and
`2 ≤ n` records the paper's ambient convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 7. -/
public theorem_wanted squareWeightedZeroSum_of_primePower_reduction (n p r k : ℕ)
    (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) (hval : n.factorization p = r)
    (S : Fin k → ZMod n)
    (hS : HasWeightedZeroSum (squareSet (p ^ r))
      (fun i => (ZMod.cast (S i) : ZMod (p ^ r)))) :
    HasWeightedZeroSum (squareSet n) S

/-- Corollary 8: under the same prime-divisor and valuation clauses,
`C_{S(n)} ≤ C_{S(p^r)}`. The exponent equality formalizes `r = v_p(n)`.
The added `2 ≤ n` records the paper's ambient convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 8. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_le_primePower (n p r : ℕ)
    (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) (hval : n.factorization p = r) :
    weightedConsecutiveConstant n (squareSet n) ≤
      weightedConsecutiveConstant (p ^ r) (squareSet (p ^ r))

/-- Lemma 9: for `2 ≤ p` and odd `r`, an `S(p)`-weighted zero sum after
reduction implies an `S(p^r)`-weighted zero sum, as printed (`S(p)` weights,
`p` an integer at least two); the otherwise unspecified length `k` is bound.
This is at least as strong as a `U(p)²` reading because `U(p)² ⊆ S(p)`, and
the two agree for prime `p`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 9. -/
public theorem_wanted squareWeightedZeroSum_of_reduction_oddPower (p r k : ℕ)
    (hp : 2 ≤ p) (hr : Odd r) (T : Fin k → ZMod (p ^ r))
    (hT : HasWeightedZeroSum (squareSet p) (fun i => (ZMod.cast (T i) : ZMod p))) :
    HasWeightedZeroSum (squareSet (p ^ r)) T

/-- Lemma 10: nonzero even `r`, unit terms `x₁,x₂,x₃`, and componentwise
reduction to `(1,1,1)` imply that the three-term sequence has no
`S(2^r)`-weighted zero-sum subsequence.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 10. -/
public theorem_wanted no_squareWeightedSubseq_three_units_twoPower (r : ℕ)
    (hr0 : r ≠ 0) (hrEven : Even r) (S : Fin 3 → ZMod (2 ^ r))
    (hunit : ∀ i, IsUnit (S i))
    (hred : ∀ i, (ZMod.cast (S i) : ZMod 4) = 1) :
    ¬HasWeightedZeroSumSubseq (squareSet (2 ^ r)) S

/-- Lemma 11: let `p` be a prime and `r` a nonzero even number, let `(z₁, z₂)` be units
modulo `p²` whose reduction modulo `p` has no `S(p)`-weighted zero sum, and let
`S = (x₁, x₂, y₁)` reduce modulo `p²` to `(z₁, z₂, p)`. Then `S` has no `S(p^r)`-weighted
zero-sum subsequence. The paper says `S` lies in `U(p^r)`, which no `y₁` reducing to the
nonunit `p` can satisfy; its proof writes `y₁ = p w₁` with `w₁` a unit, and Theorem 12 applies
the lemma to `(u_p, v_p, p)`, so `S` is taken in `ℤ_{p^r}` (then `x₁, x₂` are units because
`z₁, z₂` are). The paper's `Q_p` is `S(p)` for prime `p`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 11. -/
public theorem_wanted no_squareWeightedSubseq_pair_and_prime_of_reduction (p r : ℕ)
    (hp : p.Prime) (hr0 : r ≠ 0) (hrEven : Even r) (z : Fin 2 → ZMod (p ^ 2))
    (hz : ∀ i, IsUnit (z i))
    (hzred : ¬HasWeightedZeroSum (squareSet p) (fun i => (ZMod.cast (z i) : ZMod p)))
    (S : Fin 3 → ZMod (p ^ r))
    (hS : ∀ i, (ZMod.cast (S i) : ZMod (p ^ 2)) = ![z 0, z 1, (p : ZMod (p ^ 2))] i) :
    ¬HasWeightedZeroSumSubseq (squareSet (p ^ r)) S

/-- Theorem 12: if `n ≥ 2` is even and a natural-number square, then
`4 ≤ D_{S(n)}` (in `ℕ∞`); `n ≥ 2` is the paper's ambient convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 12. -/
public theorem_wanted weightedDavenport_squareSet_evenSquare_lowerBound (n : ℕ)
    (hn : 2 ≤ n) (heven : Even n) (hsquare : IsSquare n) :
    4 ≤ weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n)

/-- Lemma 13: for nonzero even `r` and `2 ≤ p`, a full
`U(p²)²`-weighted zero sum after reduction modulo `p²` lifts to a full
`S(p^r)`-weighted zero sum. The sequence length is explicit. The requested
bullet strengthens the paper text's `0 < p` to `2 ≤ p`; that deviation is
followed literally.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 13. -/
public theorem_wanted squareWeightedZeroSum_of_reduction_square (p r k : ℕ)
    (hp : 2 ≤ p) (hr0 : r ≠ 0) (hrEven : Even r)
    (T : Fin k → ZMod (p ^ r))
    (hT : HasWeightedZeroSum (unitSquareSet (p ^ 2))
      (fun i => (ZMod.cast (T i) : ZMod (p ^ 2)))) :
    HasWeightedZeroSum (squareSet (p ^ r)) T

/-- Corollary 14: `p ≥ 2` and nonzero even `r` give both the Davenport
and consecutive inequalities from `S(p^r)` to `U(p²)²`, represented by a
conjunction. The paper says `p` positive; `p = 1` is excluded (the paper's
ambient `n ≥ 2`), since then `S(1)` is empty, so `D_{S(1)} = ⊤`, while
`D_{U(1)²} = 1`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 14. -/
public theorem_wanted squareSet_constants_le_unitSquares_modSquare (p r : ℕ)
    (hp : 2 ≤ p) (hr0 : r ≠ 0) (hrEven : Even r) :
    weightedDavenport (zmodWeightReps (squareSet (p ^ r))) (ZMod (p ^ r)) ≤
        weightedDavenport (zmodWeightReps (unitSquareSet (p ^ 2))) (ZMod (p ^ 2)) ∧
      weightedConsecutiveConstant (p ^ r) (squareSet (p ^ r)) ≤
        weightedConsecutiveConstant (p ^ 2) (unitSquareSet (p ^ 2))

/-- Theorem 15: for a nonzero even exponent `r`, the consecutive
`S(2^r)`-weighted zero-sum constant is at most four.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 15. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_twoPower_le_four (r : ℕ)
    (hr0 : r ≠ 0) (hrEven : Even r) :
    weightedConsecutiveConstant (2 ^ r) (squareSet (2 ^ r)) ≤ 4

/-- Corollary 16: for an even square `n ≥ 2`, the Davenport and consecutive
`S(n)` constants both equal four. The consecutive defining set is asserted
nonempty to make its natural `sInf` equality nonvacuous.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 16. -/
public theorem_wanted squareSet_constants_evenSquare (n : ℕ) (hn : 2 ≤ n)
    (heven : Even n) (hsquare : IsSquare n) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n) = 4 ∧
      weightedConsecutiveConstant n (squareSet n) = 4

/-- Proposition 17: for odd `n ≥ 2`, there are two units `u,v` such that for
each prime divisor `p`, their two-term image has no `S(p)`-weighted zero-sum
subsequence. The bullet's `S(p)` replaces the paper's equivalent `Q_p` for odd
prime `p`; `n ≥ 2` records the ambient convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Proposition 17. -/
public theorem_wanted exists_pair_units_avoiding_prime_squareWeights (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) :
    ∃ u v : ZMod n, IsUnit u ∧ IsUnit v ∧
      ∀ p : ℕ, p.Prime → p ∣ n →
        ¬HasWeightedZeroSumSubseq (squareSet p)
          (fun i : Fin 2 => (ZMod.cast (![u, v] i) : ZMod p))

/-- Lemma 18: for odd prime `p` and positive `r`, if the two unit terms have
no `S(p)`-weighted zero-sum subsequence after reduction, then the original
pair has no `S(p^r)`-weighted zero-sum subsequence. The paper writes the
equivalent `Q_p` in the hypothesis.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 18. -/
public theorem_wanted no_squareWeightedSubseq_pair_of_reduction (p r : ℕ)
    (hp : p.Prime) (hpOdd : Odd p) (hr : 0 < r) (S : Fin 2 → ZMod (p ^ r))
    (hunit : ∀ i, IsUnit (S i))
    (hred : ¬HasWeightedZeroSumSubseq (squareSet p)
      (fun i => (ZMod.cast (S i) : ZMod p))) :
    ¬HasWeightedZeroSumSubseq (squareSet (p ^ r)) S

/-- Theorem 19: for odd `n ≥ 2`, `D_{S(n)} ≥ 3` (in `ℕ∞`); `n ≥ 2` is the
paper's ambient convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 19. -/
public theorem_wanted weightedDavenport_squareSet_odd_lowerBound (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) :
    3 ≤ weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n)

/-- Theorem 20: for `n ≥ 2`, if the exponent of two in `n` is even and at
least two, then `D_{S(n)} ≥ 3` (in `ℕ∞`).
`n.factorization 2` formalizes `v₂(n)`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 20. -/
public theorem_wanted weightedDavenport_squareSet_even_twoValuation_lowerBound (n : ℕ)
    (hn : 2 ≤ n) (hvalEven : Even (n.factorization 2))
    (hval : 2 ≤ n.factorization 2) :
    3 ≤ weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n)

/-- Theorem 21: for odd prime `p` and odd exponent `r`, the consecutive
`S(p^r)`-weighted zero-sum constant is at most three.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 21. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_oddPrimePower_le_three
    (p r : ℕ) (hp : p.Prime) (hpOdd : Odd p) (hrOdd : Odd r) :
    weightedConsecutiveConstant (p ^ r) (squareSet (p ^ r)) ≤ 3

/-- Corollary 22: for a nonsquare `n ≥ 2` whose two-adic exponent is even,
both constants equal three (the consecutive defining set is asserted
nonempty). Nonnegativity of `v₂(n)` is automatic because `factorization` is
natural-valued.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 22. -/
public theorem_wanted squareSet_constants_nonsquare_even_twoValuation (n : ℕ)
    (hn : 2 ≤ n) (hnotSquare : ¬IsSquare n)
    (hvalEven : Even (n.factorization 2)) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n) = 3 ∧
      weightedConsecutiveConstant n (squareSet n) = 3

/-- Theorem 23: odd exponent `r` gives
`C_{S(2^r)} ≤ 2`; oddness already implies that `r` is positive.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 23. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_odd_twoPower_le_two (r : ℕ)
    (hrOdd : Odd r) :
    weightedConsecutiveConstant (2 ^ r) (squareSet (2 ^ r)) ≤ 2

/-- Corollary 24: for positive even `n` with odd two-adic exponent, the
Davenport and consecutive constants equal two (the consecutive defining set is
asserted nonempty). `n.factorization 2` is `v₂(n)`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 24. -/
public theorem_wanted squareSet_constants_odd_twoValuation (n : ℕ) (hn : 0 < n)
    (hnEven : Even n) (hvalOdd : Odd (n.factorization 2)) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n) = 2 ∧
      weightedConsecutiveConstant n (squareSet n) = 2

/-- Lemma 25: the hypotheses give prime `p`, nonzero even `r`, two unit terms
whose reduction has no `S(p)`-weighted zero-sum subsequence, and a unit `u`;
the four-term sequence `(u w₁, u w₂, p w₁, p w₂)` then has no
`S(p^r)`-weighted zero-sum subsequence. The paper writes the equivalent `Q_p`
for the reduced weights.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 25. -/
public theorem_wanted no_squareWeightedSubseq_fourTerm_pattern (p r : ℕ)
    (hp : p.Prime) (hr0 : r ≠ 0) (hrEven : Even r)
    (w₁ w₂ u : ZMod (p ^ r)) (hw₁ : IsUnit w₁) (hw₂ : IsUnit w₂)
    (hu : IsUnit u)
    (hred : ¬HasWeightedZeroSumSubseq (squareSet p)
      (fun i : Fin 2 => (ZMod.cast (![w₁, w₂] i) : ZMod p))) :
    ¬HasWeightedZeroSumSubseq (squareSet (p ^ r))
      ![u * w₁, u * w₂, (p : ZMod (p ^ r)) * w₁, (p : ZMod (p ^ r)) * w₂]

/-- Theorem 26: for an odd square `n ≥ 2`, `D_{S(n)} ≥ 5` (in `ℕ∞`). The lower
bound on `n` is the paper's ambient convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 26. -/
public theorem_wanted weightedDavenport_squareSet_oddSquare_lowerBound (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) (hsquare : IsSquare n) :
    5 ≤ weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n)

/-- Lemma 27: for odd prime `p`, positive `r`, and three units, the sum of
`Ay₁`, `Ay₂ ∪ {0}`, and `Ay₃ ∪ {0}` is all of `ZMod (p^r)`, where
`A = U(p^r)²`, with Mathlib's pointwise set product and sum; the explicit
parentheses fix the harmless associativity convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 27. -/
public theorem_wanted three_unitSquare_cosets_cover (p r : ℕ) (hp : p.Prime)
    (hpOdd : Odd p) (hr : 0 < r) (y₁ y₂ y₃ : ZMod (p ^ r))
    (hy₁ : IsUnit y₁) (hy₂ : IsUnit y₂) (hy₃ : IsUnit y₃) :
    unitSquareSet (p ^ r) * {y₁} +
      (unitSquareSet (p ^ r) * {y₂} ∪ {0} + (unitSquareSet (p ^ r) * {y₃} ∪ {0})) =
        Set.univ

/-- Theorem 28: nonzero even `r` and odd prime `p` imply
`D_{S(p^r)} ≤ 5`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 28. -/
public theorem_wanted weightedDavenport_squareSet_oddPrimePower_le_five (p r : ℕ)
    (hp : p.Prime) (hpOdd : Odd p) (hr0 : r ≠ 0) (hrEven : Even r) :
    weightedDavenport (zmodWeightReps (squareSet (p ^ r))) (ZMod (p ^ r)) ≤ 5

/-- Corollary 29: for an odd square `n ≥ 2`, `D_{S(n)} = 5`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 29. -/
public theorem_wanted weightedDavenport_squareSet_oddSquare (n : ℕ) (hn : 2 ≤ n)
    (hnOdd : Odd n) (hsquare : IsSquare n) :
    weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n) = 5

/-- Theorem 30: the consecutive constant with weights `U(25)²` equals nine;
its defining set is also asserted nonempty to make the natural `sInf` equality
nonvacuous.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 30. -/
public theorem_wanted weightedConsecutiveConstant_unitSquares_twentyFive :
    (weightedConsecutiveDefiningSet 25 (unitSquareSet 25)).Nonempty ∧
      weightedConsecutiveConstant 25 (unitSquareSet 25) = 9

/-- Theorem 31: for an odd square `n ≥ 2`, the consecutive `S(n)` constant is
at most nine. The lower bound on `n` records the paper's ambient convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 31. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_oddSquare_le_nine (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) (hsquare : IsSquare n) :
    weightedConsecutiveConstant n (squareSet n) ≤ 9

/-- Theorem 34: prime `p ≥ 7` and even `r ≥ 4` imply
`C_{S(p^r)} ≤ 5`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 34. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_largePrimePower_le_five
    (p r : ℕ) (hp : p.Prime) (hpSeven : 7 ≤ p) (hrEven : Even r)
    (hrFour : 4 ≤ r) :
    weightedConsecutiveConstant (p ^ r) (squareSet (p ^ r)) ≤ 5

/-- Corollary 35: if odd square `n ≥ 2` is divisible by `p⁴` for a prime
`p ≥ 7`, the consecutive defining set is nonempty and `C_{S(n)} = 5`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 35. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_oddSquare_largePrime (n p : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) (hnSquare : IsSquare n)
    (hp : p.Prime) (hpSeven : 7 ≤ p) (hdiv : p ^ 4 ∣ n) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedConsecutiveConstant n (squareSet n) = 5

/-- Lemma 36: for positive `r`, if at least four terms of a sequence modulo
`5^r` are units, then the full sequence has a `U(5^r)²`-weighted zero sum.
The length `k` is explicit, and an existential finset witnesses the four unit
positions.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 36. -/
public theorem_wanted unitSquareWeightedZeroSum_modFivePower_of_four_units (r k : ℕ)
    (hr : 0 < r) (S : Fin k → ZMod (5 ^ r))
    (hunits : ∃ J : Finset (Fin k), 4 ≤ J.card ∧ ∀ i ∈ J, IsUnit (S i)) :
    HasWeightedZeroSum (unitSquareSet (5 ^ r)) S

/-- Theorem 37: even `r ≥ 4` implies `C_{S(5^r)} ≤ 7`.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 37. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_fivePower_le_seven (r : ℕ)
    (hrEven : Even r) (hrFour : 4 ≤ r) :
    weightedConsecutiveConstant (5 ^ r) (squareSet (5 ^ r)) ≤ 7

/-- Corollary 38: if square `n ≥ 2` is divisible by `5⁴`, then
`C_{S(n)} ≤ 7`. The lower bound on `n` records the paper's ambient convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 38. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_square_divisible_fiveFourth
    (n : ℕ) (hn : 2 ≤ n) (hnSquare : IsSquare n) (hdiv : 5 ^ 4 ∣ n) :
    weightedConsecutiveConstant n (squareSet n) ≤ 7

/-- Theorem 39: `n` is represented as `m²` for an odd squarefree `m`, and the
consecutive defining set is nonempty with `C_{S(n)} = 9`. The clause `2 ≤ n`
records the paper's ambient convention; `Squarefree m` is the natural-number
squarefree predicate.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 39. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_square_oddSquarefree
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n = m ^ 2) (hmOdd : Odd m)
    (hmSquarefree : Squarefree m) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedConsecutiveConstant n (squareSet n) = 9

end

end MetaMathlibExt
