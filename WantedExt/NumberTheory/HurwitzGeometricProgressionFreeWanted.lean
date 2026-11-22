/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Totient

/-!
# Avoiding 3-term geometric progressions in Hurwitz quaternions: wishlist

Source: Megumi Asada, Bruce Fang, Eva Fourakis, Sarah Manski, Nathan McNew, Steven J. Miller,
Gwyneth Moreland, Ajmain Yamin, and Sindy Xin Zhang, *Avoiding 3-Term Geometric Progressions
in Hurwitz Quaternions*, Journal of Integer Sequences 27 (2024), Article 24.7.7
(arXiv:1807.07605).

No new definition is introduced; the paper's notions are written inline (local notation),
following Section 1, Section 2 and Section 5 of the paper:

* `Q_Hur` is the set of quaternions in `ℍ[ℚ]` whose four coordinates are all in `ℤ` or all
  in `ℤ + 1/2`; the norm `Nm` is `Quaternion.normSq`.
* `S(N)` is the set of nonzero Hurwitz quaternions of norm at most `N`, and `S(G)` for
  `G ⊆ ℕ` is the set of Hurwitz quaternions whose norm lies in `G`. The (upper, lower) density
  of `A ⊆ Q_Hur` is the (lim sup, lim inf) limit of `|A ∩ S(N)| / |S(N)|`.
* A 3-term geometric progression is a triple `(a, ar, ar²)` with `a, r ∈ Q_Hur ∖ {0}` and `r`
  a non-unit, i.e. `Nm r ≠ 1`.
* Rankin's greedy set `G₃*(ℕ₊)` is the set of positive integers all of whose `p`-adic
  valuations have no digit `2` in base `3` (the paper's description via Brown and Gordon).
* The quaternion greedy set `G₃*(Q_Hur ∖ {0})` adds Hurwitz quaternions by increasing norm
  unless they complete a progression with smaller-norm members. Since `Nm r ≥ 2`, the new
  element must be the third term; the set is therefore the unique `Gq` with
  `q ∈ Gq ↔ q ∈ Q_Hur, q ≠ 0, and q ≠ a r²` for all `a, ar ∈ Gq` and non-unit `r ≠ 0`
  (unique by strong induction on the norm). Statements about it take such a `Gq` as a
  hypothesis.
-/

namespace MetaMathlibExt

@[expose] public section

set_option quotPrecheck false in
/-- The Hurwitz order: quaternions with all coordinates in `ℤ` or all in `ℤ + 1/2`. -/
local notation "𝐇" => Set.ofPred fun q : Quaternion ℚ =>
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) ∧ q.imI = (b : ℚ) ∧ q.imJ = (c : ℚ) ∧ q.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) + 1 / 2 ∧ q.imI = (b : ℚ) + 1 / 2 ∧
      q.imJ = (c : ℚ) + 1 / 2 ∧ q.imK = (d : ℚ) + 1 / 2)
set_option quotPrecheck false in
/-- `S(N)`: nonzero Hurwitz quaternions of norm at most `N`. -/
local notation "𝐒" N:max => Set.ofPred fun q : Quaternion ℚ =>
  q ∈ 𝐇 ∧ q ≠ 0 ∧ Quaternion.normSq q ≤ ((N : ℕ) : ℚ)
set_option quotPrecheck false in
/-- `S(G)`: Hurwitz quaternions whose norm lies in `G ⊆ ℕ`. -/
local notation "𝐒ᴳ" G:max => Set.ofPred fun q : Quaternion ℚ =>
  q ∈ 𝐇 ∧ ∃ n ∈ G, Quaternion.normSq q = ((n : ℕ) : ℚ)
set_option quotPrecheck false in
/-- The density ratio `|A ∩ S(N)| / |S(N)|`. -/
local notation "ρ" A:max N:max =>
  ((Set.ncard (A ∩ 𝐒 N) : ℝ) / (Set.ncard (𝐒 N) : ℝ))
set_option quotPrecheck false in
/-- `A ⊆ Q_Hur` contains no triple `(a, ar, ar²)` with `a, r ≠ 0` and `r` a non-unit. -/
local notation "GPFree" A:max => A ⊆ 𝐇 ∧ ∀ a ∈ 𝐇, ∀ r ∈ 𝐇, a ≠ 0 → r ≠ 0 →
  Quaternion.normSq r ≠ 1 → ¬ (a ∈ A ∧ a * r ∈ A ∧ a * r ^ 2 ∈ A)
set_option quotPrecheck false in
/-- Rankin's greedy set `G₃*(ℕ₊)`: positive integers whose prime valuations have no
ternary digit `2`. -/
local notation "𝐆ʳ" => Set.ofPred fun n : ℕ =>
  0 < n ∧ ∀ p : ℕ, p.Prime → 2 ∉ Nat.digits 3 (n.factorization p)
set_option quotPrecheck false in
/-- `Gq` is the quaternion greedy set `G₃*(Q_Hur ∖ {0})`, pinned by its defining recursion. -/
local notation "IsQuaternionGreedy" Gq:max => ∀ q : Quaternion ℚ, q ∈ Gq ↔
  (q ∈ 𝐇 ∧ q ≠ 0 ∧ ¬ ∃ a ∈ Gq, ∃ r ∈ 𝐇, r ≠ 0 ∧ Quaternion.normSq r ≠ 1 ∧
    a * r ∈ Gq ∧ q = a * r ^ 2)
set_option quotPrecheck false in
/-- `Q = U R²` for a unit `U ∈ Q_Hur` and some `R ∈ Q_Hur` of norm `r`. -/
local notation "IsUnitMulSq" Q:max r:max => ∃ U ∈ 𝐇, Quaternion.normSq U = 1 ∧
  ∃ R ∈ 𝐇, Quaternion.normSq R = ((r : ℕ) : ℚ) ∧ Q = U * R ^ 2

/-- For every positive integer `N`, the number of Hurwitz quaternions of norm `N` is
`24 σ_odd(N)`, where `σ_odd(N)` is the sum of the odd divisors of `N`.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 1. -/
public theorem_wanted card_hurwitz_norm_eq (N : ℕ) (hN : 0 < N) :
    (Set.ofPred fun q : Quaternion ℚ => q ∈ 𝐇 ∧ Quaternion.normSq q = (N : ℚ)).ncard =
      24 * ∑ d ∈ N.divisors with Odd d, d

/-- (a) The number of nonzero Hurwitz quaternions of norm at most `N` is
`π² N² + O(N log N)`. (b) For a fixed positive integer `M`, the number of those whose norm is
coprime to `M` is `π² N² · (φ(2M)/M) ∏_{p ∣ M} (1 - p⁻²) + O(N log N)`. The `O`-terms are
explicit constants valid for `N ≥ 2`.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 2. -/
public theorem_wanted card_hurwitz_norm_le_asymptotic :
    (∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((𝐒 N).ncard : ℝ) - Real.pi ^ 2 * (N : ℝ) ^ 2| ≤ C * N * Real.log N) ∧
    ∀ M : ℕ, 0 < M → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((Set.ofPred fun q : Quaternion ℚ => q ∈ 𝐇 ∧
            ∃ n : ℕ, Quaternion.normSq q = (n : ℚ) ∧ 0 < n ∧ n ≤ N ∧ n.Coprime M).ncard : ℝ) -
          Real.pi ^ 2 * (N : ℝ) ^ 2 * ((Nat.totient (2 * M) : ℝ) / M) *
            ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ) ^ 2)| ≤ C * N * Real.log N

/-- Let `A ⊆ ℕ` and `G = {n ≥ 1 : ν_p(n) ∈ A for all primes p}`. Then the set `S(G)` of
Hurwitz quaternions with norm in `G` has density
`(1/ζ(2)) (∑_{k ∈ A} 2^{-2k}) ∏_{p > 2} (∑_{k ∈ A} p^{-k} - p⁻¹ ∑_{k ∈ A} p^{-2k})`,
with `1/ζ(2)` written as `6/π²`.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Theorem 5. -/
public theorem_wanted density_hurwitz_norm_valuations_in (A : Set ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ρ (𝐒ᴳ (Set.ofPred fun n : ℕ =>
        0 < n ∧ ∀ p : ℕ, p.Prime → n.factorization p ∈ A)) N)
      Filter.atTop
      (nhds (6 / Real.pi ^ 2 * (∑' k : A, 1 / (2 : ℝ) ^ (2 * (k : ℕ))) *
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
          (∑' k : A, 1 / ((p : ℕ) : ℝ) ^ (k : ℕ) -
            1 / ((p : ℕ) : ℝ) * ∑' k : A, 1 / ((p : ℕ) : ℝ) ^ (2 * (k : ℕ)))))

/-- The set `S(G₃*(ℕ₊))` of Hurwitz quaternions whose norm lies in Rankin's greedy set has
density `(f(2²)/ζ(2)) ∏_{p > 2} (f(p) - f(p²)/p)`, where `f(x) = ∏_{i ≥ 0} (1 + x^{-3^i})`
and `1/ζ(2)` is written as `6/π²`. The paper's numerical value `≈ 0.782643` is not part of the
statement.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Theorem 7 (restated as the unnumbered theorem of the introduction). -/
public theorem_wanted density_hurwitz_norm_in_rankin_greedy :
    Filter.Tendsto (fun N : ℕ => ρ (𝐒ᴳ 𝐆ʳ) N) Filter.atTop
      (nhds ((∏' i : ℕ, (1 + 1 / (4 : ℝ) ^ (3 ^ i))) * (6 / Real.pi ^ 2) *
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
          ((∏' i : ℕ, (1 + 1 / ((p : ℕ) : ℝ) ^ (3 ^ i))) -
            (∏' i : ℕ, (1 + 1 / (((p : ℕ) : ℝ) ^ 2) ^ (3 ^ i))) / ((p : ℕ) : ℝ))))

/-- Let `T_N` be the set of positive integers in
`(N/48, N/45] ∪ (N/40, N/36] ∪ (N/32, N/27] ∪ (N/24, N/12] ∪ (N/9, N/8] ∪ (N/4, N]` and let
`𝒮 = ⋃_{i ≥ 1} T_{N_i}` with `N_i = 48^{2^i}`. Then the upper density of `S(𝒮)` in `Q_Hur` is
`17665627/18662400`.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 10 (the set `𝒮` from Section 4.1). -/
public theorem_wanted upperDensity_hurwitz_norm_in_interval_union :
    Filter.limsup (fun N : ℕ => ρ (𝐒ᴳ (Set.ofPred fun n : ℕ => 0 < n ∧
        ∃ i : ℕ, 1 ≤ i ∧
          let M : ℚ := ((48 ^ (2 ^ i) : ℕ) : ℚ)
          (M / 48 < n ∧ (n : ℚ) ≤ M / 45) ∨ (M / 40 < n ∧ (n : ℚ) ≤ M / 36) ∨
            (M / 32 < n ∧ (n : ℚ) ≤ M / 27) ∨ (M / 24 < n ∧ (n : ℚ) ≤ M / 12) ∨
            (M / 9 < n ∧ (n : ℚ) ≤ M / 8) ∨ (M / 4 < n ∧ (n : ℚ) ≤ M))) N) Filter.atTop =
      17665627 / 18662400

/-- Fix a Hurwitz quaternion `R` of norm `2`, and for `n : ℕ` let `E_n(N)` be the set of triples
`(b R^{3n}, b R^{3n+1}, b R^{3n+2})` with `b ∈ Q_Hur`, `Nm(b)` odd and
`Nm(b) ≤ N / 2^{3n+2}`. The union `E(N) = ⋃_n E_n(N)` consists of pairwise disjoint 3-term
geometric progressions contained in `S(N)³`, and `|E(N)| = π² N²/21 + O(N (log N)²)`.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 12. -/
public theorem_wanted disjoint_progressions_hurwitz_card (R : Quaternion ℚ) (hR : R ∈ 𝐇)
    (hR2 : Quaternion.normSq R = 2) :
    let E : ℕ → Set (Quaternion ℚ × Quaternion ℚ × Quaternion ℚ) := fun N =>
      Set.ofPred fun t => ∃ n : ℕ, ∃ b ∈ 𝐇, ∃ m : ℕ, Odd m ∧
        Quaternion.normSq b = (m : ℚ) ∧ (m : ℚ) ≤ (N : ℚ) / 2 ^ (3 * n + 2) ∧
        t = (b * R ^ (3 * n), b * R ^ (3 * n + 1), b * R ^ (3 * n + 2))
    (∀ N : ℕ, ∀ t ∈ E N,
      (t.1 ∈ 𝐒 N ∧ t.2.1 ∈ 𝐒 N ∧ t.2.2 ∈ 𝐒 N ∧ t.2.1 = t.1 * R ∧ t.2.2 = t.1 * R ^ 2) ∧
      ∀ t' ∈ E N, t ≠ t' →
        Disjoint ({t.1, t.2.1, t.2.2} : Set (Quaternion ℚ)) {t'.1, t'.2.1, t'.2.2}) ∧
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((E N).ncard : ℝ) - Real.pi ^ 2 * (N : ℝ) ^ 2 / 21| ≤ C * N * Real.log N ^ 2

/-- Every set of Hurwitz quaternions avoiding 3-term geometric progressions has upper density
at most `20/21`.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 13. -/
public theorem_wanted upperDensity_le_of_hurwitz_gpFree (A : Set (Quaternion ℚ))
    (hA : GPFree A) :
    Filter.limsup (fun N : ℕ => ρ A N) Filter.atTop ≤ 20 / 21

/-- The supremum `m̄_Hur` of the upper densities of sets of Hurwitz quaternions avoiding 3-term
geometric progressions satisfies `17665627/18662400 ≤ m̄_Hur ≤ 20/21`. The paper's decimal
approximations are not part of the statement.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Theorem 14 (restated as the unnumbered theorem of the introduction). -/
public theorem_wanted sSup_upperDensity_hurwitz_gpFree_bounds :
    let m : ℝ := sSup (Set.ofPred fun x : ℝ => ∃ A : Set (Quaternion ℚ), (GPFree A) ∧
      Filter.limsup (fun N : ℕ => ρ A N) Filter.atTop = x)
    17665627 / 18662400 ≤ m ∧ m ≤ 20 / 21

/-- The quaternion greedy set contains every Hurwitz quaternion of squarefree norm, and its
lower density is at least `60 / (7 π² ζ(3))`, with `ζ(3) = ∑_{n ≥ 1} n⁻³`.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 17. -/
public theorem_wanted quaternionGreedy_squarefree_norm_and_lowerDensity
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) :
    (∀ q ∈ 𝐇, (∃ n : ℕ, Squarefree n ∧ Quaternion.normSq q = (n : ℚ)) → q ∈ Gq) ∧
      60 / (7 * Real.pi ^ 2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) ≤
        Filter.liminf (fun N : ℕ => ρ Gq N) Filter.atTop

/-- The quaternion greedy set is not of the form `S(G)` for any set `G` of positive integers.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 18. -/
public theorem_wanted quaternionGreedy_ne_norm_preimage
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) (G : Set ℕ)
    (hG : ∀ n ∈ G, 0 < n) :
    Gq ≠ 𝐒ᴳ G

/-- Both differences `G₃*(Q_Hur ∖ {0}) ∖ S(G₃*(ℕ₊))` and `S(G₃*(ℕ₊)) ∖ G₃*(Q_Hur ∖ {0})`
between the quaternion greedy set and the norm preimage of Rankin's greedy set are infinite.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 19. -/
public theorem_wanted quaternionGreedy_diff_rankin_infinite
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) :
    (Gq \ 𝐒ᴳ 𝐆ʳ).Infinite ∧ (𝐒ᴳ 𝐆ʳ \ Gq).Infinite

/-- If a positive integer `r` is not a sum of three integer squares, or is divisible by an odd
integer greater than `24`, then some Hurwitz quaternion `Q` of norm `r²` is not of the form
`U R²` with `U` a unit and `Nm(R) = r`; in the first case `Q = r` works.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 20. -/
public theorem_wanted exists_hurwitz_norm_sq_not_unit_mul_sq (r : ℕ) (hr : 0 < r)
    (h : (¬ ∃ a b c : ℕ, r = a ^ 2 + b ^ 2 + c ^ 2) ∨ ∃ m : ℕ, Odd m ∧ 24 < m ∧ m ∣ r) :
    (∃ Q ∈ 𝐇, Quaternion.normSq Q = ((r ^ 2 : ℕ) : ℚ) ∧ ¬ IsUnitMulSq Q r) ∧
      ((¬ ∃ a b c : ℕ, r = a ^ 2 + b ^ 2 + c ^ 2) →
        ¬ IsUnitMulSq ((r : ℚ) : Quaternion ℚ) r)

/-- Let `p` be a prime and `Q` a Hurwitz quaternion of norm `p²` that is not of the form `U R²`
with `U` a unit and `Nm(R) = p`. Then `Q` lies in the quaternion greedy set but not in
`S(G₃*(ℕ₊))`, and `Q²` lies in `S(G₃*(ℕ₊))` but not in the quaternion greedy set.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 21. -/
public theorem_wanted quaternionGreedy_mem_of_not_unit_mul_sq
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) (p : ℕ) (hp : p.Prime)
    (Q : Quaternion ℚ) (hQ : Q ∈ 𝐇) (hQn : Quaternion.normSq Q = ((p ^ 2 : ℕ) : ℚ))
    (hQU : ¬ IsUnitMulSq Q p) :
    Q ∈ Gq \ 𝐒ᴳ 𝐆ʳ ∧ Q ^ 2 ∈ 𝐒ᴳ 𝐆ʳ \ Gq

end

end MetaMathlibExt
