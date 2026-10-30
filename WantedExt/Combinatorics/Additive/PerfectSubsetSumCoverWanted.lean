/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Perfect subset-sum covers of abelian groups of order a power of two

Greene and Higgins count sets `S` in an abelian group `G` of order `2^n` whose subset
sums cover every element of `G` exactly once (*perfect covers*), and more generally
colored multisets whose subset sums cover every element exactly `m` times (*perfect
`m`-covers*). A colored multiset is an indexed family `s : ι → G`; its subsets are the
index sets `I : Finset ι`, so repeated values are distinguished. The record text fixes
these notions: a perfect cover of a group of order `2^n` is a set of `n` nonzero elements
with distinct subset sums (Lemma 16), a perfect `m`-cover covers each element `m` times
(Lemmas 5 and 8), and `C(G)` is the number of perfect covers of `G`. The relation `a ∼ b`
("`b` is an odd multiple of `a`") and the operator `𝒯` are taken from the paper's Section 3.
-/

namespace MetaMathlibExt

@[expose] public section

namespace PerfectSubsetSumCover

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- `coverCount s g` is the number of index sets `I` with `∑ i ∈ I, s i = g`: the number
of times the colored multiset `s` covers `g` by its subset sums (the empty set covers `0`).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (subset sums,
"covered `m` times", Lemma 8). -/
def coverCount {ι : Type*} [Fintype ι] (s : ι → G) (g : G) : ℕ :=
  (Finset.univ.filter fun I : Finset ι => ∑ i ∈ I, s i = g).card

/-- A colored multiset `s` is a perfect `m`-cover of `G` when every element of `G` is the
subset sum of exactly `m` index sets.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (perfect
`m`-covers, Lemmas 5 and 8). -/
def IsPerfectMCover {ι : Type*} [Fintype ι] (m : ℕ) (s : ι → G) : Prop :=
  ∀ g, coverCount s g = m

instance {ι : Type*} [Fintype ι] [Fintype G] (m : ℕ) (s : ι → G) :
    Decidable (IsPerfectMCover m s) := by
  unfold IsPerfectMCover; infer_instance

/-- A set `S ⊆ G` is a perfect cover of `G` when every element of `G` is the sum of
exactly one subset of `S`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (perfect covers,
Lemma 16). -/
def IsPerfectCover (S : Finset G) : Prop :=
  IsPerfectMCover 1 (fun x : S => (x : G))

instance [Fintype G] (S : Finset G) : Decidable (IsPerfectCover S) := by
  unfold IsPerfectCover; infer_instance

/-- `count G` is the number `C(G)` of perfect covers of `G`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (`C(G)`). -/
noncomputable def count (G : Type*) [AddCommGroup G] [DecidableEq G] : ℕ :=
  Nat.card {S : Finset G // IsPerfectCover S}

/-- For a finite group, `C(G)` is the number of perfect covers in `Finset G`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (`C(G)`). -/
theorem count_eq_card_filter [Fintype G] :
    count G = (Finset.univ.filter fun S : Finset G => IsPerfectCover S).card := by
  rw [count, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Small values: `C(ℤ₂) = 1`, `C(ℤ₄) = 2` (the covers `{1, 2}` and `{2, 3}`), and
`C(ℤ₂ ⊕ ℤ₂) = 3`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorems 2 and 4 at
`n = 1, 2` and `m = 2`. -/
theorem count_small :
    count (ZMod 2) = 1 ∧ count (ZMod 4) = 2 ∧ count (ZMod 2 × ZMod 2) = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [count_eq_card_filter] <;> decide

/-- `{1, 2}` is a perfect cover of `ℤ₄` and `{1, 3}` is not (`1 + 3 = 0`).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (perfect
covers). -/
theorem isPerfectCover_zmod_four :
    IsPerfectCover ({1, 2} : Finset (ZMod 4)) ∧ ¬ IsPerfectCover ({1, 3} : Finset (ZMod 4)) := by
  decide

omit [DecidableEq G] in
/-- `oddCombinations A` is the paper's `𝒯(A)`: the set of combinations `∑_{x ∈ A} c_x x` in
which every integer coefficient `c_x` is `0` or odd.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 3 (the operator `𝒯`). -/
def oddCombinations (A : Finset G) : Set G :=
  {g | ∃ c : G → ℤ, (∀ x ∈ A, c x = 0 ∨ Odd (c x)) ∧ g = ∑ x ∈ A, c x • x}

omit [DecidableEq G] in
/-- `0 ∈ 𝒯(A)` (all coefficients `0`).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 3 (the operator `𝒯`). -/
theorem zero_mem_oddCombinations (A : Finset G) : (0 : G) ∈ oddCombinations A :=
  ⟨0, fun _ _ => Or.inl rfl, by simp⟩

/-- Every element of `A` lies in `𝒯(A)` (coefficient `1` on it, `0` elsewhere).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 3 (the operator `𝒯`). -/
theorem mem_oddCombinations_of_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    x ∈ oddCombinations A := by
  refine ⟨fun y => if y = x then 1 else 0, fun y _ => ?_, ?_⟩
  · by_cases h : y = x <;> simp [h]
  · simp [ite_smul, Finset.sum_ite_eq', hx]

omit [DecidableEq G] in
/-- `𝒯(∅) = {0}`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 3 (the operator `𝒯`). -/
theorem oddCombinations_empty : oddCombinations (∅ : Finset G) = {0} := by
  ext g
  simp [oddCombinations]

end PerfectSubsetSumCover

open PerfectSubsetSumCover

/-- Every abelian group of order `2^n` has a perfect cover, and every nonzero `x` lies in
some perfect cover.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 1
(`jis-2025-25.7.8-thm-1`). -/
public theorem_wanted exists_isPerfectCover_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n) :
    (∃ S : Finset G, IsPerfectCover S) ∧
      ∀ x : G, x ≠ 0 → ∃ S : Finset G, IsPerfectCover S ∧ x ∈ S

/-- The cyclic group `ℤ_{2^n}` has `2^{n(n-1)/2}` perfect covers.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 2
(`jis-2025-25.7.8-thm-2`). -/
public theorem_wanted count_zmod_two_pow (n : ℕ) :
    count (ZMod (2 ^ n)) = 2 ^ (n * (n - 1) / 2)

/-- Rank two: `a_{m,n} = C(ℤ_{2^m} ⊕ ℤ_{2^n})` satisfies, for `m ≥ n ≥ 1`,
`a_{m,n} = 2^{m+n-1} (a_{m-1,n} + 2 a_{m,n-1}) - 3 · 2^{2m+2n-4} a_{m-1,n-1}`, and for each
`n` there is a rational polynomial `p` of degree `n` with
`a_{m,n} = 2^{(m-1)n} 2^{m(m-1)/2} p(m)` for all `m ≥ n`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 3
(`jis-2025-25.7.8-thm-3`). -/
public theorem_wanted count_zmod_two_pow_prod_recurrence :
    (∀ m n : ℕ, 1 ≤ n → n ≤ m →
      (count (ZMod (2 ^ m) × ZMod (2 ^ n)) : ℤ) =
        2 ^ (m + n - 1) * (count (ZMod (2 ^ (m - 1)) × ZMod (2 ^ n)) +
          2 * count (ZMod (2 ^ m) × ZMod (2 ^ (n - 1)))) -
        3 * 2 ^ (2 * m + 2 * n - 4) * count (ZMod (2 ^ (m - 1)) × ZMod (2 ^ (n - 1)))) ∧
    ∀ n : ℕ, ∃ p : Polynomial ℚ, p.natDegree = n ∧ ∀ m : ℕ, n ≤ m →
      (count (ZMod (2 ^ m) × ZMod (2 ^ n)) : ℚ) =
        2 ^ ((m - 1) * n) * 2 ^ (m * (m - 1) / 2) * p.eval (m : ℚ)

/-- One large factor: `b_{m,n} = C((ℤ₂)^m ⊕ ℤ_{2^n})` has
`b_{m,0} · m! = (2^m - 1)(2^m - 2) ⋯ (2^m - 2^{m-1})`; with
`B_{m,k} = 2^m (2^m - 1)(2^m - 2) ⋯ (2^m - 2^{k-1}) / (k+1)!` it satisfies
`b_{m,n} = 2^{m+n-1} b_{m,n-1} + ∑_{k=1}^{m} B_{m,k} 2^{k(m-k)} 2^{(k+1)(n-1)} b_{m-k,n-1}` for
`m, n > 0`; and for each `m` there is a rational polynomial `q` of degree `m` with
`b_{m,n} = 2^{m(n-1)} 2^{n(n-1)/2} q(n)` for all `n ≥ 0` (the first power is an integer
power, `2^{-m}` at `n = 0`).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 4
(`jis-2025-25.7.8-thm-4`). -/
public theorem_wanted count_elementary_prod_zmod_two_pow :
    (∀ m : ℕ, count (Fin m → ZMod 2) * m.factorial =
      ∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i)) ∧
    (∀ m n : ℕ, 0 < m → 0 < n →
      (count ((Fin m → ZMod 2) × ZMod (2 ^ n)) : ℚ) =
        2 ^ (m + n - 1) * count ((Fin m → ZMod 2) × ZMod (2 ^ (n - 1))) +
          ∑ k ∈ Finset.Icc 1 m,
            (2 ^ m * ∏ i ∈ Finset.range k, ((2 : ℚ) ^ m - 2 ^ i)) / (k + 1).factorial *
              2 ^ (k * (m - k)) * 2 ^ ((k + 1) * (n - 1)) *
              count ((Fin (m - k) → ZMod 2) × ZMod (2 ^ (n - 1)))) ∧
    ∀ m : ℕ, ∃ q : Polynomial ℚ, q.natDegree = m ∧ ∀ n : ℕ,
      (count ((Fin m → ZMod 2) × ZMod (2 ^ n)) : ℚ) =
        (2 : ℚ) ^ ((m : ℤ) * ((n : ℤ) - 1)) * 2 ^ (n * (n - 1) / 2) * q.eval (n : ℚ)

/-- Rank-two special cases: `C(ℤ_{2^n} ⊕ ℤ₂) = 2^{n-1} 2^{n(n-1)/2} (n + 2)` for all `n`,
`C(ℤ_{2^n} ⊕ ℤ₄) = 2^{2n-2} 2^{n(n-1)/2} (n^2 + 11n + 4)` for `n ≥ 1`, and
`C(ℤ_{2^n} ⊕ ℤ₈) = 2^{3n-3} 2^{n(n-1)/2} (4n^3 + 108n^2 + 512n - 384)/3` for `n ≥ 2`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 25
(`jis-2025-25.7.8-cor-25`). The record gives no range; the second identity fails at
`n = 0` (`C(ℤ₄) = 2`, formula `1`) and the third at `n = 0, 1` (`C(ℤ₈) = 8`, formula `-16`;
`C(ℤ₂ ⊕ ℤ₈) = 160`, formula `80`), matching Theorem 3's range `m ≥ n`. -/
public theorem_wanted count_zmod_two_pow_prod_small_special :
    (∀ n : ℕ, (count (ZMod (2 ^ n) × ZMod 2) : ℚ) =
      (2 : ℚ) ^ ((n : ℤ) - 1) * 2 ^ (n * (n - 1) / 2) * ((n : ℚ) + 2)) ∧
    (∀ n : ℕ, 1 ≤ n → (count (ZMod (2 ^ n) × ZMod 4) : ℚ) =
      2 ^ (2 * n - 2) * 2 ^ (n * (n - 1) / 2) * ((n : ℚ) ^ 2 + 11 * n + 4)) ∧
    ∀ n : ℕ, 2 ≤ n → (count (ZMod (2 ^ n) × ZMod 8) : ℚ) =
      2 ^ (3 * n - 3) * 2 ^ (n * (n - 1) / 2) *
        ((4 * (n : ℚ) ^ 3 + 108 * n ^ 2 + 512 * n - 384) / 3)

/-- Special cases of Theorem 4: for all `n ≥ 0`,
`C((ℤ₂)^2 ⊕ ℤ_{2^n}) = 2^{2n-2} 2^{n(n-1)/2} (3n^2 + 13n + 12)` and
`C((ℤ₂)^3 ⊕ ℤ_{2^n}) = 2^{3n-3} 2^{n(n-1)/2} (28n^3 + 196n^2 + 392n + 224)`
(integer powers of `2`).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 26
(`jis-2025-25.7.8-cor-26`). The record's third identity, for `(ℤ₂)^4 ⊕ ℤ_{2^n}`, is
omitted: it fails as printed at `n = 1` (`C((ℤ₂)^5) = 83328`, formula `72328`). -/
public theorem_wanted count_elementary_two_three_prod_zmod :
    (∀ n : ℕ, (count ((Fin 2 → ZMod 2) × ZMod (2 ^ n)) : ℚ) =
      (2 : ℚ) ^ (2 * (n : ℤ) - 2) * 2 ^ (n * (n - 1) / 2) * (3 * (n : ℚ) ^ 2 + 13 * n + 12)) ∧
    ∀ n : ℕ, (count ((Fin 3 → ZMod 2) × ZMod (2 ^ n)) : ℚ) =
      (2 : ℚ) ^ (3 * (n : ℤ) - 3) * 2 ^ (n * (n - 1) / 2) *
        (28 * (n : ℚ) ^ 3 + 196 * n ^ 2 + 392 * n + 224)

/-- Adjoining any element `g` to a perfect `m`-cover gives a perfect `2m`-cover.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 5
(`jis-2025-25.7.8-lem-5`). -/
public theorem_wanted isPerfectMCover_cons {G : Type*} [AddCommGroup G] [DecidableEq G]
    {k m : ℕ} {s : Fin k → G} (hs : IsPerfectMCover m s) (g : G) :
    IsPerfectMCover (2 * m) (Fin.cons g s : Fin (k + 1) → G)

/-- If `s` is a perfect `l`-cover of `H ⊕ K` with `|H| = 2^m` and `|K| = 2^n`, its first
coordinates form a perfect `2^n l`-cover of `H` and its second coordinates a perfect
`2^m l`-cover of `K`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 6
(`jis-2025-25.7.8-lem-6`). -/
public theorem_wanted isPerfectMCover_fst_snd {H K : Type*} [AddCommGroup H] [DecidableEq H]
    [Fintype H] [AddCommGroup K] [DecidableEq K] [Fintype K] {m n l : ℕ}
    (hH : Fintype.card H = 2 ^ m) (hK : Fintype.card K = 2 ^ n) {ι : Type*} [Fintype ι]
    {s : ι → H × K} (hs : IsPerfectMCover l s) :
    IsPerfectMCover (2 ^ n * l) (fun i => (s i).1) ∧
      IsPerfectMCover (2 ^ m * l) (fun i => (s i).2)

/-- Let `S` be a perfect cover of an abelian group `G` of order `2^n`, `z ∈ S` and
`S₁ = S \ {z}`. (a) The subset sums of `S₁` cover exactly half of `G`, nothing more than
once. (b) If `S₁` covers `g` and `j ≥ 1`, then `S₁` covers `g + 2jz` but not
`g + (2j - 1)z`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 7
(`jis-2025-25.7.8-lem-7`). -/
public theorem_wanted perfectCover_erase_coverCount {G : Type*} [AddCommGroup G]
    [DecidableEq G] [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n) {S : Finset G}
    (hS : IsPerfectCover S) {z : G} (hz : z ∈ S) :
    ((∀ g : G, coverCount (fun x : S.erase z => (x : G)) g ≤ 1) ∧
      2 * (Finset.univ.filter fun g : G =>
        coverCount (fun x : S.erase z => (x : G)) g = 1).card = 2 ^ n) ∧
    ∀ g : G, 1 ≤ coverCount (fun x : S.erase z => (x : G)) g → ∀ j : ℕ, 1 ≤ j →
      1 ≤ coverCount (fun x : S.erase z => (x : G)) (g + (2 * j) • z) ∧
        coverCount (fun x : S.erase z => (x : G)) (g + (2 * j - 1) • z) = 0

/-- Let `s = (x_1, …, x_{k+1})` be a perfect `2^j`-cover and `S₁ = (x_1, …, x_k)`. If `S₁`
covers `a` exactly `c` times, then it covers `a + x_{k+1}` exactly `2^j - c` times.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 8
(`jis-2025-25.7.8-lem-8`). The paper's `|G| = 2^n` and `k + 1 = j + n` are not needed. -/
public theorem_wanted coverCount_init_add_last {G : Type*} [AddCommGroup G] [DecidableEq G]
    {j k : ℕ} {s : Fin (k + 1) → G} (hs : IsPerfectMCover (2 ^ j) s) (a : G) :
    coverCount (s ∘ Fin.castSucc) (a + s (Fin.last k)) =
      2 ^ j - coverCount (s ∘ Fin.castSucc) a

/-- In the setting of Lemma 8, if `S₁` covers `b` exactly `c` times, then for every integer
`t` it covers `b + 2t x_{k+1}` exactly `c` times and `b + (2t + 1) x_{k+1}` exactly
`2^j - c` times.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 9
(`jis-2025-25.7.8-cor-9`). `t` ranges over `ℤ`. -/
public theorem_wanted coverCount_init_add_zsmul_last {G : Type*} [AddCommGroup G]
    [DecidableEq G] {j k : ℕ} {s : Fin (k + 1) → G} (hs : IsPerfectMCover (2 ^ j) s)
    (b : G) (t : ℤ) :
    coverCount (s ∘ Fin.castSucc) (b + (2 * t) • s (Fin.last k)) =
        coverCount (s ∘ Fin.castSucc) b ∧
      coverCount (s ∘ Fin.castSucc) (b + (2 * t + 1) • s (Fin.last k)) =
        2 ^ j - coverCount (s ∘ Fin.castSucc) b

/-- For nonzero `a, b` in an abelian group `G` of order `2^n`, write `a ∼ b` when `b` is an odd
multiple of `a`. Then `a ∼ b` holds if and only if replacing `a` by `b` in any perfect cover
containing `a` gives a perfect cover, and, for `a ≠ b`, if and only if no perfect cover
contains both `a` and `b`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 10
(`jis-2025-25.7.8-thm-10`). `a, b ≠ 0` added and `a ≠ b` added for (3): for `a = 0, b ≠ 0`
conditions (2) and (3) hold vacuously while (1) fails, and for `a = b ≠ 0` condition (3)
fails (Theorem 1 puts `a` in a perfect cover) while (1) holds. -/
public theorem_wanted oddMultiple_iff_perfectCover_replace {G : Type*} [AddCommGroup G]
    [DecidableEq G] [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n) {a b : G} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    ((∃ j : ℤ, b = (2 * j + 1) • a) ↔
      ∀ S : Finset G, IsPerfectCover S → a ∈ S → IsPerfectCover (insert b (S.erase a))) ∧
    (a ≠ b → ((∃ j : ℤ, b = (2 * j + 1) • a) ↔
      ∀ S : Finset G, IsPerfectCover S → ¬ (a ∈ S ∧ b ∈ S)))

/-- If `(a, s_2, …)` is a perfect `2^k`-cover and `b` is an odd multiple of `a`, then
`(b, s_2, …)` is also a perfect `2^k`-cover.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 11
(`jis-2025-25.7.8-lem-11`). The paper's `|G| = 2^n` and length `n + k` are not needed. -/
public theorem_wanted isPerfectMCover_cons_oddMultiple {G : Type*} [AddCommGroup G]
    [DecidableEq G] {k N : ℕ} {a b : G} {s : Fin N → G}
    (hs : IsPerfectMCover (2 ^ k) (Fin.cons a s : Fin (N + 1) → G))
    (hab : ∃ j : ℤ, b = (2 * j + 1) • a) :
    IsPerfectMCover (2 ^ k) (Fin.cons b s : Fin (N + 1) → G)

/-- A colored multiset `s` in `ℤ_{2^n}` is a perfect `m`-cover for some `m` if and only if
it contains elements of each order `2, 2^2, …, 2^n`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 12
(`jis-2025-25.7.8-thm-12`). The multiplicity `m` is existentially quantified. -/
public theorem_wanted exists_isPerfectMCover_zmod_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → ZMod (2 ^ n)) :
    (∃ m, IsPerfectMCover m s) ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ n → ∃ i, addOrderOf (s i) = 2 ^ j

/-- Every perfect `m`-cover of `ℤ_{2^n}` contains a perfect cover: some subfamily is a
perfect `1`-cover.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 13
(`jis-2025-25.7.8-cor-13`). -/
public theorem_wanted exists_perfectCover_subfamily_zmod {n m : ℕ} {ι : Type*} [Fintype ι]
    {s : ι → ZMod (2 ^ n)} (hs : IsPerfectMCover m s) :
    ∃ T : Finset ι, IsPerfectMCover 1 (fun i : T => s i)

/-- If `s` is a perfect `m`-cover of `H ⊕ ℤ_{2^n}` with `|H|` a power of two, then the
second coordinates of `s` contain elements of each order `2^j`, `1 ≤ j ≤ n`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 14
(`jis-2025-25.7.8-cor-14`). The family has any finite index type (the record reuses `n`
for its length). -/
public theorem_wanted exists_snd_addOrderOf_of_isPerfectMCover {H : Type*} [AddCommGroup H]
    [DecidableEq H] [Fintype H] {r n m : ℕ} (hH : Fintype.card H = 2 ^ r) {ι : Type*}
    [Fintype ι] {s : ι → H × ZMod (2 ^ n)} (hs : IsPerfectMCover m s) :
    ∀ j : ℕ, 1 ≤ j → j ≤ n → ∃ i, addOrderOf (s i).2 = 2 ^ j

/-- Let `S` be a perfect cover of an abelian group of order `2^n`. (a) For disjoint
`A, B ⊆ S`, `𝒯(A) ∩ 𝒯(B) = {0}`. (b) If `A ⊆ S` and `s ∈ S \ A`, then `s ∉ 𝒯(A)`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 15 (a), (b)
(`jis-2025-25.7.8-thm-15`). -/
public theorem_wanted oddCombinations_inter_of_isPerfectCover {G : Type*} [AddCommGroup G]
    [DecidableEq G] [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n) {S : Finset G}
    (hS : IsPerfectCover S) :
    (∀ A B : Finset G, A ⊆ S → B ⊆ S → Disjoint A B →
      oddCombinations A ∩ oddCombinations B = {0}) ∧
    ∀ A : Finset G, A ⊆ S → ∀ s ∈ S, s ∉ A → s ∉ oddCombinations A

/-- For any finite `A ⊆ G`, `𝒯(A)` is a union of `∼`-classes together with `0`: it is closed
under taking odd multiples.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 15 (c)
(`jis-2025-25.7.8-thm-15`). "Union of equivalence classes" is stated as closure under odd
multiples (`0 ∈ 𝒯(A)` is `zero_mem_oddCombinations`). -/
public theorem_wanted zsmul_mem_oddCombinations {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) {g : G} (hg : g ∈ oddCombinations A) (j : ℤ) :
    (2 * j + 1) • g ∈ oddCombinations A

/-- If `x_i ∉ 𝒯({x_1, …, x_{i-1}})` for every `i` (for `i = 1` this says `x_1 ≠ 0`, and for
`i ≥ 2` it forces `x_i ≠ 0`), then all subset sums of `(x_1, …, x_m)` are distinct; if moreover
`|G| = 2^m`, the family is a perfect cover.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 16
(`jis-2025-25.7.8-lem-16`). The paper's "nonzero" hypothesis is the `i = 1` case of `hx`;
distinctness needs no finiteness, and "`m = n`" is `Nat.card G = 2 ^ m`. -/
public theorem_wanted coverCount_le_one_of_not_mem_oddCombinations {G : Type*}
    [AddCommGroup G] [DecidableEq G] {m : ℕ} {x : Fin m → G}
    (hx : ∀ i : Fin m, x i ∉ oddCombinations ((Finset.Iio i).image x)) :
    (∀ g : G, coverCount x g ≤ 1) ∧ (Nat.card G = 2 ^ m → IsPerfectMCover 1 x)

/-- If `H` is a subgroup of order `2^m` of an abelian group `G` of order `2^n`, exactly
`2^{m(n-m)} C(G/H) C(H)` perfect covers of `G` contain a perfect cover of `H`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 17
(`jis-2025-25.7.8-lem-17`). -/
public theorem_wanted card_perfectCover_superset_subgroup {G : Type*} [AddCommGroup G]
    [DecidableEq G] [Fintype G] {n m : ℕ} (hG : Fintype.card G = 2 ^ n) (H : AddSubgroup G)
    (hH : Nat.card H = 2 ^ m) [DecidableEq (G ⧸ H)] :
    Nat.card {S : Finset G // IsPerfectCover S ∧
        ∃ A : Finset H, IsPerfectCover A ∧ A.map (Function.Embedding.subtype _) ⊆ S} =
      2 ^ (m * (n - m)) * count (G ⧸ H) * count H

/-- If `A` is a subset of a perfect cover of an abelian group of order `2^n` and `A` has no
element of order `2`, then `𝒯(A)` does not contain exactly one element of order `2`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 18
(`jis-2025-25.7.8-lem-18`). "No elements of order `2`, or at least two" is stated as "not
exactly one". -/
public theorem_wanted not_existsUnique_addOrderOf_two_mem_oddCombinations {G : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n)
    {S A : Finset G} (hS : IsPerfectCover S) (hA : A ⊆ S) (hA2 : ∀ x ∈ A, addOrderOf x ≠ 2) :
    ¬ ∃! h : G, h ∈ oddCombinations A ∧ addOrderOf h = 2

/-- Every perfect cover of `ℤ_{2^m} ⊕ ℤ_{2^n}` contains an element of order `2`, provided
the group is nontrivial.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 19
(`jis-2025-25.7.8-lem-19`). Hypothesis `0 < m + n` added: the trivial group's perfect
cover is empty. -/
public theorem_wanted exists_addOrderOf_eq_two_of_isPerfectCover {m n : ℕ} (hmn : 0 < m + n)
    {S : Finset (ZMod (2 ^ m) × ZMod (2 ^ n))} (hS : IsPerfectCover S) :
    ∃ x ∈ S, addOrderOf x = 2

/-- For `G = H ⊕ ℤ_{2^n}` with `|H| = 2^m` and `n ≥ 1`, and any `k` with `1 ≤ k ≤ m + 1`, some
perfect cover of `G` has exactly `k` elements whose `ℤ_{2^n}`-coordinate `y` is odd.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 20
(`jis-2025-25.7.8-lem-20`). The setting `G = H ⊕ ℤ_{2^n}`, `|H| = 2^m`, is the one fixed
before the lemma in Section 5; `y` odd means `y.val` odd; `n ≥ 1` added (for `n = 0` no `y` is
odd). -/
public theorem_wanted exists_isPerfectCover_card_odd {H : Type*} [AddCommGroup H]
    [DecidableEq H] [Fintype H] {m n k : ℕ} (hH : Fintype.card H = 2 ^ m) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkm : k ≤ m + 1) :
    ∃ S : Finset (H × ZMod (2 ^ n)), IsPerfectCover S ∧ (S.filter fun x => Odd x.2.val).card = k

/-- For `G = H ⊕ ℤ_{2^n}` with `|H| = 2^m` and `n ≥ 1`, exactly `2^m 2^{n-1} C(H ⊕ ℤ_{2^{n-1}})`
perfect covers of `G` have exactly one element whose `ℤ_{2^n}`-coordinate `y` is odd.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 21
(`jis-2025-25.7.8-lem-21`). "`y_1` odd, all other `y_i` even" is read as "exactly one odd
`y`" for the unordered set; `y` odd means `y.val` odd; `n ≥ 1` added (`ℤ_{2^{n-1}}`). -/
public theorem_wanted card_perfectCover_one_odd {H : Type*} [AddCommGroup H] [DecidableEq H]
    [Fintype H] {m n : ℕ} (hH : Fintype.card H = 2 ^ m) (hn : 1 ≤ n) :
    Nat.card {S : Finset (H × ZMod (2 ^ n)) // IsPerfectCover S ∧
        (S.filter fun x => Odd x.2.val).card = 1} =
      2 ^ m * 2 ^ (n - 1) * count (H × ZMod (2 ^ (n - 1)))

/-- Let `s = (s_1, …, s_{m+n})`, `s_i = (x_i, y_i)`, be a perfect cover of
`(ℤ₂)^m ⊕ ℤ_{2^n}` with `y_1, …, y_{k+1}` odd and the other `y_i` even. Then
`U = span{x_1 + x_2, …, x_1 + x_{k+1}}` and `V = span{x_{k+2}, …, x_{m+n}}` in `(ℤ₂)^m` have
`dim U = k`, `dim V = m - k` and `U ∩ V = 0`.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 23
(`jis-2025-25.7.8-lem-23`). Indices are `0`-based (`i < k + 1` are the odd ones, and
`k + 1 ≤ m + n` makes `y_1, …, y_{k+1}` exist); the perfect cover is an indexed family
(perfect covers have distinct entries); `(ℤ₂)^m = U ⊕ V` is stated as `U ⊔ V = ⊤`. -/
public theorem_wanted perfectCover_odd_even_span {m n k : ℕ} (hk : k + 1 ≤ m + n)
    {s : Fin (m + n) → (Fin m → ZMod 2) × ZMod (2 ^ n)} (hs : IsPerfectMCover 1 s)
    (hodd : ∀ i : Fin (m + n), Odd (s i).2.val ↔ i.val < k + 1) :
    let U := Submodule.span (ZMod 2)
      {v | ∃ i : Fin (m + n), 1 ≤ i.val ∧ i.val < k + 1 ∧ v = (s ⟨0, by omega⟩).1 + (s i).1}
    let V := Submodule.span (ZMod 2) {v | ∃ i : Fin (m + n), k + 1 ≤ i.val ∧ v = (s i).1}
    Module.finrank (ZMod 2) U = k ∧ Module.finrank (ZMod 2) V = m - k ∧ U ⊓ V = ⊥ ∧ U ⊔ V = ⊤

/-- In the setting of Lemma 23, the elements `s_{k+2}, …, s_{m+n}` form a perfect cover of
the subgroup `V ⊕ 2ℤ_{2^n}`: every `(x, y)` with `x ∈ V` and `y` even is the sum of exactly
one subfamily.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 24
(`jis-2025-25.7.8-lem-24`). The family's elements lie in `V ⊕ 2ℤ_{2^n}` by hypothesis and
by definition of `V`; only the covering statement is stated. -/
public theorem_wanted perfectCover_even_tail_coverCount {m n k : ℕ} (hk : k + 1 ≤ m + n)
    {s : Fin (m + n) → (Fin m → ZMod 2) × ZMod (2 ^ n)} (hs : IsPerfectMCover 1 s)
    (hodd : ∀ i : Fin (m + n), Odd (s i).2.val ↔ i.val < k + 1)
    (g : (Fin m → ZMod 2) × ZMod (2 ^ n))
    (hgV : g.1 ∈ Submodule.span (ZMod 2) {v | ∃ i : Fin (m + n), k + 1 ≤ i.val ∧ v = (s i).1})
    (hg2 : Even g.2.val) :
    coverCount (fun i : {i : Fin (m + n) // k + 1 ≤ i.val} => s i) g = 1

end

end MetaMathlibExt
