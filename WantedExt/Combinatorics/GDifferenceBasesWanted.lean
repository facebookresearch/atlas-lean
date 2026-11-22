/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- The difference representation function `r_{A-A}(x) = |{(a, a') ∈ A × A : a - a' = x}|`
of a finite subset `A` of an abelian group (ordered pairs are counted).

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public def subRepCount {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (x : G) :
    ℕ :=
  ((A ×ˢ A).filter fun p => p.1 - p.2 = x).card

/-- `η_g(n)`: the least size of a finite set `A ⊆ ℤ` that is a `g`-difference basis for
`[n] = {1, …, n}`, i.e. `r_{A-A}(x) ≥ g` for every `x ∈ [n]`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public noncomputable def diffBasisNumber (g n : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset ℤ, A.card = k ∧ ∀ x ∈ Finset.Icc (1 : ℤ) n, g ≤ subRepCount A x}

/-- `η_g(G)`: the least size of a `g`-difference basis of a finite abelian group `G`, i.e. of a
set `A ⊆ G` with `r_{A-A}(x) ≥ g` for every `x ∈ G` (the paper's `η_g(S)` with `S = G`).
Whenever no such finite set exists the value is the junk value `0` (`sInf ∅`): for an infinite
group with `g ≥ 1`, and for a finite group with `g > Nat.card G`, since
`r_{A-A}(x) ≤ |A| ≤ Nat.card G`. For a finite group with `g ≤ Nat.card G` the set `A = G` is a
basis, so the value is the true minimum. The statements below use `g = 1` on finite groups, or
a limit along groups whose order tends to infinity, so they never read the junk value.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Sections 1 and 3. -/
public noncomputable def groupDiffBasisNumber (g : ℕ) (G : Type*) [AddCommGroup G]
    [DecidableEq G] : ℕ :=
  sInf {k | ∃ A : Finset G, A.card = k ∧ ∀ x : G, g ≤ subRepCount A x}

/-- `α_g(n)`: the largest size of a set `A ⊆ [n]` with `r_{A-A}(x) ≤ g` for every nonzero `x`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Sections 1 and 4. -/
public noncomputable def boundedDiffSetNumber (g n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℤ, A ⊆ Finset.Icc (1 : ℤ) n ∧ A.card = k ∧
    ∀ x : ℤ, x ≠ 0 → subRepCount A x ≤ g}

/-- `r_{A-A}(0) = |A|`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public theorem subRepCount_zero {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    subRepCount A 0 = A.card := by
  rw [← Finset.diag_card A, Finset.diag_eq_filter]
  simp only [subRepCount, sub_eq_zero]

private theorem two_le_card_of_subRepCount {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} {x : G} (hx : x ≠ 0) (h : 1 ≤ subRepCount A x) : 2 ≤ A.card := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨h1, h2⟩, hpx⟩ := hp
  have hne : p.1 ≠ p.2 := fun he => hx (by rw [← hpx, he, sub_self])
  exact Finset.one_lt_card.mpr ⟨p.1, h1, p.2, h2, hne⟩

/-- `η_1(1) = 2`: a difference basis for `[1]` needs two elements, and `{0, 1}` is one.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public theorem diffBasisNumber_one_one : diffBasisNumber 1 1 = 2 := by
  have hmem : 2 ∈ {k | ∃ A : Finset ℤ, A.card = k ∧
      ∀ x ∈ Finset.Icc (1 : ℤ) (1 : ℕ), 1 ≤ subRepCount A x} := by
    refine ⟨{0, 1}, by decide, fun x hx => ?_⟩
    have : x = 1 := by simp at hx; omega
    subst this
    decide
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨2, hmem⟩ ?_)
  rintro k ⟨A, rfl, hA⟩
  exact two_le_card_of_subRepCount one_ne_zero (hA 1 (by simp))

/-- `η_1(ℤ/3ℤ) = 2`: `{0, 1}` has differences `0, 1, 2`, and one element is not enough.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 3. -/
public theorem groupDiffBasisNumber_one_zmod_three : groupDiffBasisNumber 1 (ZMod 3) = 2 := by
  have hmem : 2 ∈ {k | ∃ A : Finset (ZMod 3), A.card = k ∧
      ∀ x : ZMod 3, 1 ≤ subRepCount A x} := ⟨{0, 1}, by decide, by decide⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨2, hmem⟩ ?_)
  rintro k ⟨A, rfl, hA⟩
  exact two_le_card_of_subRepCount (by decide) (hA 1)

/-- `α_g(n) ≤ n`, since the sets are subsets of `[n]`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 4. -/
public theorem boundedDiffSetNumber_le (g n : ℕ) : boundedDiffSetNumber g n ≤ n := by
  refine csSup_le ⟨0, ∅, by simp, by simp, by simp [subRepCount]⟩ ?_
  rintro k ⟨A, hA, rfl, -⟩
  simpa using Finset.card_le_card hA

/-- `α_g(1) = 1`: the singleton `{1}` has no nonzero differences.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 4. -/
public theorem boundedDiffSetNumber_one (g : ℕ) : boundedDiffSetNumber g 1 = 1 := by
  refine le_antisymm (boundedDiffSetNumber_le g 1) (le_csSup ⟨1, ?_⟩ ?_)
  · rintro k ⟨A, hA, rfl, -⟩
    simpa using Finset.card_le_card hA
  · refine ⟨{1}, by simp, rfl, fun x hx => ?_⟩
    have : subRepCount ({1} : Finset ℤ) x = 0 := by
      simp [subRepCount, Finset.filter_singleton, Ne.symm hx]
    omega

/-- The trivial lower bound `η_g(n)/√n ≥ √(2g)` for `n > 1`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 1 (`integers-2025-A77-lem-1`). -/
public theorem_wanted sqrt_two_mul_le_diffBasisNumber_div_sqrt (g n : ℕ) (hn : 1 < n) :
    Real.sqrt (2 * g) ≤ (diffBasisNumber g n : ℝ) / Real.sqrt n

/-- The Rédei–Rényi set: with `k = ⌈√n⌉`, the set
`B_n = {1, …, k - 1} ∪ {k, 2k, …, k², (k + 1)k}` has `2k` elements and is a `1`-difference
basis for `[n]` (`n ≥ 1`).

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 2 (`integers-2025-A77-lem-2`). -/
public theorem_wanted redeiRenyi_diffBasis (n : ℕ) (hn : 0 < n) :
    let k : ℕ := ⌈Real.sqrt n⌉₊
    let B : Finset ℤ :=
      Finset.Icc 1 ((k : ℤ) - 1) ∪ (Finset.Icc (1 : ℤ) (k + 1)).image (· * (k : ℤ))
    B.card = 2 * k ∧ ∀ x ∈ Finset.Icc (1 : ℤ) n, 1 ≤ subRepCount B x

/-- The upper bound `η_g(n)/√n ≤ 2(1 + 1/√n) g`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Corollary 1 (`integers-2025-A77-cor-1`). -/
public theorem_wanted diffBasisNumber_div_sqrt_le (g n : ℕ) :
    (diffBasisNumber g n : ℝ) / Real.sqrt n ≤ 2 * (1 + 1 / Real.sqrt n) * g

/-- `η_1(n) ≤ η_g(n) ≤ g η_1(n)` for `n > 1` and `g ≥ 1`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Corollary 2 (`integers-2025-A77-cor-2`). -/
public theorem_wanted diffBasisNumber_one_le_and_le_mul (g n : ℕ) (hn : 1 < n) (hg : 1 ≤ g) :
    diffBasisNumber 1 n ≤ diffBasisNumber g n ∧ diffBasisNumber g n ≤ g * diffBasisNumber 1 n

/-- Kravitz's question answered: for every `g ≥ 1` the limit of `η_g(n)/√n` exists and is a
positive real number.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 1 (`integers-2025-A77-thm-1`). -/
public theorem_wanted tendsto_diffBasisNumber_div_sqrt (g : ℕ) (hg : 0 < g) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (diffBasisNumber g n : ℝ) / Real.sqrt n) atTop (𝓝 c)

/-- The Singer product construction: if `a₀, …, a_q ∈ [m]`, `m = q² + q + 1`, form a Singer
difference set modulo `m` and `B` is a `g`-difference basis for `[v]`, then
`F = {a_i + m b : 0 ≤ i ≤ q, b ∈ B}` is a `g`-difference basis for `[mv]`. Corrected reading: all
`q + 1` Singer elements are used (the paper prints `1 ≤ i ≤ q`, which fails, see the audit row).

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 4 (`integers-2025-A77-lem-4`). -/
public theorem_wanted singer_product_diffBasis (g q v : ℕ) (a : Fin (q + 1) → ℤ)
    (ha : ∀ i, a i ∈ Finset.Icc (1 : ℤ) (q ^ 2 + q + 1))
    (hsinger : ∀ r ∈ Finset.Icc (1 : ℤ) (q ^ 2 + q),
      ∃! ij : Fin (q + 1) × Fin (q + 1),
        ij.1 ≠ ij.2 ∧ a ij.1 - a ij.2 ≡ r [ZMOD (q ^ 2 + q + 1 : ℤ)])
    (B : Finset ℤ) (hB : ∀ x ∈ Finset.Icc (1 : ℤ) v, g ≤ subRepCount B x) :
    ∀ s ∈ Finset.Icc (1 : ℤ) ((q ^ 2 + q + 1) * v),
      g ≤ subRepCount
        ((Finset.univ ×ˢ B).image fun ib : Fin (q + 1) × ℤ => a ib.1 + (q ^ 2 + q + 1) * ib.2) s

/-- If `q` is prime and `√(n/v) ≤ q`, then `η_g(n) ≤ (q + 1) η_g(v)`. Corrected reading: the
paper prints the factor `q`, obtained from the misprinted Lemma 4; its proof gives `q + 1`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Corollary 3 (`integers-2025-A77-cor-3`). -/
public theorem_wanted diffBasisNumber_le_succ_mul (g q n v : ℕ) (hq : q.Prime)
    (hn : n ≤ q ^ 2 * v) :
    diffBasisNumber g n ≤ (q + 1) * diffBasisNumber g v

/-- Products of difference bases: if `A_i` is a `g_i`-difference basis of the abelian group
`G_i`, then `A₁ × A₂` is a `g₁g₂`-difference basis of `G₁ × G₂`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 5 (`integers-2025-A77-lem-5`). -/
public theorem_wanted subRepCount_prod_ge {G₁ G₂ : Type*} [AddCommGroup G₁] [AddCommGroup G₂]
    [DecidableEq G₁] [DecidableEq G₂] (g₁ g₂ : ℕ) (A₁ : Finset G₁) (A₂ : Finset G₂)
    (h₁ : ∀ x, g₁ ≤ subRepCount A₁ x) (h₂ : ∀ x, g₂ ≤ subRepCount A₂ x) :
    ∀ x : G₁ × G₂, g₁ * g₂ ≤ subRepCount (A₁ ×ˢ A₂) x

/-- For a prime `p`, `η_1(𝔽_p) ≤ 2⌈√p⌉` (reduce the Rédei–Rényi set modulo `p`).

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, equation (5) after Lemma 5 (`integers-2025-A77-lem-5`). -/
public theorem_wanted groupDiffBasisNumber_zmod_le (p : ℕ) [Fact p.Prime] :
    groupDiffBasisNumber 1 (ZMod p) ≤ 2 * ⌈Real.sqrt p⌉₊

/-- For a finite field `K` of odd order `q`, `η_1(K × K) ≤ q + η_1(K)`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 6 (`integers-2025-A77-lem-6`). -/
public theorem_wanted groupDiffBasisNumber_prod_self_le {K : Type*} [Field K] [Finite K]
    [DecidableEq K] (hK : ringChar K ≠ 2) :
    groupDiffBasisNumber 1 (K × K) ≤ Nat.card K + groupDiffBasisNumber 1 K

/-- For every finite field `K` of order `q`, `η_1(K) ≤ 100 √q`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 7 (`integers-2025-A77-lem-7`). -/
public theorem_wanted groupDiffBasisNumber_le_hundred_sqrt {K : Type*} [Field K] [Finite K]
    [DecidableEq K] :
    (groupDiffBasisNumber 1 K : ℝ) ≤ 100 * Real.sqrt (Nat.card K)

open Classical in
/-- For an odd prime `p`, `η_1(𝔽_{p^t} × 𝔽_{p^t}) = (1 + o(1)) p^t` as `t → ∞`. Restricted to odd
`p`: for `p = 2` the claim fails (see the audit row).

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 8 (`integers-2025-A77-lem-8`). -/
public theorem_wanted tendsto_groupDiffBasisNumber_galoisField_prod (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) :
    Tendsto (fun t : ℕ =>
        (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) / (p : ℝ) ^ t)
      atTop (𝓝 1)

/-- For an odd prime `p` and `g ≥ 1`, the even and odd limits of `η_g(𝔽_p^n)/√(p^n)` exist and
are positive real numbers.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 2 (`integers-2025-A77-thm-2`). -/
public theorem_wanted tendsto_groupDiffBasisNumber_even_odd (p g : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hg : 0 < g) :
    (∃ Le : ℝ, 0 < Le ∧ Tendsto (fun k : ℕ =>
        (groupDiffBasisNumber g (Fin (2 * k) → ZMod p) : ℝ) / Real.sqrt ((p : ℝ) ^ (2 * k)))
      atTop (𝓝 Le)) ∧
    (∃ Lo : ℝ, 0 < Lo ∧ Tendsto (fun k : ℕ =>
        (groupDiffBasisNumber g (Fin (2 * k + 1) → ZMod p) : ℝ) /
          Real.sqrt ((p : ℝ) ^ (2 * k + 1)))
      atTop (𝓝 Lo))

/-- The Bose–Chowla set avoids the order-`g` subgroup: let `K` be a field of order `q²`, `θ` a
generator of `Kˣ`, and `B_q = {a ∈ ℤ/(q² - 1) : θ^a - θ ∈ 𝔽_q}` (with `𝔽_q = {x : x^q = x}`).
If `g ∣ q - 1` and `H` is the subgroup generated by `(q² - 1)/g`, then `(B_q - B_q) ∩ H = {0}`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 9 (`integers-2025-A77-lem-9`), quoting Bose–Chowla and
Brandão–Debarre–Tait / Gómez–Trujillo–Tait. -/
public theorem_wanted boseChowla_sub_mem_subgroup_eq {K : Type*} [Field K] [Finite K]
    (q g : ℕ) (hK : Nat.card K = q ^ 2) (hgq : g ∣ q - 1) (θ : K)
    (hθ : IsPrimitiveRoot θ (q ^ 2 - 1)) (a b : ℕ) (ha : a < q ^ 2 - 1) (hb : b < q ^ 2 - 1)
    (hBa : (θ ^ a - θ) ^ q = θ ^ a - θ) (hBb : (θ ^ b - θ) ^ q = θ ^ b - θ)
    (hab : (((q ^ 2 - 1) / g : ℕ) : ℤ) ∣ (a : ℤ) - b) :
    a = b

/-- Upper bound: for fixed `g ≥ 1`, `α_g(n) ≤ (1 + o(1)) √(gn)`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Proposition 1 (`integers-2025-A77-prop-1`). -/
public theorem_wanted boundedDiffSetNumber_le_one_add_mul_sqrt (g : ℕ) (hg : 0 < g) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (boundedDiffSetNumber g n : ℝ) ≤ (1 + ε) * Real.sqrt (g * n)

/-- Lower bound construction: for fixed `g ≥ 1` there are sets `A_n ⊆ [n]` with
`r_{A_n - A_n}(x) ≤ g` for all nonzero `x` and `|A_n| = (1 - o(1)) √(gn)`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Proposition 2 (`integers-2025-A77-prop-2`). -/
public theorem_wanted exists_boundedDiffSet_card_div_sqrt_tendsto (g : ℕ) (hg : 0 < g) :
    ∃ A : ℕ → Finset ℤ,
      (∀ n, A n ⊆ Finset.Icc (1 : ℤ) n ∧ ∀ x : ℤ, x ≠ 0 → subRepCount (A n) x ≤ g) ∧
      Tendsto (fun n : ℕ => ((A n).card : ℝ) / Real.sqrt (g * n)) atTop (𝓝 1)

/-- For every `g ≥ 1`, `α_g(n) = (1 + o_g(1)) √(gn)` as `n → ∞`.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 3 (`integers-2025-A77-thm-3`). -/
public theorem_wanted tendsto_boundedDiffSetNumber_div_sqrt (g : ℕ) (hg : 0 < g) :
    Tendsto (fun n : ℕ => (boundedDiffSetNumber g n : ℝ) / Real.sqrt (g * n)) atTop (𝓝 1)

end

end MetaMathlibExt
