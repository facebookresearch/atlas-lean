/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.HardyLittlewoodPrimeTuple
public import MathlibExt.NumberTheory.PrimeGapLiminf
public import WantedExt.NumberTheory.PrimeGapBoundsHypotheses

/-!
# Bounded prime-gap literature requests

The chronological catalogue upper rows and the three conditional bounds are
private unproved data. The external PrimeGaps186 development is not imported.
Its three declared analytic/numerical inputs do not become axioms of this library.
Source: Optimization Problems, constants/88a.md, revision
2c1968cd520b60f1cf3cf50749f7285e800e4e15. See Sources/PrimeGapBounds.md for gaps.
-/

@[expose] public section

namespace WantedExt.NumberTheory.PrimeGapBounds

open MathlibExt.NumberTheory

/-- **Zhang's 2014 bound on prime gaps.** Let $p_0 < p_1 < p_2 < \cdots$ be the primes in
increasing order. Then $\liminf_{n \to \infty} (p_{n+1} - p_n) \le 70\,000\,000$, where the
liminf is taken in $\mathbb{N} \cup \{\infty\}$.

Source: Zhang, Annals of Mathematics 179 (2014), 1121-1174; Polymath8b v4, Theorem 1.2. -/
theorem_wanted zhang2014UpperBound : primeGapLiminf ≤ (70000000 : WithTop ℕ)

/-- **Polymath8a bound 4680 on small prime gaps.** Let $p_0 < p_1 < p_2 < \cdots$ be the primes
in increasing order. Then $\liminf_{n \to \infty} (p_{n+1} - p_n) \le 4680$, where the liminf is
taken in $\mathbb{N} \cup \{\infty\}$.

Source: Polymath, Algebra & Number Theory 8 (2014), 2067-2199; Polymath8b v4, Introduction. -/
theorem_wanted polymath8a2014UpperBound : primeGapLiminf ≤ (4680 : WithTop ℕ)

/-- **Maynard's bound 600 on small prime gaps.** Let $p_0 < p_1 < p_2 < \cdots$ be the primes in
increasing order. Then $\liminf_{n \to \infty} (p_{n+1} - p_n) \le 600$, where the liminf is
taken in $\mathbb{N} \cup \{\infty\}$.

The bound was also obtained independently by Tao.

Source: Maynard, Annals of Mathematics 181 (2015), 383-413; Polymath8b v4, Theorem 1.3(i). -/
theorem_wanted maynard2015UpperBound : primeGapLiminf ≤ (600 : WithTop ℕ)

/-- **Polymath8b bound 246 on small prime gaps.** Let $p_0 < p_1 < p_2 < \cdots$ be the primes in
increasing order. Then $\liminf_{n \to \infty} (p_{n+1} - p_n) \le 246$, where the liminf is
taken in $\mathbb{N} \cup \{\infty\}$.

The bound is the one stated in the original arXiv version v4; whether the 2015 erratum affects it
is unresolved.

Source: Polymath8b, arXiv:1407.4897v4, Theorem 1.4(i), DOI 10.1186/s40687-014-0012-7. -/
theorem_wanted polymath8b2014UpperBound : primeGapLiminf ≤ (246 : WithTop ℕ)

/-- **Zhang's 2026 bound of 240 on prime gaps.** Let $p_0 < p_1 < p_2 < \cdots$ be the primes in
increasing order. Then $\liminf_{n \to \infty} (p_{n+1} - p_n) \le 240$, where the liminf is
taken in $\mathbb{N} \cup \{\infty\}$.

Source: Zhang, Zenodo 10.5281/zenodo.22135842, 28 August 2026, as quoted in constants/88a.md. -/
theorem_wanted zhang2026UpperBound : primeGapLiminf ≤ (240 : WithTop ℕ)

/-- **OpenAI's bound 186 on small prime gaps.** Let $p_0 < p_1 < p_2 < \cdots$ be the primes in
increasing order. Then $\liminf_{n \to \infty} (p_{n+1} - p_n) \le 186$, where the liminf is
taken in $\mathbb{N} \cup \{\infty\}$.

Source: OpenAI, Improved short gaps between primes, 30 August 2026, quoted in constants/88a.md. -/
theorem_wanted openai2026UpperBound : primeGapLiminf ≤ (186 : WithTop ℕ)

/-- **Stadlmann's bound 240 on small prime gaps.** Let $p_0 < p_1 < p_2 < \cdots$ be the primes
in increasing order. Then $\liminf_{n \to \infty} (p_{n+1} - p_n) \le 240$, where the liminf is
taken in $\mathbb{N} \cup \{\infty\}$.

Source: Stadlmann, arXiv:2608.31126, 31 August 2026, as quoted in constants/88a.md. -/
theorem_wanted stadlmann2026UpperBound : primeGapLiminf ≤ (240 : WithTop ℕ)

/-- **Maynard's bound under Elliott–Halberstam.** Let $p_0 < p_1 < p_2 < \cdots$ be the primes in
increasing order. If the Elliott–Halberstam conjecture holds at every level $\theta$ with
$0 < \theta < 1$, in Polymath8b's dyadic form, then $\liminf_{n \to \infty} (p_{n+1} - p_n) \le 12$,
where the liminf is taken in $\mathbb{N} \cup \{\infty\}$.

Source: Maynard (2015); Polymath8b v4, Theorem 1.3(iii). -/
theorem_wanted maynardElliottHalberstamUpperBound :
  Polymath8b.ElliottHalberstam → primeGapLiminf ≤ (12 : WithTop ℕ)

/-- **Goldston–Pintz–Yıldırım bound under Elliott–Halberstam.** Let $p_0 < p_1 < p_2 < \cdots$
be the primes in increasing order. If the Elliott–Halberstam conjecture holds at every level
$\theta$ with $0 < \theta < 1$, in Polymath8b's dyadic form, then
$\liminf_{n \to \infty} (p_{n+1} - p_n) \le 16$, where the liminf is taken in
$\mathbb{N} \cup \{\infty\}$.

Source: Goldston-Pintz-Yıldırım (2009); Polymath8b v4, Theorem 1.1. -/
theorem_wanted gpyElliottHalberstamUpperBound :
  Polymath8b.ElliottHalberstam → primeGapLiminf ≤ (16 : WithTop ℕ)

/-- **Polymath8b bound under the generalized Elliott–Halberstam conjecture.** Let
$p_0 < p_1 < p_2 < \cdots$ be the primes in increasing order. If the generalized
Elliott–Halberstam conjecture holds at every level $\theta$ with $0 < \theta < 1$, in Polymath8b's
dyadic form, then $\liminf_{n \to \infty} (p_{n+1} - p_n) \le 6$, where the liminf is taken in
$\mathbb{N} \cup \{\infty\}$.

Source: Polymath8b v4, Theorem 1.4(xii); the 2015 erratum correction is unavailable. -/
theorem_wanted polymath8bGeneralizedElliottHalberstamUpperBound :
  Polymath8b.GeneralizedElliottHalberstam → primeGapLiminf ≤ (6 : WithTop ℕ)

/-- **Two primes in infinitely many translates of an admissible 40-tuple.** Let
$h_1, \dots, h_{40}$ be distinct integers forming an admissible tuple: for every prime $p$, some
residue class modulo $p$ contains none of the $h_i$. Then there are infinitely many natural
numbers $n$ such that at least two of the integers $n + h_1, \dots, n + h_{40}$ are prime.

A negative integer or zero is never counted as prime.

Source: OpenAI (2026), Theorem 1.1, as quoted in the 186 row of constants/88a.md. -/
theorem_wanted openai2026DHL :
  ∀ h : Fin 40 → ℤ, Function.Injective h →
    MetaMathlibExt.IsHardyLittlewoodAdmissible 40 h →
      Set.Infinite {n : ℕ |
        2 ≤ (Finset.univ.filter (fun i : Fin 40 ↦ Nat.Prime ((n : ℤ) + h i).toNat)).card}

/-- **The forty shifts behind the bound 186.** The list of the forty integers
$0, 2, 6, 12, 20, 26, 30, 32, 36, 42, 48, 50, 56, 60, 68, 72, 78, 86, 90, 92, 98, 102, 110,
116, 120, 126, 132, 138, 140, 146, 152, 156, 158, 162, 168, 170, 176, 180, 182, 186$, in this
order.

Source: OpenAI (2026), equation (1.3), retained PrimeGaps186.lean lines 1095-1104. -/
def shifts186 : List ℤ :=
  [0, 2, 6, 12, 20, 26, 30, 32, 36, 42, 48, 50, 56, 60, 68, 72, 78, 86, 90, 92,
    98, 102, 110, 116, 120, 126, 132, 138, 140, 146, 152, 156, 158, 162,
    168, 170, 176, 180, 182, 186]

/-- **The explicit 40-tuple for the gap bound 186.** The $40$-tuple of integers
$h = (h_0, \dots, h_{39})$ whose entries, in order, are $0, 2, 6, 12, 20, 26, 30, 32, 36, 42,
48, 50, 56, 60, 68, 72, 78, 86, 90, 92, 98, 102, 110, 116, 120, 126, 132, 138, 140, 146, 152,
156, 158, 162, 168, 170, 176, 180, 182, 186$.

Source: OpenAI (2026), equation (1.3), and the 186 row of constants/88a.md. -/
def tuple186 (i : Fin 40) : ℤ := shifts186.get ⟨i.val, by simp [shifts186]⟩

/-- **The explicit 40-tuple has distinct entries.** Let $h = (h_0, \dots, h_{39})$ be the
explicit $40$-tuple of integers $(0, 2, 6, \dots, 182, 186)$. Then the entries of $h$ are
pairwise distinct: $h_i = h_j$ implies $i = j$.

Source: the explicit tuple in OpenAI (2026), equation (1.3). -/
theorem tuple186_injective : Function.Injective tuple186 := by decide

/-- **The entries of the explicit 40-tuple lie between 0 and 186.** Let
$h = (h_0, \dots, h_{39})$ be the explicit $40$-tuple of integers $(0, 2, 6, \dots, 182, 186)$.
Then $0 \le h_i \le 186$ for every $i \in \{0, \dots, 39\}$.

Source: the explicit tuple in OpenAI (2026), equation (1.3). -/
theorem tuple186_bounds : ∀ i : Fin 40, 0 ≤ tuple186 i ∧ tuple186 i ≤ 186 := by decide

/-- **The explicit 40-tuple has diameter 186.** Let $h = (h_0, \dots, h_{39})$ be the explicit
$40$-tuple of integers $(0, 2, 6, \dots, 182, 186)$. The largest value in the set
$\{h_0, \dots, h_{39}\}$ minus the smallest value in it equals $186$.

Source: OpenAI (2026), equation (1.3), as quoted in constants/88a.md. -/
theorem tuple186_diameter :
    (Finset.univ.image tuple186).max' (by simp) -
      (Finset.univ.image tuple186).min' (by simp) = 186 := by
  let s := Finset.univ.image tuple186
  have hs : s.Nonempty := by simp [s]
  have hmax : s.max' hs = 186 := by
    apply (Finset.max'_eq_iff s hs 186).2
    constructor
    · exact Finset.mem_image.mpr ⟨39, Finset.mem_univ _, rfl⟩
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨i, _, rfl⟩
      exact (tuple186_bounds i).2
  have hmin : s.min' hs = 0 := by
    apply (Finset.min'_eq_iff s hs 0).2
    constructor
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨i, _, rfl⟩
      exact (tuple186_bounds i).1
  change s.max' hs - s.min' hs = 186
  rw [hmax, hmin]
  norm_num

/-- **The explicit 40-tuple is admissible.** Let $h = (h_0, \dots, h_{39})$ be the explicit
$40$-tuple of integers $(0, 2, 6, \dots, 182, 186)$. Then $h$ is Hardy–Littlewood admissible:
for every prime $p$, the number of residue classes modulo $p$ that contain an entry of $h$ is
not $p$.

Source: OpenAI (2026), equation (1.3); retained PrimeGaps186.lean lines 1109-1117. -/
theorem tuple186_admissible : MetaMathlibExt.IsHardyLittlewoodAdmissible 40 tuple186 := by
  intro p hp
  by_cases h : p < 41
  · have small : ∀ q ∈ Finset.range 41, Nat.Prime q →
        MetaMathlibExt.hardyLittlewoodResidueCount 40 tuple186 q ≠ q := by decide +kernel
    exact small p (Finset.mem_range.mpr h) hp
  · have hcard : MetaMathlibExt.hardyLittlewoodResidueCount 40 tuple186 p ≤ 40 := by
      unfold MetaMathlibExt.hardyLittlewoodResidueCount
      exact Finset.card_image_le.trans (by simp)
    exact ne_of_lt (hcard.trans_lt (by omega))

end WantedExt.NumberTheory.PrimeGapBounds
