/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.PermutationStatistics
public import WantedExt.Combinatorics.Enumerative.OddFibonacciWanted

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

/-- No separable king permutations of length `n ≥ 2` exist: every permutation of length
`n ≥ 2` in which adjacent entries never differ by exactly `1` contains the pattern `2413`
or the pattern `3142`.

A king permutation is one with `|σ(i + 1) - σ(i)| ≠ 1` for all adjacent positions (the
standard definition; these are counted by OEIS A002464), and a separable permutation is one
avoiding both `2413` and `3142`; the conclusion is the negation of separability. Patterns
are zero-based value functions for the classical containment
`MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted.HasPattern`, so `2413` is
`![1, 3, 0, 2]` and `3142` is `![2, 0, 3, 1]`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Theorem 2 (`integers-2026-A59-thm-2`). -/
public theorem_wanted king_permutation_not_separable (n : ℕ) (hn : 2 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (hking : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i) :
    HasPattern σ ![1, 3, 0, 2] ∨ HasPattern σ ![2, 0, 3, 1]

/-- Classical part of Theorem 1: for `n ≥ 2` no king permutation of length `n` avoids any of
the classical patterns `12`, `21`, `132`, `213`, `231`, `312`; that is, every permutation of
length `n ≥ 2` whose adjacent entries never differ by exactly `1` contains each of them.
Patterns are zero-based value functions for `HasPattern`, so `132` is `![0, 2, 1]`. The
nine partially ordered patterns in the theorem's pattern set are not stated (their diagrams
are lost in the extracted record).

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Theorem 1 (`integers-2026-A59-thm-1`). -/
public theorem_wanted king_permutation_hasPattern_classical (n : ℕ) (hn : 2 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (hking : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i) :
    HasPattern σ ![0, 1] ∧ HasPattern σ ![1, 0] ∧ HasPattern σ ![0, 2, 1] ∧
      HasPattern σ ![1, 0, 2] ∧ HasPattern σ ![1, 2, 0] ∧ HasPattern σ ![2, 0, 1]

/-- A king permutation: adjacent entries never differ by exactly `1`, i.e.
`|σ(i + 1) - σ(i)| > 1` for all adjacent positions.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.3. -/
def IsKingPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, (j : ℕ) = i + 1 → (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i

/-- The number of ascents `asc(σ)`: positions `i` with `σ(i) < σ(i + 1)`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permAscentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∃ j : Fin n, (j : ℕ) = i + 1 ∧ σ i < σ j).card

/-- The number of descents `des(σ)`: positions `i` with `σ(i) > σ(i + 1)`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permDescentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∃ j : Fin n, (j : ℕ) = i + 1 ∧ σ j < σ i).card

/-- The statistics of `123`: two ascents, no descent, three left-to-right maxima, one
right-to-left maximum, one left-to-right minimum, three right-to-left minima.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
theorem permStats_one_fin_three :
    permAscentCount (1 : Equiv.Perm (Fin 3)) = 2 ∧ permDescentCount (1 : Equiv.Perm (Fin 3)) = 0 ∧
      permLeftToRightMaxCount (1 : Equiv.Perm (Fin 3)) = 3 ∧
      permRightToLeftMaxCount (1 : Equiv.Perm (Fin 3)) = 1 ∧
      permLeftToRightMinCount (1 : Equiv.Perm (Fin 3)) = 1 ∧
      permRightToLeftMinCount (1 : Equiv.Perm (Fin 3)) = 3 := by
  decide

/-- The statistics of `321`: no ascent, two descents, one left-to-right maximum, three
right-to-left maxima, three left-to-right minima, one right-to-left minimum.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
theorem permStats_revPerm_fin_three :
    permAscentCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 0 ∧
      permDescentCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 2 ∧
      permLeftToRightMaxCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 1 ∧
      permRightToLeftMaxCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 3 ∧
      permLeftToRightMinCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 3 ∧
      permRightToLeftMinCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 1 := by
  decide

/-- `σ` contains the flat partially ordered pattern of size `4` whose label `j + 1` lies below the
other three labels (which are mutually incomparable): there are positions `i₀ < i₁ < i₂ < i₃`
with `σ(i_j) < σ(i_m)` for every `m ≠ j`. For `j = 0, 1, 2, 3` these are the paper's POPs
`P₁, P₂, P₃, P₄` (Table 1).

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.1 and Table 1. -/
def ContainsFlatPOPBelow {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin 4) : Prop :=
  ∃ f : Fin 4 ↪o Fin n, ∀ m, m ≠ j → σ (f j) < σ (f m)

/-- `σ` contains the flat partially ordered pattern of size `4` whose label `j + 1` lies above the
other three labels: there are positions `i₀ < i₁ < i₂ < i₃` with `σ(i_m) < σ(i_j)` for every
`m ≠ j`. For `j = 0, 1, 2, 3` these are the paper's POPs `Q₁, Q₂, Q₃, Q₄` (Table 1; `Q_k` is the
complement of `P_k`).

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.1 and Table 1. -/
def ContainsFlatPOPAbove {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin 4) : Prop :=
  ∃ f : Fin 4 ↪o Fin n, ∀ m, m ≠ j → σ (f m) < σ (f j)

/-- A permutation containing a flat POP of size `4` has length at least `4`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.1. -/
theorem four_le_of_containsFlatPOPBelow {n : ℕ} {σ : Equiv.Perm (Fin n)} {j : Fin 4}
    (h : ContainsFlatPOPBelow σ j) : 4 ≤ n := by
  obtain ⟨f, -⟩ := h
  simpa using Fintype.card_le_of_embedding f.toEmbedding

/-- A permutation containing a flat POP of size `4` has length at least `4`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.1. -/
theorem four_le_of_containsFlatPOPAbove {n : ℕ} {σ : Equiv.Perm (Fin n)} {j : Fin 4}
    (h : ContainsFlatPOPAbove σ j) : 4 ≤ n := by
  obtain ⟨f, -⟩ := h
  simpa using Fintype.card_le_of_embedding f.toEmbedding

open Classical in
/-- The generating function `A_P(x, p, q, u, v) = ∑_{n ≥ 0} ∑_{σ ∈ K_n(P)}
x^n p^{asc σ} q^{des σ} u^{lmax σ} v^{rmax σ}` for `P = P_{j+1}` (king permutations avoiding
`ContainsFlatPOPBelow · j`), with `p, q, u, v` the variables `X 0, X 1, X 2, X 3`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.4. -/
noncomputable def kingFlatPOPBelowGF (j : Fin 4) : PowerSeries (MvPolynomial (Fin 4) ℤ) :=
  PowerSeries.mk fun n =>
    ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => IsKingPerm σ ∧ ¬ ContainsFlatPOPBelow σ j),
      MvPolynomial.X 0 ^ permAscentCount σ * MvPolynomial.X 1 ^ permDescentCount σ *
        MvPolynomial.X 2 ^ permLeftToRightMaxCount σ * MvPolynomial.X 3 ^ permRightToLeftMaxCount σ

open Classical in
/-- The generating function `Ā_Q(x, p, q, s, t) = ∑_{n ≥ 0} ∑_{σ ∈ K_n(Q)}
x^n p^{asc σ} q^{des σ} s^{lmin σ} t^{rmin σ}` for `Q = Q_{j+1}` (king permutations avoiding
`ContainsFlatPOPAbove · j`), with `p, q, s, t` the variables `X 0, X 1, X 2, X 3`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.4. -/
noncomputable def kingFlatPOPAboveGF (j : Fin 4) : PowerSeries (MvPolynomial (Fin 4) ℤ) :=
  PowerSeries.mk fun n =>
    ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => IsKingPerm σ ∧ ¬ ContainsFlatPOPAbove σ j),
      MvPolynomial.X 0 ^ permAscentCount σ * MvPolynomial.X 1 ^ permDescentCount σ *
        MvPolynomial.X 2 ^ permLeftToRightMinCount σ * MvPolynomial.X 3 ^ permRightToLeftMinCount σ

/-- The empty permutation contributes the constant term `1` of `A_P`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.4 and proof of Theorem 3. -/
theorem constantCoeff_kingFlatPOPBelowGF (j : Fin 4) :
    PowerSeries.constantCoeff (kingFlatPOPBelowGF j) = 1 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, kingFlatPOPBelowGF, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
  · simp [permAscentCount, permDescentCount, permLeftToRightMaxCount, permRightToLeftMaxCount]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i => i.elim0, fun h => by simpa using four_le_of_containsFlatPOPBelow h⟩
  · intro b _ hb
    exact absurd (Subsingleton.elim b 1) hb

/-- The empty permutation contributes the constant term `1` of `Ā_Q`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1.4 and proof of Theorem 3. -/
theorem constantCoeff_kingFlatPOPAboveGF (j : Fin 4) :
    PowerSeries.constantCoeff (kingFlatPOPAboveGF j) = 1 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, kingFlatPOPAboveGF, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
  · simp [permAscentCount, permDescentCount, permLeftToRightMinCount, permRightToLeftMinCount]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i => i.elim0, fun h => by simpa using four_le_of_containsFlatPOPAbove h⟩
  · intro b _ hb
    exact absurd (Subsingleton.elim b 1) hb

/-- Theorem 3: for `P₁` (label `1` below labels `2, 3, 4`), `A_{P₁} = A / B`, stated as
`B · A_{P₁} = A` (`B` has constant term `-1`, so this determines `A_{P₁}`), where
`A = -1 - uvx + pqvx² + (pq²v + pquv²)x³ + (p²q²v² + pq³v² + pq²uv² - p²qu²v² - pq²u²v²)x⁴
+ (p²q³v² - p²q²u²v² + 2p²q³v³ + pq⁴v³ - 2p²q²u²v³ - pq³u²v³)x⁵
+ (2p²q⁴v³ - 2p²q³u²v³ + p²q⁴v⁴ - p²q³u²v⁴)x⁶ + (p²q⁵v⁴ - p²q⁴u²v⁴)x⁷` and
`B = -1 + pqvx² + pq²vx³ + (p²q²v² + pq³v²)x⁴ + (p²q³v² + 2p²q³v³ + pq⁴v³)x⁵
+ (2p²q⁴v³ + p²q⁴v⁴)x⁶ + p²q⁵v⁴x⁷`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Theorem 3. -/
theorem_wanted kingFlatPOPBelowGF_zero_eq :
    let p : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 0
    let q : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 1
    let u : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 2
    let v : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 3
    let x : PowerSeries (MvPolynomial (Fin 4) ℤ) := PowerSeries.X
    let c : MvPolynomial (Fin 4) ℤ → PowerSeries (MvPolynomial (Fin 4) ℤ) := PowerSeries.C
    (c (-1) + c (p * q * v) * x ^ 2 + c (p * q ^ 2 * v) * x ^ 3 +
        c (p ^ 2 * q ^ 2 * v ^ 2 + p * q ^ 3 * v ^ 2) * x ^ 4 +
        c (p ^ 2 * q ^ 3 * v ^ 2 + 2 * p ^ 2 * q ^ 3 * v ^ 3 + p * q ^ 4 * v ^ 3) * x ^ 5 +
        c (2 * p ^ 2 * q ^ 4 * v ^ 3 + p ^ 2 * q ^ 4 * v ^ 4) * x ^ 6 +
        c (p ^ 2 * q ^ 5 * v ^ 4) * x ^ 7) * kingFlatPOPBelowGF 0 =
      c (-1) - c (u * v) * x + c (p * q * v) * x ^ 2 +
        c (p * q ^ 2 * v + p * q * u * v ^ 2) * x ^ 3 +
        c (p ^ 2 * q ^ 2 * v ^ 2 + p * q ^ 3 * v ^ 2 + p * q ^ 2 * u * v ^ 2 -
          p ^ 2 * q * u ^ 2 * v ^ 2 - p * q ^ 2 * u ^ 2 * v ^ 2) * x ^ 4 +
        c (p ^ 2 * q ^ 3 * v ^ 2 - p ^ 2 * q ^ 2 * u ^ 2 * v ^ 2 + 2 * p ^ 2 * q ^ 3 * v ^ 3 +
          p * q ^ 4 * v ^ 3 - 2 * p ^ 2 * q ^ 2 * u ^ 2 * v ^ 3 -
            p * q ^ 3 * u ^ 2 * v ^ 3) * x ^ 5 +
        c (2 * p ^ 2 * q ^ 4 * v ^ 3 - 2 * p ^ 2 * q ^ 3 * u ^ 2 * v ^ 3 + p ^ 2 * q ^ 4 * v ^ 4 -
          p ^ 2 * q ^ 3 * u ^ 2 * v ^ 4) * x ^ 6 +
        c (p ^ 2 * q ^ 5 * v ^ 4 - p ^ 2 * q ^ 4 * u ^ 2 * v ^ 4) * x ^ 7

/-- Theorem 4: for `P₂` (label `2` below labels `1, 3, 4`), `A_{P₂} = A / B`, stated as
`B · A_{P₂} = A` (`B` has constant term `-1`), where
`A = -1 - uvx + (pqu + pquv)x² + (p²quv + pqu²v + pqu²v²)x³
+ (p²q²uv + p³qu²v - p²q²u²v + p²q²uv²)x⁴ + (p³q²u²v + p²q³uv² + p³q²u²v² - p²q²u³v²)x⁵
+ p³q³u²v²x⁶` and `B = -1 + (pqu + pquv)x² + p²quvx³ + (p²q²uv + p³qu²v - p²q²u²v + p²q²uv²)x⁴
+ (p³q²u²v + p²q³uv² + p³q²u²v²)x⁵ + p³q³u²v²x⁶`.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Theorem 4. -/
theorem_wanted kingFlatPOPBelowGF_one_eq :
    let p : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 0
    let q : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 1
    let u : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 2
    let v : MvPolynomial (Fin 4) ℤ := MvPolynomial.X 3
    let x : PowerSeries (MvPolynomial (Fin 4) ℤ) := PowerSeries.X
    let c : MvPolynomial (Fin 4) ℤ → PowerSeries (MvPolynomial (Fin 4) ℤ) := PowerSeries.C
    (c (-1) + c (p * q * u + p * q * u * v) * x ^ 2 + c (p ^ 2 * q * u * v) * x ^ 3 +
        c (p ^ 2 * q ^ 2 * u * v + p ^ 3 * q * u ^ 2 * v - p ^ 2 * q ^ 2 * u ^ 2 * v +
          p ^ 2 * q ^ 2 * u * v ^ 2) * x ^ 4 +
        c (p ^ 3 * q ^ 2 * u ^ 2 * v + p ^ 2 * q ^ 3 * u * v ^ 2 + p ^ 3 * q ^ 2 * u ^ 2 * v ^ 2) *
          x ^ 5 +
        c (p ^ 3 * q ^ 3 * u ^ 2 * v ^ 2) * x ^ 6) * kingFlatPOPBelowGF 1 =
      c (-1) - c (u * v) * x + c (p * q * u + p * q * u * v) * x ^ 2 +
        c (p ^ 2 * q * u * v + p * q * u ^ 2 * v + p * q * u ^ 2 * v ^ 2) * x ^ 3 +
        c (p ^ 2 * q ^ 2 * u * v + p ^ 3 * q * u ^ 2 * v - p ^ 2 * q ^ 2 * u ^ 2 * v +
          p ^ 2 * q ^ 2 * u * v ^ 2) * x ^ 4 +
        c (p ^ 3 * q ^ 2 * u ^ 2 * v + p ^ 2 * q ^ 3 * u * v ^ 2 + p ^ 3 * q ^ 2 * u ^ 2 * v ^ 2 -
          p ^ 2 * q ^ 2 * u ^ 3 * v ^ 2) * x ^ 5 +
        c (p ^ 3 * q ^ 3 * u ^ 2 * v ^ 2) * x ^ 6

/-- For `P₄` (label `4` below labels `1, 2, 3`), `A_{P₄}(x, p, q, u, v) = A_{P₁}(x, q, p, v, u)`.
The substitution of variables is
`MvPolynomial.rename` along `Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3` applied coefficientwise.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 1. -/
theorem_wanted kingFlatPOPBelowGF_three_eq_rename :
    kingFlatPOPBelowGF 3 =
      PowerSeries.map (MvPolynomial.rename
          ⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))).toRingHom
        (kingFlatPOPBelowGF 0)

/-- For `Q₁` (label `1` above labels `2, 3, 4`), `Ā_{Q₁}(x, p, q, s, t) = A_{P₁}(x, q, p, s, t)`.
The substitution of variables is
`MvPolynomial.rename` along `Equiv.swap (0 : Fin 4) 1` applied coefficientwise.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 2. -/
theorem_wanted kingFlatPOPAboveGF_zero_eq_rename :
    kingFlatPOPAboveGF 0 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (0 : Fin 4) 1)).toRingHom
        (kingFlatPOPBelowGF 0)

/-- For `Q₄` (label `4` above labels `1, 2, 3`), `Ā_{Q₄}(x, p, q, s, t) = A_{P₁}(x, p, q, t, s)`.
The substitution of variables is
`MvPolynomial.rename` along `Equiv.swap (2 : Fin 4) 3` applied coefficientwise.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 3. -/
theorem_wanted kingFlatPOPAboveGF_three_eq_rename :
    kingFlatPOPAboveGF 3 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (2 : Fin 4) 3)).toRingHom
        (kingFlatPOPBelowGF 0)

/-- For `P₃` (label `3` below labels `1, 2, 4`), `A_{P₃}(x, p, q, u, v) = A_{P₂}(x, q, p, v, u)`.
The substitution of variables is
`MvPolynomial.rename` along `Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3` applied coefficientwise.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 4. -/
theorem_wanted kingFlatPOPBelowGF_two_eq_rename :
    kingFlatPOPBelowGF 2 =
      PowerSeries.map (MvPolynomial.rename
          ⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))).toRingHom
        (kingFlatPOPBelowGF 1)

/-- For `Q₂` (label `2` above labels `1, 3, 4`), `Ā_{Q₂}(x, p, q, s, t) = A_{P₂}(x, q, p, s, t)`.
The substitution of variables is
`MvPolynomial.rename` along `Equiv.swap (0 : Fin 4) 1` applied coefficientwise.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 5. -/
theorem_wanted kingFlatPOPAboveGF_one_eq_rename :
    kingFlatPOPAboveGF 1 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (0 : Fin 4) 1)).toRingHom
        (kingFlatPOPBelowGF 1)

/-- For `Q₃` (label `3` above labels `1, 2, 4`), `Ā_{Q₃}(x, p, q, s, t) = A_{P₂}(x, p, q, t, s)`.
The substitution of variables is
`MvPolynomial.rename` along `Equiv.swap (2 : Fin 4) 3` applied coefficientwise.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Corollary 6. -/
theorem_wanted kingFlatPOPAboveGF_two_eq_rename :
    kingFlatPOPAboveGF 2 =
      PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (2 : Fin 4) 3)).toRingHom
        (kingFlatPOPBelowGF 1)

end

end MetaMathlibExt
