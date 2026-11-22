/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Continuous Turán numbers

Statements from Sections 2-6 of Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24
(2024), Article A1 (primary text: arXiv:2105.04864).

`S ⊆ ℝ²` contains `P ⊆ ℝ²` when coordinate maps expanding all distances (slope at least one)
send `P` into `S`; `opx(n, P)` is the supremum of the Lebesgue measure of open `P`-free subsets
of `[0, n]²`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Computability.Ackermann

namespace MetaMathlibExt

@[expose] public section

/-- Containment of point sets (the paper's definition): `S` contains `P` when there are maps
`f_X, f_Y : ℝ → ℝ` that expand distances between coordinates of `P`
(`f(x₀) - f(x₁) ≥ x₀ - x₁` for `x₀ > x₁` among the `x`-coordinates, resp. `y`-coordinates, of `P`)
and send every `(x, y) ∈ P` to `(f_X x, f_Y y) ∈ S`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of containment). -/
public def PointSetContainsPattern (S P : Set (ℝ × ℝ)) : Prop :=
  ∃ fX fY : ℝ → ℝ,
    (∀ p ∈ P, ∀ q ∈ P, q.1 < p.1 → p.1 - q.1 ≤ fX p.1 - fX q.1) ∧
    (∀ p ∈ P, ∀ q ∈ P, q.2 < p.2 → p.2 - q.2 ≤ fY p.2 - fY q.2) ∧
    ∀ p ∈ P, (fX p.1, fY p.2) ∈ S

/-- Every set contains the empty pattern.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of containment). -/
public theorem pointSetContainsPattern_empty (S : Set (ℝ × ℝ)) : PointSetContainsPattern S ∅ :=
  ⟨id, id, by simp, by simp, by simp⟩

/-- The continuous Turán number `opx(n, P)`: the supremum of the Lebesgue measure `μ₂(S)` over
open `P`-free sets `S ⊆ [0, n]²` (`sSup ∅ = 0`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of `opx(n, P)`). -/
public noncomputable def opx (n : ℝ) (P : Set (ℝ × ℝ)) : ℝ :=
  sSup ((fun S => (MeasureTheory.volume S).toReal) ''
    {S | IsOpen S ∧ S ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n ∧ ¬ PointSetContainsPattern S P})

/-- `opx(n, P) ≥ 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of `opx(n, P)`). -/
public theorem opx_nonneg (n : ℝ) (P : Set (ℝ × ℝ)) : 0 ≤ opx n P := by
  apply Real.sSup_nonneg
  rintro _ ⟨S, -, rfl⟩
  exact ENNReal.toReal_nonneg

/-- The empty pattern is contained in every set, so `opx(n, ∅) = 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of `opx(n, P)`). -/
public theorem opx_empty (n : ℝ) : opx n ∅ = 0 := by
  simp [opx, pointSetContainsPattern_empty]

/-- Lemma 2.1: `opx(n, P)` is invariant under `90°` rotation `(x, y) ↦ (-y, x)` and the horizontal
and
vertical reflections `(x, y) ↦ (-x, y)`, `(x, y) ↦ (x, -y)`. Stated for all real `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.1
(`integers-2024-A1-lem-2-1`). -/
public theorem_wanted opx_rotate_reflect (n : ℝ) (P : Set (ℝ × ℝ)) :
    opx n ((fun p : ℝ × ℝ => (-p.2, p.1)) '' P) = opx n P ∧
      opx n ((fun p : ℝ × ℝ => (-p.1, p.2)) '' P) = opx n P ∧
      opx n ((fun p : ℝ × ℝ => (p.1, -p.2)) '' P) = opx n P

/-- Lemma 2.2: `opx(n, P)` is invariant under translating `P`. Stated for all real `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.2
(`integers-2024-A1-lem-2-2`). -/
public theorem_wanted opx_translate (n : ℝ) (P : Set (ℝ × ℝ)) (v : ℝ × ℝ) :
    opx n ((fun p => p + v) '' P) = opx n P

/-- Lemma 2.3: if `Q` contains `P`, then `opx(n, P) ≤ opx(n, Q)`. Stated for all real `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.3
(`integers-2024-A1-lem-2-3`). -/
public theorem_wanted opx_mono_of_containsPattern (n : ℝ) {P Q : Set (ℝ × ℝ)}
    (h : PointSetContainsPattern Q P) :
    opx n P ≤ opx n Q

/-- Lemma 2.4: `opx(m, P) ≤ opx(n, P)` for `m ≤ n` (the paper's `0 < m` is not needed: `opx`
vanishes for `m ≤ 0`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.4
(`integers-2024-A1-lem-2-4`). -/
public theorem_wanted opx_mono_left (P : Set (ℝ × ℝ)) {m n : ℝ} (hmn : m ≤ n) : opx m P ≤ opx n P

/-- Lemma 2.5: `opx(n, P)` is super-additive: `opx(m, P) + opx(n, P) ≤ opx(m + n, P)` for `m, n >
0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.5
(`integers-2024-A1-lem-2-5`). -/
public theorem_wanted opx_superadditive (P : Set (ℝ × ℝ)) {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    opx m P + opx n P ≤ opx (m + n) P

/-- Lemma 2.6: for `n > 0` and `0 < δ < n`, `opx(n, P) ≤ opx(n + δ, P) < opx(n, P) + 3nδ`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.6
(`integers-2024-A1-lem-2-6`). -/
public theorem_wanted opx_add_lt (P : Set (ℝ × ℝ)) {n δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hδn : δ < n)
:
    opx n P ≤ opx (n + δ) P ∧ opx (n + δ) P < opx n P + 3 * n * δ

/-- Proposition 2.7: `opx(n, P)` is continuous in `n` for `n > 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Proposition 2.7
(`integers-2024-A1-prop-2-7`). -/
public theorem_wanted opx_continuousOn (P : Set (ℝ × ℝ)) : ContinuousOn (fun n => opx n P) (Set.Ioi
0)

/-- Lemma 2.8: if `P = [a, a + c] × {b}` is a closed horizontal segment of length `c ≥ 0` and
`S ⊆ [0, n]²` is open and `P`-free, then every horizontal section `S_y` has `μ₁(S_y) ≤ c`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.8
(`integers-2024-A1-lem-2-8`). -/
public theorem_wanted volume_section_le_of_segment_free {a b c n : ℝ} (hc : 0 ≤ c) {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hSn : S ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n)
    (hfree : ¬ PointSetContainsPattern S (Set.Icc a (a + c) ×ˢ {b})) :
    ∀ y ∈ Set.Icc 0 n, MeasureTheory.volume {x : ℝ | (x, y) ∈ S} ≤ ENNReal.ofReal c

/-- Lemma 2.9: if `P` has a rightmost column `x = x₀` through `(x₀, y₀) ∈ P`, and `P'` adds the
horizontal segment `[x₀, x₀ + c] × {y₀}`, `c ≥ 0`, then `opx(n, P') ≤ opx(n, P) + cn` (`n > 0`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.9
(`integers-2024-A1-lem-2-9`). -/
public theorem_wanted opx_union_segment_le {P : Set (ℝ × ℝ)} {x₀ y₀ c n : ℝ} (hmem : (x₀, y₀) ∈ P)
    (hright : ∀ p ∈ P, p.1 ≤ x₀) (hc : 0 ≤ c) (hn : 0 < n) :
    opx n (P ∪ Set.Icc x₀ (x₀ + c) ×ˢ {y₀}) ≤ opx n P + c * n

/-- Corollary 2.10: if `P` has a rightmost column through `(x₀, y₀) ∈ P` and `P'` adds the point
`(x₀ + c, y₀)`, `c > 0`, then `opx(n, P') ≤ opx(n, P) + cn` (`n > 0`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 2.10
(`integers-2024-A1-cor-2-10`). -/
public theorem_wanted opx_insert_point_le {P : Set (ℝ × ℝ)} {x₀ y₀ c n : ℝ} (hmem : (x₀, y₀) ∈ P)
    (hright : ∀ p ∈ P, p.1 ≤ x₀) (hc : 0 < c) (hn : 0 < n) :
    opx n (insert (x₀ + c, y₀) P) ≤ opx n P + c * n

/-- Lemma 2.12: let `P` be finite with all gaps between consecutive distinct `x`-coordinates and
between consecutive distinct `y`-coordinates in `[c, d]`, `c > 0`, and let `P' = qP`, `q > 1`.
Then `opx(n, P') ≤ (⌈qd/c⌉ + 1)² opx(⌈⌈n/c⌉ / (⌈qd/c⌉ + 1)⌉ c, P)` for `n > 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.12
(`integers-2024-A1-lem-2-12`). -/
public theorem_wanted opx_dilate_le {P : Set (ℝ × ℝ)} (hP : P.Finite) {c d q n : ℝ} (hc : 0 < c) (hq
: 1 < q)
    (hn : 0 < n)
    (hx : ∀ p ∈ P, ∀ p' ∈ P, p.1 < p'.1 → (∀ r ∈ P, ¬ (p.1 < r.1 ∧ r.1 < p'.1)) →
      c ≤ p'.1 - p.1 ∧ p'.1 - p.1 ≤ d)
    (hy : ∀ p ∈ P, ∀ p' ∈ P, p.2 < p'.2 → (∀ r ∈ P, ¬ (p.2 < r.2 ∧ r.2 < p'.2)) →
      c ≤ p'.2 - p.2 ∧ p'.2 - p.2 ≤ d) :
    opx n ((fun p : ℝ × ℝ => q • p) '' P) ≤
      ((⌈q * d / c⌉ : ℝ) + 1) ^ 2 *
        opx ((⌈(⌈n / c⌉ : ℝ) / ((⌈q * d / c⌉ : ℝ) + 1)⌉ : ℝ) * c) P

/-- Theorem 4.1: a closed horizontal segment `P = [a, a + c] × {b}` of length `c ≥ 0` has
`opx(n, P) = cn`, for `n ≥ c`. CORRECTED READING: the paper omits `n ≥ c`, which its lower-bound
construction `(0, c) × (0, n) ⊆ [0, n]²` uses; for `n < c` every open `S ⊆ [0, n]²` avoids `P`, so
`opx(n, P) = n² ≠ cn` (e.g. `c = 2`, `n = 1`: `1 ≠ 2`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.1
(`integers-2024-A1-thm-4-1`). -/
public theorem_wanted opx_horizontal_segment {a b c n : ℝ} (hc : 0 ≤ c) (hcn : c ≤ n) :
    opx n (Set.Icc a (a + c) ×ˢ {b}) = c * n

/-- Theorem 4.2: the closed segment from `(0, 0)` to `(a, b)`, `a, b > 0`, has
`opx(n, P) = (a + b)n - ab`, for `n ≥ max(a, b)`. CORRECTED READING: the paper omits
`a, b ≤ n`, which its construction `(0, a) × (0, n) ∪ (0, n) × (0, b) ⊆ [0, n]²` uses; for
`n < max(a, b)` every open `S ⊆ [0, n]²` avoids `P`, so `opx(n, P) = n²` (e.g. `a = b = 2`,
`n = 1`: `1 ≠ 0`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.2
(`integers-2024-A1-thm-4-2`). -/
public theorem_wanted opx_diagonal_segment {a b n : ℝ} (ha : 0 < a) (hb : 0 < b) (han : a ≤ n) (hbn
: b ≤ n) :
    opx n (segment ℝ ((0 : ℝ), (0 : ℝ)) (a, b)) = (a + b) * n - a * b

/-- Theorem 4.5: a nonempty open `P ⊆ ℝ²` has `opx(n, P) = Θ(n²)` as `n → ∞`. Nonemptiness is
added: `opx(n, ∅) = 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.5
(`integers-2024-A1-thm-4-5`). -/
public theorem_wanted opx_open_isTheta {P : Set (ℝ × ℝ)} (hP : IsOpen P) (hne : P.Nonempty) :
    (fun n : ℝ => opx n P) =Θ[Filter.atTop] (fun n : ℝ => n ^ 2)

/-- Theorem 4.6: for nonempty open `P ⊆ ℝ²`, the set `Q_P` of points of `P` with rational
coordinates has `opx(n, Q_P) = Θ(n²)` as `n → ∞`. Nonemptiness is added (`Q_∅ = ∅`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.6
(`integers-2024-A1-thm-4-6`). -/
public theorem_wanted opx_rational_points_isTheta {P : Set (ℝ × ℝ)} (hP : IsOpen P) (hne :
P.Nonempty) :
    (fun n : ℝ => opx n {p ∈ P | ∃ x y : ℚ, p = ((x : ℝ), (y : ℝ))}) =Θ[Filter.atTop]
      (fun n : ℝ => n ^ 2)

/-- Theorem 4.3: if `f` is increasing on `[0, a]`, `a > 0`, with difference quotients
`(f t - f s) / (t - s) ≤ b` for `s < t` in `[0, a]`, then its graph `P = {(t, f t) : t ∈ [0, a]}`
has `opx(n, P) = Θ(n)` as `n → ∞`. The hypothesis `a > 0` is explicit (for `a = 0`, `P` is a
point and `opx(n, P) = 0`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.3
(`integers-2024-A1-thm-4-3`). -/
public theorem_wanted opx_increasing_graph_isTheta {a b : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : StrictMonoOn f (Set.Icc 0 a))
    (hb : ∀ s ∈ Set.Icc 0 a, ∀ t ∈ Set.Icc 0 a, s < t → (f t - f s) / (t - s) ≤ b) :
    (fun n : ℝ => opx n ((fun t => (t, f t)) '' Set.Icc 0 a)) =Θ[Filter.atTop] (fun n : ℝ => n)

/-- Lemma 4.4 (the cited Kővári–Sós–Turán-type lower bound, with the paper's explicit constant):
for `r ≥ 2` and `n ≥ 1` there is a set of at least `n^{2 - 2/(r+1)} / 2` cells of the `n × n`
grid containing no `r × r` all-ones submatrix `J_{r,r}`, i.e. `ex(n, J_{r,r}) ≥ n^{2-2/(r+1)}/2`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 4.4
(`integers-2024-A1-lem-4-4`). -/
public theorem_wanted exists_large_Jrr_free_cells {r n : ℕ} (hr : 2 ≤ r) (hn : 1 ≤ n) :
    ∃ S : Finset (Fin n × Fin n),
      (¬ ∃ R C : Finset (Fin n), R.card = r ∧ C.card = r ∧ R ×ˢ C ⊆ S) ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ ((2 : ℝ) - 2 / (r + 1)) ≤ S.card

/-- Theorem 4.7: for fixed `s, c > 0`, the pattern `P_{s,2,c} = [0, s] × {c, 2c}` (an equal
sign) has `opx(n, P_{s,2,c}) = Θ(s^{1/2} n^{3/2})` as `n → ∞`, with `s` fixed.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.7
(`integers-2024-A1-thm-4-7`); `P_{s,t,c}` as defined before it. -/
public theorem_wanted opx_equal_sign_isTheta {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (fun n : ℝ => opx n (Set.Icc 0 s ×ˢ {c, 2 * c})) =Θ[Filter.atTop]
      (fun n : ℝ => s ^ (1 / 2 : ℝ) * n ^ (3 / 2 : ℝ))

/-- Lemma 4.8: for `c ≥ 0` and `n ≥ ct`, the set `X ⊆ ℝ^t` of `y` with `0 < y_{t-1}`,
`y_{i+1} + c < y_i` and `y_i < n - i c` (indices from `0`) has `μ_t(X) ≥ (n/t - c)^t`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 4.8
(`integers-2024-A1-lem-4-8`), the explicit bound. -/
public theorem_wanted volume_staircase_simplex_ge {t : ℕ} {c n : ℝ} (hc : 0 ≤ c)
    (hn : c * t ≤ n) :
    ENNReal.ofReal ((n / t - c) ^ t) ≤
      MeasureTheory.volume {y : Fin t → ℝ | (∀ i : Fin t, y i < n - (i : ℕ) * c) ∧
        (∀ i : Fin t, (i : ℕ) + 1 = t → 0 < y i) ∧
        ∀ i j : Fin t, (j : ℕ) = (i : ℕ) + 1 → y j + c < y i}

/-- Theorem 4.9: for fixed `t ≥ 2` and `s, c > 0`, the pattern
`P_{s,t,c} = [0, s] × {c, 2c, …, tc}` has `opx(n, P_{s,t,c}) = O(s^{1/t} n^{2 - 1/t})` as
`n → ∞`, with `s` fixed.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.9
(`integers-2024-A1-thm-4-9`); `P_{s,t,c}` as defined before Theorem 4.7. -/
public theorem_wanted opx_stacked_segments_isBigO {t : ℕ} (ht : 2 ≤ t) {s c : ℝ} (hs : 0 < s)
    (hc : 0 < c) :
    (fun n : ℝ => opx n {p : ℝ × ℝ | p.1 ∈ Set.Icc 0 s ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ p.2 = i * c}) =O[Filter.atTop]
      (fun n : ℝ => s ^ (1 / t : ℝ) * n ^ (2 - 1 / t : ℝ))

/-- Theorem 4.10: if `P` is a finite union of horizontal segments `[a_i, b_i] × {y_i}` with
pairwise disjoint `x`-ranges and distinct heights `y_i`, then `opx(n, P) = O(n)`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.10
(`integers-2024-A1-thm-4-10`). -/
public theorem_wanted opx_horizontal_segments_isBigO {k : ℕ} (a b y : Fin k → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hx : ∀ i j, i ≠ j → Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j)))
    (hy : Function.Injective y) :
    (fun n : ℝ => opx n (⋃ i, Set.Icc (a i) (b i) ×ˢ {y i})) =O[Filter.atTop] (fun n : ℝ => n)

/-- Containment of a point pattern in a set of grid cells, i.e. 0-1 matrix containment of `M_P`:
the cells `A ⊆ ℕ × ℕ` (column, row) contain `P ⊆ ℝ²` when there are strictly increasing maps from
the `x`-coordinates of `P` to column indices and from the `y`-coordinates of `P` to row indices that
send every `(x, y) ∈ P` to a cell of `A`. For finite `P` this is containment of the 0-1 matrix
`M_P` (rows of `P` listed bottom to top; flipping the rows of both matrices preserves containment).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(0-1 matrix containment and the matrix `M_P` of a finite point set). -/
public def CellsContainPattern (A : Set (ℕ × ℕ)) (P : Set (ℝ × ℝ)) : Prop :=
  ∃ fX fY : ℝ → ℕ, StrictMonoOn fX (Prod.fst '' P) ∧ StrictMonoOn fY (Prod.snd '' P) ∧
    ∀ p ∈ P, (fX p.1, fY p.2) ∈ A

/-- `ex(n, M_P)`: the maximum number of cells of the `n × n` grid `{0, …, n - 1}²` forming a set
that does not contain `P` (`CellsContainPattern`). For finite `P` this is the 0-1 matrix
extremal function `ex(n, M_P)`, the maximum number of ones in an `M_P`-free `n × n` 0-1 matrix.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definitions of `ex(n, M)` and of `M_P`). -/
public noncomputable def patternEx (n : ℕ) (P : Set (ℝ × ℝ)) : ℕ :=
  sSup {k | ∃ A : Finset (ℕ × ℕ), A ⊆ Finset.range n ×ˢ Finset.range n ∧ A.card = k ∧
    ¬ CellsContainPattern (A : Set (ℕ × ℕ)) P}

/-- Every set of cells contains the empty pattern, so `ex(n, M_∅) = 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definitions of `ex(n, M)` and of `M_P`). -/
public theorem patternEx_empty (n : ℕ) : patternEx n ∅ = 0 := by
  have h : ∀ A : Set (ℕ × ℕ), CellsContainPattern A ∅ :=
    fun A => ⟨fun _ => 0, fun _ => 0, by simp [StrictMonoOn], by simp [StrictMonoOn], by simp⟩
  simp [patternEx, h]

/-- A single point is contained in every nonempty set of cells, so `ex(n, M_{p}) = 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definitions of `ex(n, M)` and of `M_P`). -/
public theorem patternEx_singleton (n : ℕ) (p : ℝ × ℝ) : patternEx n {p} = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro k ⟨A, -, rfl, hA⟩
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · exact absurd ⟨fun _ => a.1, fun _ => a.2, by simp, by simp, by simpa using ha⟩ hA

/-- `ex(n, M_P) ≤ n²`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definitions of `ex(n, M)` and of `M_P`). -/
public theorem patternEx_le_sq (n : ℕ) (P : Set (ℝ × ℝ)) : patternEx n P ≤ n ^ 2 := by
  apply csSup_le'
  rintro k ⟨A, hA, rfl, -⟩
  simpa [sq] using Finset.card_le_card hA

/-- The inverse Ackermann function `α(n)`: the least `k` with `n ≤ A(k, k)`, where `A = ack` is
the two-argument Ackermann function (the standard diagonal form).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)` in Keszegh's bound quoted before Corollary 3.8). -/
public def inverseAckermann (n : ℕ) : ℕ :=
  Nat.find (⟨n, (lt_ack_left n n).le⟩ : ∃ k, n ≤ ack k k)

/-- `n ≤ A(α(n), α(n))`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)`). -/
public theorem le_ack_inverseAckermann (n : ℕ) :
    n ≤ ack (inverseAckermann n) (inverseAckermann n) :=
  Nat.find_spec (⟨n, (lt_ack_left n n).le⟩ : ∃ k, n ≤ ack k k)

/-- `α(n) ≤ k` whenever `n ≤ A(k, k)`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)`). -/
public theorem inverseAckermann_le {n k : ℕ} (h : n ≤ ack k k) : inverseAckermann n ≤ k :=
  Nat.find_min' _ h

/-- `α(2) = 1` (`A(0, 0) = 1 < 2 ≤ 3 = A(1, 1)`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)`). -/
public theorem inverseAckermann_two : inverseAckermann 2 = 1 := by
  rw [inverseAckermann, Nat.find_eq_iff]
  refine ⟨by simp, fun k hk => ?_⟩
  interval_cases k
  simp [ack_zero]

/-- `α(8) = 3` (`A(2, 2) = 7 < 8 ≤ 61 = A(3, 3)`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)`). -/
public theorem inverseAckermann_eight : inverseAckermann 8 = 3 := by
  rw [inverseAckermann, Nat.find_eq_iff]
  refine ⟨by simp, fun k hk => ?_⟩
  interval_cases k <;> simp

/-- Theorem 3.1: for finite `P ⊆ ℝ²`, `opx(n, P) = Θ(ex(n, M_P))` as `n → ∞`, the constants
depending on `P`. Stated along natural `n` (the domain of `ex`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 3.1
(`integers-2024-A1-thm-3-1`). -/
public theorem_wanted opx_isTheta_patternEx {P : Set (ℝ × ℝ)} (hP : P.Finite) :
    (fun n : ℕ => opx n P) =Θ[Filter.atTop] (fun n : ℕ => (patternEx n P : ℝ))

/-- Theorem 3.2 (lower bound): for finite `P ⊆ ℝ²`, `opx(n, P) = Ω(ex(n, M_P))`. Stated along
natural `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 3.2
(`integers-2024-A1-thm-3-2`). -/
public theorem_wanted patternEx_isBigO_opx {P : Set (ℝ × ℝ)} (hP : P.Finite) :
    (fun n : ℕ => (patternEx n P : ℝ)) =O[Filter.atTop] (fun n : ℕ => opx n P)

/-- Theorem 3.3 (upper bound): for finite `P ⊆ ℝ²`, `opx(n, P) = O(ex(n, M_P))`. Stated along
natural `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 3.3
(`integers-2024-A1-thm-3-3`). -/
public theorem_wanted opx_isBigO_patternEx {P : Set (ℝ × ℝ)} (hP : P.Finite) :
    (fun n : ℕ => opx n P) =O[Filter.atTop] (fun n : ℕ => (patternEx n P : ℝ))

/-- Corollary 3.4: there is an absolute `C` such that for every `c > 0` there is `K` with
`opx(n, P) ≤ K · 2^{Ck} · n` for all natural `n` and every `k`-point `P ⊆ ℝ²` with pairwise
distinct `x`-coordinates and pairwise distinct `y`-coordinates whose consecutive columns and
consecutive rows are at most `c` apart (the paper's `2^{O(k)} n`, constant depending on `c`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.4
(`integers-2024-A1-cor-3-4`). -/
public theorem_wanted opx_permutation_pattern_le :
    ∃ C : ℝ, ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ P : Finset (ℝ × ℝ),
      Set.InjOn Prod.fst (P : Set (ℝ × ℝ)) → Set.InjOn Prod.snd (P : Set (ℝ × ℝ)) →
      (∀ p ∈ P, ∀ q ∈ P, p.1 < q.1 → (∀ r ∈ P, ¬ (p.1 < r.1 ∧ r.1 < q.1)) → q.1 - p.1 ≤ c) →
      (∀ p ∈ P, ∀ q ∈ P, p.2 < q.2 → (∀ r ∈ P, ¬ (p.2 < r.2 ∧ r.2 < q.2)) → q.2 - p.2 ≤ c) →
      ∀ n : ℕ, opx n P ≤ K * (2 : ℝ) ^ (C * P.card) * n

/-- Corollary 3.5: a full grid `P = X × Y` with `t = |X|` columns and `s = |Y|` rows (`st` points)
has `opx(n, P) = O(n^{2 - 1/t})`. Stated along natural `n`; for `t = 0` (`P = ∅`) the bound reads
`O(n²)` (Lean's `1 / 0 = 0`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.5
(`integers-2024-A1-cor-3-5`). -/
public theorem_wanted opx_grid_isBigO (X Y : Finset ℝ) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (2 - 1 / (X.card : ℝ)))

/-- Corollary 3.6: for every finite `P ⊆ ℝ²` there is `ε > 0` with `opx(n, P) = O(n^{2-ε})`.
Stated along natural `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.6
(`integers-2024-A1-cor-3-6`). -/
public theorem_wanted exists_opx_isBigO_rpow {P : Set (ℝ × ℝ)} (hP : P.Finite) :
    ∃ ε : ℝ, 0 < ε ∧
      (fun n : ℕ => opx n P) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (2 - ε))

/-- Corollary 3.7, first part: a grid `P = X × Y` with `2` columns and `k = |Y| ≥ 2` rows has
`opx(n, P) = Θ(n^{3/2})`. Stated along natural `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.7
(`integers-2024-A1-cor-3-7`), first sentence. -/
public theorem_wanted opx_grid_two_columns_isTheta {X Y : Finset ℝ} (hX : X.card = 2)
    (hY : 2 ≤ Y.card) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =Θ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ))

/-- Corollary 3.7, second part: a grid `P = X × Y` with `3` columns and `k = |Y| ≥ 3` rows has
`opx(n, P) = Θ(n^{5/3})`. Stated along natural `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.7
(`integers-2024-A1-cor-3-7`), second sentence. -/
public theorem_wanted opx_grid_three_columns_isTheta {X Y : Finset ℝ} (hX : X.card = 3)
    (hY : 3 ≤ Y.card) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =Θ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ))

/-- Corollary 3.8: if a finite `P ⊆ ℝ²` has no row with two points (pairwise distinct
`y`-coordinates), then `opx(n, P) = O(n · 2^{α(n)^t})` for some `t`, with `α` the inverse
Ackermann function. Stated along natural `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.8
(`integers-2024-A1-cor-3-8`). -/
public theorem_wanted exists_opx_isBigO_inverseAckermann {P : Set (ℝ × ℝ)} (hP : P.Finite)
    (hrow : Set.InjOn Prod.snd P) :
    ∃ t : ℕ, (fun n : ℕ => opx n P) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) * 2 ^ (inverseAckermann n ^ t))

/-- Proposition 6.4: let `Q n ⊆ ℝ²` have minimum `x`-coordinate `0`, maximum `x`-coordinate
`s n` and all `y`-coordinates in `{0, 1}`. Then `opx(n, Q n) = Ω(n^{2-o(1)})` iff
`s(n) = Ω(n^{1-o(1)})`, each side read as: for every `ε > 0`, eventually the left side is at
least `n^{2-ε}` (resp. `s n ≥ n^{1-ε}`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1,
Proposition 6.4 (`integers-2024-A1-prop-6-4`). -/
public theorem_wanted opx_two_row_growing_iff (s : ℝ → ℝ) (Q : ℝ → Set (ℝ × ℝ))
    (hmin : ∀ n, IsLeast (Prod.fst '' Q n) 0) (hmax : ∀ n, IsGreatest (Prod.fst '' Q n) (s n))
    (hy : ∀ n, ∀ p ∈ Q n, p.2 = 0 ∨ p.2 = 1) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, n ^ (2 - ε) ≤ opx n (Q n)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, n ^ (1 - ε) ≤ s n

/-- An open `S ⊆ [0, n]²` is saturating for `P` in `[0, n]²` when it avoids `P` but every open
proper superset `S' ⊆ [0, n]²` contains `P`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6
(definition of saturating sets). -/
public def IsOpxSaturating (n : ℝ) (P S : Set (ℝ × ℝ)) : Prop :=
  IsOpen S ∧ S ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n ∧ ¬ PointSetContainsPattern S P ∧
    ∀ S' : Set (ℝ × ℝ), IsOpen S' → S' ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n → S ⊂ S' →
      PointSetContainsPattern S' P

/-- The saturation function `osat(n, P)`: the infimum of `μ₂(S)` over open sets `S` saturating for
`P` in `[0, n]²` (`sInf ∅ = 0`; the paper leaves `osat(n, P)` undefined when no saturating set
exists).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6
(definition of `osat(n, P)`). -/
public noncomputable def osat (n : ℝ) (P : Set (ℝ × ℝ)) : ℝ :=
  sInf ((fun S => (MeasureTheory.volume S).toReal) '' {S | IsOpxSaturating n P S})

/-- `osat(n, P) ≥ 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6
(definition of `osat(n, P)`). -/
public theorem osat_nonneg (n : ℝ) (P : Set (ℝ × ℝ)) : 0 ≤ osat n P := by
  apply Real.sInf_nonneg
  rintro _ ⟨S, -, rfl⟩
  exact ENNReal.toReal_nonneg

/-- Lemma 6.5: for a single point `P = {p}`, `osat(n, P) = opx(n, P) = 0`. Stated for all real
`n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 6.5
(`integers-2024-A1-lem-6-5`). -/
public theorem_wanted osat_singleton_and_opx_singleton (n : ℝ) (p : ℝ × ℝ) :
    osat n {p} = 0 ∧ opx n {p} = 0

/-- Containment of point sets in `ℝ^d` (the paper's definition): `S` contains `P` when there are
maps `f_i : ℝ → ℝ`, one per coordinate, expanding distances between `i`-th coordinates of points
of `P` (`f_i(x) - f_i(x') ≥ x - x'` for `x > x'`) and sending every `p ∈ P` to
`(f_1(p_1), …, f_d(p_d)) ∈ S`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of containment in `ℝ^d`). -/
public def ContainsPatternD {d : ℕ} (S P : Set (Fin d → ℝ)) : Prop :=
  ∃ f : Fin d → ℝ → ℝ,
    (∀ i, ∀ p ∈ P, ∀ q ∈ P, q i < p i → p i - q i ≤ f i (p i) - f i (q i)) ∧
    ∀ p ∈ P, (fun i => f i (p i)) ∈ S

/-- Every set contains the empty pattern.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of containment in `ℝ^d`). -/
public theorem containsPatternD_empty {d : ℕ} (S : Set (Fin d → ℝ)) : ContainsPatternD S ∅ :=
  ⟨fun _ => id, by simp, by simp⟩

/-- The continuous Turán number `opx(n, P, d)`: the supremum of `μ_d(S)` over open `P`-free sets
`S ⊆ [0, n]^d` (`sSup ∅ = 0`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of `opx(n, P, d)`). -/
public noncomputable def opxD (d : ℕ) (n : ℝ) (P : Set (Fin d → ℝ)) : ℝ :=
  sSup ((fun S => (MeasureTheory.volume S).toReal) ''
    {S | IsOpen S ∧ S ⊆ Set.Icc 0 (fun _ => n) ∧ ¬ ContainsPatternD S P})

/-- `opx(n, P, d) ≥ 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of `opx(n, P, d)`). -/
public theorem opxD_nonneg (d : ℕ) (n : ℝ) (P : Set (Fin d → ℝ)) : 0 ≤ opxD d n P := by
  apply Real.sSup_nonneg
  rintro _ ⟨S, -, rfl⟩
  exact ENNReal.toReal_nonneg

/-- The empty pattern is contained in every set, so `opx(n, ∅, d) = 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of `opx(n, P, d)`). -/
public theorem opxD_empty (d : ℕ) (n : ℝ) : opxD d n ∅ = 0 := by
  simp [opxD, containsPatternD_empty]

/-- Containment of a point pattern `P ⊆ ℝ^d` in a set of cells `A ⊆ ℕ^d`, i.e. containment of the
`d`-dimensional 0-1 matrix `M_P`: there are strictly increasing maps from the `i`-th coordinates of
`P` to indices, one per coordinate, sending every `p ∈ P` to a cell of `A`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(containment of `d`-dimensional 0-1 matrices and the matrix `M_P`). -/
public def CellsContainPatternD {d : ℕ} (A : Set (Fin d → ℕ)) (P : Set (Fin d → ℝ)) : Prop :=
  ∃ f : Fin d → ℝ → ℕ, (∀ i, StrictMonoOn (f i) ((fun p => p i) '' P)) ∧
    ∀ p ∈ P, (fun i => f i (p i)) ∈ A

/-- `ex(n, M_P, d)`: the maximum number of cells of the grid `{0, …, n - 1}^d` forming a set that
does not contain `P` (`CellsContainPatternD`); for finite `P` this is the `d`-dimensional 0-1
matrix extremal function `ex(n, M_P, d)`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definitions of `ex(n, M, d)` and of `M_P`). -/
public noncomputable def patternExD (d n : ℕ) (P : Set (Fin d → ℝ)) : ℕ :=
  sSup {k | ∃ A : Finset (Fin d → ℕ), (∀ a ∈ A, ∀ i, a i < n) ∧ A.card = k ∧
    ¬ CellsContainPatternD (A : Set (Fin d → ℕ)) P}

/-- `ex(n, M_∅, d) = 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definitions of `ex(n, M, d)` and of `M_P`). -/
public theorem patternExD_empty (d n : ℕ) : patternExD d n ∅ = 0 := by
  have h : ∀ A : Set (Fin d → ℕ), CellsContainPatternD A ∅ :=
    fun A => ⟨fun _ _ => 0, fun _ => by simp [StrictMonoOn], by simp⟩
  simp [patternExD, h]

/-- A single point is contained in every nonempty set of cells, so `ex(n, M_{p}, d) = 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definitions of `ex(n, M, d)` and of `M_P`). -/
public theorem patternExD_singleton (d n : ℕ) (p : Fin d → ℝ) : patternExD d n {p} = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro k ⟨A, -, rfl, hA⟩
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · exact absurd ⟨fun i _ => a i, fun i => by simp, by simpa using ha⟩ hA

/-- Lemma 5.1: if `Q` contains `P` in `ℝ^d`, then `opx(n, P, d) ≤ opx(n, Q, d)`. Stated for all
real `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.1
(`integers-2024-A1-lem-5-1`). -/
public theorem_wanted opxD_mono_of_containsPatternD {d : ℕ} (n : ℝ) {P Q : Set (Fin d → ℝ)}
    (h : ContainsPatternD Q P) : opxD d n P ≤ opxD d n Q

/-- Lemma 5.2: `opx(m, P, d) ≤ opx(n, P, d)` for `m ≤ n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.2
(`integers-2024-A1-lem-5-2`). -/
public theorem_wanted opxD_mono_left {d : ℕ} (P : Set (Fin d → ℝ)) {m n : ℝ} (hmn : m ≤ n) :
    opxD d m P ≤ opxD d n P

/-- Lemma 5.3: for `n > 0` and `0 < ε < n`,
`opx(n, P, d) ≤ opx(n + ε, P, d) < opx(n, P, d) + d (2n)^{d-1} ε`. The hypothesis `2 ≤ d` is
added: for `d = 1` the strict inequality fails (`P = {0, L}` with `L > n + ε` is avoided by every
open subset of `[0, n + ε]`, so `opx(n + ε, P, 1) = n + ε = opx(n, P, 1) + ε`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.3
(`integers-2024-A1-lem-5-3`). -/
public theorem_wanted opxD_add_lt {d : ℕ} (hd : 2 ≤ d) (P : Set (Fin d → ℝ)) {n ε : ℝ}
    (hn : 0 < n) (hε : 0 < ε) (hεn : ε < n) :
    opxD d n P ≤ opxD d (n + ε) P ∧ opxD d (n + ε) P < opxD d n P + d * (2 * n) ^ (d - 1) * ε

/-- Proposition 5.4: `opx(n, P, d)` is continuous in `n` for `n > 0`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Proposition 5.4
(`integers-2024-A1-prop-5-4`). -/
public theorem_wanted opxD_continuousOn {d : ℕ} (P : Set (Fin d → ℝ)) :
    ContinuousOn (fun n => opxD d n P) (Set.Ioi 0)

/-- Lemma 5.5: for `P ⊆ ℝ^{d+1}` with projection `Pr(P) ⊆ ℝ^d` (drop the last coordinate),
`opx(n, P, d + 1) ≥ n · opx(n, Pr(P), d)`. Stated for all real `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.5
(`integers-2024-A1-lem-5-5`); `Pr(P)` as defined before it. -/
public theorem_wanted mul_opxD_init_le {d : ℕ} (n : ℝ) (P : Set (Fin (d + 1) → ℝ)) :
    n * opxD d n (Fin.init '' P) ≤ opxD (d + 1) n P

/-- Proposition 5.6: if all points of `P ⊆ ℝ^{d+1}` share their last coordinate, then
`opx(n, P, d + 1) = n · opx(n, Pr(P), d)`. Stated for all real `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Proposition 5.6
(`integers-2024-A1-prop-5-6`). -/
public theorem_wanted opxD_eq_mul_opxD_init {d : ℕ} (n : ℝ) {P : Set (Fin (d + 1) → ℝ)}
    (hP : ∃ z, ∀ p ∈ P, p (Fin.last d) = z) :
    opxD (d + 1) n P = n * opxD d n (Fin.init '' P)

/-- Corollary 5.7: for nonempty open `P ⊆ ℝ²` and dimension `m + 3 > 2`, let `P' ⊆ ℝ^{m+3}` be
`P × {0}^{m+1}` and `Q_{P'}` its points with rational coordinates; then
`opx(n, Q_{P'}, m + 3) = Θ(n^{m+3})`. Nonemptiness is added (`Q_∅ = ∅`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.7
(`integers-2024-A1-cor-5-7`). -/
public theorem_wanted opxD_rational_points_embed_isTheta (m : ℕ) {P : Set (ℝ × ℝ)}
    (hP : IsOpen P) (hne : P.Nonempty) :
    (fun n : ℝ => opxD (m + 3) n {v | (v 0, v 1) ∈ P ∧
        (∀ i : Fin (m + 3), 2 ≤ (i : ℕ) → v i = 0) ∧ ∀ i, ∃ q : ℚ, v i = q}) =Θ[Filter.atTop]
      (fun n : ℝ => n ^ (m + 3))

/-- Corollary 5.8: for nonempty open `P ⊆ ℝ^d` with `d ≥ 2`, `opx(n, P, d) = Θ(n^d)` and
`opx(n, Q_P, d) = Θ(n^d)`, `Q_P` the points of `P` with rational coordinates. Nonemptiness is
added; `2 ≤ d` is added: for `d = 1`, `P = (0, 1)` has `opx(n, P, 1) ≤ 1` (an expanding map of
`(0, 1)` into `S` has a `1`-Lipschitz inverse, so a `P`-free open `S` has `μ₁(S) ≤ 1`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.8
(`integers-2024-A1-cor-5-8`). -/
public theorem_wanted opxD_open_isTheta {d : ℕ} (hd : 2 ≤ d) {P : Set (Fin d → ℝ)}
    (hP : IsOpen P) (hne : P.Nonempty) :
    (fun n : ℝ => opxD d n P) =Θ[Filter.atTop] (fun n : ℝ => n ^ d) ∧
      (fun n : ℝ => opxD d n {p ∈ P | ∀ i, ∃ q : ℚ, p i = q}) =Θ[Filter.atTop]
        (fun n : ℝ => n ^ d)

/-- Lemma 5.10: let `P ⊆ ℝ^d` be finite with all gaps between consecutive distinct values of each
coordinate in `[c₁, c₂]`, `c₁ > 0`, and `P' = qP`, `q > 1`. Then
`opx(n, P', d) ≤ (⌈qc₂/c₁⌉ + 1)^d opx(⌈⌈n/c₁⌉ / (⌈qc₂/c₁⌉ + 1)⌉ c₁, P, d)` for `n > 0`. Read from
the primary text (the extracted record's display is garbled).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.10
(`integers-2024-A1-lem-5-10`). -/
public theorem_wanted opxD_dilate_le {d : ℕ} {P : Set (Fin d → ℝ)} (hP : P.Finite)
    {c₁ c₂ q n : ℝ} (hc : 0 < c₁) (hq : 1 < q) (hn : 0 < n)
    (hgap : ∀ i, ∀ p ∈ P, ∀ p' ∈ P, p i < p' i → (∀ r ∈ P, ¬ (p i < r i ∧ r i < p' i)) →
      c₁ ≤ p' i - p i ∧ p' i - p i ≤ c₂) :
    opxD d n ((fun p => q • p) '' P) ≤
      ((⌈q * c₂ / c₁⌉ : ℝ) + 1) ^ d *
        opxD d ((⌈(⌈n / c₁⌉ : ℝ) / ((⌈q * c₂ / c₁⌉ : ℝ) + 1)⌉ : ℝ) * c₁) P

/-- Theorem 5.11: for finite `P ⊆ ℝ^d`, `opx(n, P, d) = Θ(ex(n, M_P, d))`, the constants
depending on `P`. Stated along natural `n` (the domain of `ex`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 5.11
(`integers-2024-A1-thm-5-11`). -/
public theorem_wanted opxD_isTheta_patternExD {d : ℕ} {P : Set (Fin d → ℝ)} (hP : P.Finite) :
    (fun n : ℕ => opxD d n P) =Θ[Filter.atTop] (fun n : ℕ => (patternExD d n P : ℝ))

/-- Corollary 5.12: for each `d` there is `C` such that for every `c > 0` there is `K` with
`opx(n, P, d) ≤ K · 2^{Ck} · n^{d-1}` for all natural `n` and every `k`-point `P ⊆ ℝ^d` in which no
two points share a coordinate and consecutive values of each coordinate are at most `c` apart.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.12
(`integers-2024-A1-cor-5-12`). -/
public theorem_wanted opxD_permutation_pattern_le (d : ℕ) :
    ∃ C : ℝ, ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ P : Finset (Fin d → ℝ),
      (∀ i, Set.InjOn (fun p : Fin d → ℝ => p i) (P : Set (Fin d → ℝ))) →
      (∀ i, ∀ p ∈ P, ∀ q ∈ P, p i < q i → (∀ r ∈ P, ¬ (p i < r i ∧ r i < q i)) →
        q i - p i ≤ c) →
      ∀ n : ℕ, opxD d n P ≤ K * (2 : ℝ) ^ (C * P.card) * (n : ℝ) ^ (d - 1)

/-- Corollary 5.13: a full grid `P = X_1 × ⋯ × X_d` (so `M_P = J_{k_1, …, k_d}`, `k_i = |X_i|`) has
`opx(n, P, d) = O(n^{d - α})`, `α = max_i k_i / ∏_i k_i`. Stated along natural `n`; if some
`k_i = 0` then `P = ∅` and the bound reads `O(n^d)` (Lean's `x / 0 = 0`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.13
(`integers-2024-A1-cor-5-13`). -/
public theorem_wanted opxD_grid_isBigO {d : ℕ} (X : Fin d → Finset ℝ) :
    (fun n : ℕ => opxD d n (Set.univ.pi fun i => (X i : Set ℝ))) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ ((d : ℝ) -
        ((Finset.univ.sup fun i => (X i).card : ℕ) : ℝ) / ((∏ i, (X i).card : ℕ) : ℝ)))

/-- Corollary 5.14: for every finite `P ⊆ ℝ^d` there is `ε > 0` with `opx(n, P, d) = O(n^{d-ε})`.
Stated along natural `n`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.14
(`integers-2024-A1-cor-5-14`). -/
public theorem_wanted exists_opxD_isBigO_rpow {d : ℕ} {P : Set (Fin d → ℝ)} (hP : P.Finite) :
    ∃ ε : ℝ, 0 < ε ∧
      (fun n : ℕ => opxD d n P) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ ((d : ℝ) - ε))

/-- Corollary 5.15: let `P ⊆ ℝ²` have `k ≥ 2` points with pairwise distinct `x`-coordinates and
pairwise distinct `y`-coordinates, and `P_i = {(x, y, j) : (x, y) ∈ P, j = 1, …, i} ⊆ ℝ³`. Then
`opx(n, P_2, 3) = Θ(n^{5/2})` and `opx(n, P_3, 3) = Θ(n^{8/3})`. Stated along natural `n`;
`k ≥ 2` is the paper's standing assumption on the permutation matrix (for `k = 1`, `P_2` is two
points on a vertical line and `opx(n, P_2, 3) ≤ n²`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.15
(`integers-2024-A1-cor-5-15`). -/
public theorem_wanted opxD_permutation_stack_isTheta {P : Finset (ℝ × ℝ)} (hk : 2 ≤ P.card)
    (hx : Set.InjOn Prod.fst (P : Set (ℝ × ℝ))) (hy : Set.InjOn Prod.snd (P : Set (ℝ × ℝ))) :
    (fun n : ℕ => opxD 3 n {v | (v 0, v 1) ∈ P ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ 2 ∧ v 2 = j})
        =Θ[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (5 / 2 : ℝ)) ∧
      (fun n : ℕ => opxD 3 n {v | (v 0, v 1) ∈ P ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ 3 ∧ v 2 = j})
        =Θ[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (8 / 3 : ℝ))

/-- Theorem 5.16: for `d`, `t ≥ 2` and `c > 0` there is `K` (depending only on `d`, `t`, `c`) such
that for every `P ⊆ ℝ^d` and `n > 0`, with
`Q_{P,t,c} = {(x, y) : x ∈ P, y ∈ {c, 2c, …, tc}} ⊆ ℝ^{d+1}`,
`opx(n, Q_{P,t,c}, d + 1) ≤ K (opx(n, P, d)^{1/t} n^{d+1-d/t} + n^d)`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 5.16
(`integers-2024-A1-thm-5-16`); `Q_{P,t,c}` as defined before it. -/
public theorem_wanted opxD_stack_le (d t : ℕ) (hd : 2 ≤ d) (ht : 2 ≤ t) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, ∀ (P : Set (Fin d → ℝ)) (n : ℝ), 0 < n →
      opxD (d + 1) n {v | Fin.init v ∈ P ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ v (Fin.last d) = i * c} ≤
        K * (opxD d n P ^ (1 / t : ℝ) * n ^ ((d : ℝ) + 1 - d / t) + n ^ d)

/-- Corollary 5.17, first part: if `P ⊆ ℝ²` has at least two points and `opx(n, P) = O(n)`, then for
`c > 0`, `Q_{P,2,c} = {(x, y, z) : (x, y) ∈ P, z ∈ {c, 2c}}` has
`opx(n, Q_{P,2,c}, 3) = Θ(n^{5/2})`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.17
(`integers-2024-A1-cor-5-17`), first sentence. -/
public theorem_wanted opxD_stack_two_isTheta {P : Set (ℝ × ℝ)} (hP : P.Nontrivial)
    (hlin : (fun n : ℝ => opx n P) =O[Filter.atTop] (fun n : ℝ => n)) {c : ℝ} (hc : 0 < c) :
    (fun n : ℝ => opxD 3 n {v | (v 0, v 1) ∈ P ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * c})
      =Θ[Filter.atTop] (fun n : ℝ => n ^ (5 / 2 : ℝ))

/-- Corollary 5.17, second part: if `P ⊆ ℝ²` has three points with pairwise distinct
`x`-coordinates and `opx(n, P) = O(n)`, then for `c > 0`,
`Q_{P,3,c} = {(x, y, z) : (x, y) ∈ P, z ∈ {c, 2c, 3c}}` has `opx(n, Q_{P,3,c}, 3) = Θ(n^{8/3})`.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.17
(`integers-2024-A1-cor-5-17`), second sentence. -/
public theorem_wanted opxD_stack_three_isTheta {P : Set (ℝ × ℝ)}
    (hP : ∃ p ∈ P, ∃ q ∈ P, ∃ r ∈ P, p.1 ≠ q.1 ∧ p.1 ≠ r.1 ∧ q.1 ≠ r.1)
    (hlin : (fun n : ℝ => opx n P) =O[Filter.atTop] (fun n : ℝ => n)) {c : ℝ} (hc : 0 < c) :
    (fun n : ℝ => opxD 3 n {v | (v 0, v 1) ∈ P ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c})
      =Θ[Filter.atTop] (fun n : ℝ => n ^ (8 / 3 : ℝ))

/-- Corollary 5.18: for `f` increasing on `[0, a]`, `a > 0`, with difference quotients at most `b`,
its graph `P` and `c > 0`: `opx(n, Q_{P,2,c}, 3) = Θ(n^{5/2})` and
`opx(n, Q_{P,3,c}, 3) = Θ(n^{8/3})`. The hypothesis `a > 0` is explicit (as in Theorem 4.3).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.18
(`integers-2024-A1-cor-5-18`). -/
public theorem_wanted opxD_graph_stack_isTheta {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Icc 0 a))
    (hb : ∀ s ∈ Set.Icc 0 a, ∀ t ∈ Set.Icc 0 a, s < t → (f t - f s) / (t - s) ≤ b) :
    (fun n : ℝ => opxD 3 n {v | (∃ t ∈ Set.Icc 0 a, v 0 = t ∧ v 1 = f t) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (5 / 2 : ℝ)) ∧
      (fun n : ℝ => opxD 3 n {v | (∃ t ∈ Set.Icc 0 a, v 0 = t ∧ v 1 = f t) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (8 / 3 : ℝ))

/-- Corollary 5.19: for the plus sign `P = {(x, y) : |x|, |y| ≤ r, x = 0 ∨ y = 0}` with `r > 0`
and `c > 0`: `opx(n, Q_{P,2,c}, 3) = Θ(n^{5/2})` and `opx(n, Q_{P,3,c}, 3) = Θ(n^{8/3})`. The
paper's size parameter `d` is renamed `r`; `r > 0` is added (for `r = 0`, `Q_{P,2,c}` is two points
on a vertical line and `opx(n, Q_{P,2,c}, 3) ≤ c n²`).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.19
(`integers-2024-A1-cor-5-19`). -/
public theorem_wanted opxD_plus_stack_isTheta {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (fun n : ℝ => opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (5 / 2 : ℝ)) ∧
      (fun n : ℝ => opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (8 / 3 : ℝ))

end

end MetaMathlibExt
