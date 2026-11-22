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

/-- **Containment of planar point sets.** A set $S \subseteq \mathbb{R}^2$ contains a set
$P \subseteq \mathbb{R}^2$ when there are maps $f_X, f_Y : \mathbb{R} \to \mathbb{R}$ such that
$f_X(x_0) - f_X(x_1) \ge x_0 - x_1$ whenever $x_0 > x_1$ are $x$-coordinates of points of $P$,
$f_Y(y_0) - f_Y(y_1) \ge y_0 - y_1$ whenever $y_0 > y_1$ are $y$-coordinates of points of $P$,
and $(f_X(x), f_Y(y)) \in S$ for every $(x, y) \in P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of containment). -/
public def PointSetContainsPattern (S P : Set (ℝ × ℝ)) : Prop :=
  ∃ fX fY : ℝ → ℝ,
    (∀ p ∈ P, ∀ q ∈ P, q.1 < p.1 → p.1 - q.1 ≤ fX p.1 - fX q.1) ∧
    (∀ p ∈ P, ∀ q ∈ P, q.2 < p.2 → p.2 - q.2 ≤ fY p.2 - fY q.2) ∧
    ∀ p ∈ P, (fX p.1, fY p.2) ∈ S

/-- **Every planar set contains the empty pattern.** Every set $S \subseteq \mathbb{R}^2$ contains
the empty set $\emptyset$ in the sense of containment of planar point sets.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of containment). -/
public theorem pointSetContainsPattern_empty (S : Set (ℝ × ℝ)) : PointSetContainsPattern S ∅ :=
  ⟨id, id, by simp, by simp, by simp⟩

/-- **Continuous Turán number in the plane.** For a real number $n$ and a set
$P \subseteq \mathbb{R}^2$, the continuous Turán number $\operatorname{opx}(n, P)$ is the supremum
of the Lebesgue measures $\mu_2(S)$ over all open sets $S \subseteq [0, n]^2$ that do not contain
$P$ in the sense of point-set pattern containment; it is $0$ when there is no such set.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of `opx(n, P)`). -/
public noncomputable def opx (n : ℝ) (P : Set (ℝ × ℝ)) : ℝ :=
  sSup ((fun S => (MeasureTheory.volume S).toReal) ''
    {S | IsOpen S ∧ S ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n ∧ ¬ PointSetContainsPattern S P})

/-- **Nonnegativity of the continuous Turán number.** For every real number $n$ and every set
$P \subseteq \mathbb{R}^2$, $\operatorname{opx}(n, P) \ge 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of `opx(n, P)`). -/
public theorem opx_nonneg (n : ℝ) (P : Set (ℝ × ℝ)) : 0 ≤ opx n P := by
  apply Real.sSup_nonneg
  rintro _ ⟨S, -, rfl⟩
  exact ENNReal.toReal_nonneg

/-- **Continuous Turán number of the empty pattern.** For every real number $n$,
$\mathrm{opx}(n, \emptyset) = 0$: every set contains the empty pattern, so no set avoids it.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of `opx(n, P)`). -/
public theorem opx_empty (n : ℝ) : opx n ∅ = 0 := by
  simp [opx, pointSetContainsPattern_empty]

/-- **Rotation and reflection invariance of the continuous Turán number.** For every real
number $n$ and every set $P \subseteq \mathbb{R}^2$, the value $\operatorname{opx}(n, P)$ does
not change when $P$ is replaced by its image under the rotation by $90^\circ$,
$(x, y) \mapsto (-y, x)$, under the reflection $(x, y) \mapsto (-x, y)$, or under the
reflection $(x, y) \mapsto (x, -y)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.1
(`integers-2024-A1-lem-2-1`). -/
public theorem_wanted opx_rotate_reflect (n : ℝ) (P : Set (ℝ × ℝ)) :
    opx n ((fun p : ℝ × ℝ => (-p.2, p.1)) '' P) = opx n P ∧
      opx n ((fun p : ℝ × ℝ => (-p.1, p.2)) '' P) = opx n P ∧
      opx n ((fun p : ℝ × ℝ => (p.1, -p.2)) '' P) = opx n P

/-- **Translation invariance of the continuous Turán number.** Let $n$ be a real number,
$P \subseteq \mathbb{R}^2$ a set and $v \in \mathbb{R}^2$ a vector, and let
$P + v = \{p + v : p \in P\}$ be the translate of $P$ by $v$. Then
$\operatorname{opx}(n, P + v) = \operatorname{opx}(n, P)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.2
(`integers-2024-A1-lem-2-2`). -/
public theorem_wanted opx_translate (n : ℝ) (P : Set (ℝ × ℝ)) (v : ℝ × ℝ) :
    opx n ((fun p => p + v) '' P) = opx n P

/-- **Monotonicity of the continuous Turán number under containment.** Let $n$ be a real number
and let $P, Q \subseteq \mathbb{R}^2$. If $Q$ contains $P$ in the sense of containment of planar
point sets, then $\operatorname{opx}(n, P) \le \operatorname{opx}(n, Q)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.3
(`integers-2024-A1-lem-2-3`). -/
public theorem_wanted opx_mono_of_containsPattern (n : ℝ) {P Q : Set (ℝ × ℝ)}
    (h : PointSetContainsPattern Q P) :
    opx n P ≤ opx n Q

/-- **Monotonicity of the continuous Turán number in the side length.** For every set
$P \subseteq \mathbb{R}^2$ and all real numbers $m \le n$, the continuous Turán numbers satisfy
$\operatorname{opx}(m, P) \le \operatorname{opx}(n, P)$.

The paper assumes $0 < m$. This is not needed, since $\operatorname{opx}(m, P) = 0$ for $m \le 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.4
(`integers-2024-A1-lem-2-4`). -/
public theorem_wanted opx_mono_left (P : Set (ℝ × ℝ)) {m n : ℝ} (hmn : m ≤ n) : opx m P ≤ opx n P

/-- **Superadditivity of the continuous Turán number.** For every set $P \subseteq \mathbb{R}^2$
and all real numbers $m, n > 0$,
$\operatorname{opx}(m, P) + \operatorname{opx}(n, P) \le \operatorname{opx}(m + n, P)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.5
(`integers-2024-A1-lem-2-5`). -/
public theorem_wanted opx_superadditive (P : Set (ℝ × ℝ)) {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    opx m P + opx n P ≤ opx (m + n) P

/-- **Increment bound for the continuous Turán number.** Let $P \subseteq \mathbb{R}^2$ and let
$n, \delta$ be real numbers with $n > 0$ and $0 < \delta < n$. Then the continuous Turán number
$\mathrm{opx}$ satisfies $\mathrm{opx}(n, P) \le \mathrm{opx}(n + \delta, P)$ and
$\mathrm{opx}(n + \delta, P) < \mathrm{opx}(n, P) + 3 n \delta$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.6
(`integers-2024-A1-lem-2-6`). -/
public theorem_wanted opx_add_lt (P : Set (ℝ × ℝ)) {n δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hδn : δ < n)
:
    opx n P ≤ opx (n + δ) P ∧ opx (n + δ) P < opx n P + 3 * n * δ

/-- **Continuity of the continuous Turán number.** For every $P \subseteq \mathbb{R}^2$, the
continuous Turán number $\mathrm{opx}(n, P)$ is a continuous function of $n$ on $(0, \infty)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Proposition 2.7
(`integers-2024-A1-prop-2-7`). -/
public theorem_wanted opx_continuousOn (P : Set (ℝ × ℝ)) : ContinuousOn (fun n => opx n P) (Set.Ioi
0)

/-- **Sections of open sets avoiding a horizontal segment.** Let $a, b, c, n$ be real numbers with
$c \ge 0$, and let $S \subseteq [0, n]^2$ be an open set that does not contain the closed
horizontal segment $[a, a + c] \times \{b\}$ in the sense of containment of planar point sets.
Then for every $y \in [0, n]$ the horizontal section $\{x \in \mathbb{R} : (x, y) \in S\}$ has
one-dimensional Lebesgue measure at most $c$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.8
(`integers-2024-A1-lem-2-8`). -/
public theorem_wanted volume_section_le_of_segment_free {a b c n : ℝ} (hc : 0 ≤ c) {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hSn : S ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n)
    (hfree : ¬ PointSetContainsPattern S (Set.Icc a (a + c) ×ˢ {b})) :
    ∀ y ∈ Set.Icc 0 n, MeasureTheory.volume {x : ℝ | (x, y) ∈ S} ≤ ENNReal.ofReal c

/-- **Extending a pattern by a horizontal segment at its right edge.** Let
$P \subseteq \mathbb{R}^2$ and $(x_0, y_0) \in P$ with $x \le x_0$ for every $(x, y) \in P$, and let
$c \ge 0$ and $n > 0$ be real numbers. Then
$$\operatorname{opx}(n, P \cup ([x_0, x_0 + c] \times \{y_0\})) \le \operatorname{opx}(n, P) + cn.$$

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.9
(`integers-2024-A1-lem-2-9`). -/
public theorem_wanted opx_union_segment_le {P : Set (ℝ × ℝ)} {x₀ y₀ c n : ℝ} (hmem : (x₀, y₀) ∈ P)
    (hright : ∀ p ∈ P, p.1 ≤ x₀) (hc : 0 ≤ c) (hn : 0 < n) :
    opx n (P ∪ Set.Icc x₀ (x₀ + c) ×ˢ {y₀}) ≤ opx n P + c * n

/-- **Adding a point to the right of a pattern.** Let $P \subseteq \mathbb{R}^2$ and let
$(x_0, y_0) \in P$ be such that every point of $P$ has $x$-coordinate at most $x_0$. Then
$\operatorname{opx}(n, P \cup \{(x_0 + c, y_0)\}) \le \operatorname{opx}(n, P) + cn$ for all real
numbers $c > 0$ and $n > 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 2.10
(`integers-2024-A1-cor-2-10`). -/
public theorem_wanted opx_insert_point_le {P : Set (ℝ × ℝ)} {x₀ y₀ c n : ℝ} (hmem : (x₀, y₀) ∈ P)
    (hright : ∀ p ∈ P, p.1 ≤ x₀) (hc : 0 < c) (hn : 0 < n) :
    opx n (insert (x₀ + c, y₀) P) ≤ opx n P + c * n

/-- **Continuous Turán number of a dilated finite pattern.** Let $P \subseteq \mathbb{R}^2$ be
finite, and let $c > 0$ and $d$ be real numbers such that any two consecutive distinct
$x$-coordinates of points of $P$ differ by at least $c$ and at most $d$, and likewise for
$y$-coordinates. Let $q > 1$ and $qP = \{qp : p \in P\}$. Then for every real $n > 0$,
$\mathrm{opx}(n, qP) \le (\lceil qd/c \rceil + 1)^2 \, \mathrm{opx}(m, P)$, where
$m = \lceil \lceil n/c \rceil / (\lceil qd/c \rceil + 1) \rceil \, c$.

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

/-- **Continuous Turán number of a horizontal segment.** Let $a, b, c, n$ be real numbers with
$0 \le c \le n$, and let $P = [a, a + c] \times \{b\}$ be the closed horizontal segment of length
$c$ at height $b$. Then $\operatorname{opx}(n, P) = cn$.

The hypothesis $n \ge c$ is missing from the paper, whose lower-bound construction
$(0, c) \times (0, n) \subseteq [0, n]^2$ uses it: for $0 < n < c$ no subset of $[0, n]^2$ contains
$P$, so $\operatorname{opx}(n, P) = n^2 \ne cn$ (for example $c = 2$ and $n = 1$).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.1
(`integers-2024-A1-thm-4-1`). -/
public theorem_wanted opx_horizontal_segment {a b c n : ℝ} (hc : 0 ≤ c) (hcn : c ≤ n) :
    opx n (Set.Icc a (a + c) ×ˢ {b}) = c * n

/-- **Continuous Turán number of a diagonal segment.** Let $a, b, n$ be real numbers with
$0 < a \le n$ and $0 < b \le n$, and let $P$ be the closed segment from $(0, 0)$ to $(a, b)$.
Then the continuous Turán number satisfies $\operatorname{opx}(n, P) = (a + b)n - ab$.

The hypotheses $a \le n$ and $b \le n$ are missing from the paper, whose lower-bound construction
$(0, a) \times (0, n) \cup (0, n) \times (0, b) \subseteq [0, n]^2$ uses them: for
$0 < n < \max(a, b)$ no subset of $[0, n]^2$ contains $P$, so $\operatorname{opx}(n, P) = n^2$
(for example $a = b = 2$ and $n = 1$, where $(a + b)n - ab = 0 \ne 1$).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.2
(`integers-2024-A1-thm-4-2`). -/
public theorem_wanted opx_diagonal_segment {a b n : ℝ} (ha : 0 < a) (hb : 0 < b) (han : a ≤ n) (hbn
: b ≤ n) :
    opx n (segment ℝ ((0 : ℝ), (0 : ℝ)) (a, b)) = (a + b) * n - a * b

/-- **Open patterns have quadratic continuous Turán number.** For every nonempty open set
$P \subseteq \mathbb{R}^2$, $\operatorname{opx}(n, P) = \Theta(n^2)$ as the real number $n$ tends
to infinity.

The paper does not assume that $P$ is nonempty. The assumption is needed, since
$\operatorname{opx}(n, \emptyset) = 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.5
(`integers-2024-A1-thm-4-5`). -/
public theorem_wanted opx_open_isTheta {P : Set (ℝ × ℝ)} (hP : IsOpen P) (hne : P.Nonempty) :
    (fun n : ℝ => opx n P) =Θ[Filter.atTop] (fun n : ℝ => n ^ 2)

/-- **Rational points of open patterns have quadratic continuous Turán number.** Let
$P \subseteq \mathbb{R}^2$ be a nonempty open set and let $Q_P$ be the set of points of $P$ both
of whose coordinates are rational. Then $\operatorname{opx}(n, Q_P) = \Theta(n^2)$ as the real
number $n$ tends to infinity.

The paper does not assume that $P$ is nonempty. The assumption is needed, since
$Q_\emptyset = \emptyset$ and $\operatorname{opx}(n, \emptyset) = 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.6
(`integers-2024-A1-thm-4-6`). -/
public theorem_wanted opx_rational_points_isTheta {P : Set (ℝ × ℝ)} (hP : IsOpen P) (hne :
P.Nonempty) :
    (fun n : ℝ => opx n {p ∈ P | ∃ x y : ℚ, p = ((x : ℝ), (y : ℝ))}) =Θ[Filter.atTop]
      (fun n : ℝ => n ^ 2)

/-- **Continuous Turán number of the graph of an increasing function.** Let $a > 0$ and $b$ be real
numbers and let $f : \mathbb{R} \to \mathbb{R}$ be strictly increasing on $[0, a]$ with
$(f(t) - f(s)) / (t - s) \le b$ for all $s < t$ in $[0, a]$. Then the graph
$P = \{(t, f(t)) : t \in [0, a]\}$ satisfies $\operatorname{opx}(n, P) = \Theta(n)$ as the real
number $n$ tends to infinity.

The hypothesis $a > 0$ is needed: for $a = 0$ the set $P$ is a single point and
$\operatorname{opx}(n, P) = 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.3
(`integers-2024-A1-thm-4-3`). -/
public theorem_wanted opx_increasing_graph_isTheta {a b : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : StrictMonoOn f (Set.Icc 0 a))
    (hb : ∀ s ∈ Set.Icc 0 a, ∀ t ∈ Set.Icc 0 a, s < t → (f t - f s) / (t - s) ≤ b) :
    (fun n : ℝ => opx n ((fun t => (t, f t)) '' Set.Icc 0 a)) =Θ[Filter.atTop] (fun n : ℝ => n)

/-- **Large sets of grid cells with no $r \times r$ all-ones submatrix.** For all natural numbers
$r \ge 2$ and $n \ge 1$ there is a set $S$ of cells of the $n \times n$ grid
$\{0, \dots, n - 1\}^2$ with $|S| \ge \frac{1}{2} n^{2 - 2/(r+1)}$ that contains no $r \times r$
all-ones submatrix: there are no sets $R, C \subseteq \{0, \dots, n - 1\}$ with $|R| = |C| = r$
and $R \times C \subseteq S$.

In the language of 0-1 matrix extremal functions this says $\operatorname{ex}(n, J_{r,r}) \ge
\frac{1}{2} n^{2-2/(r+1)}$ for the $r \times r$ all-ones matrix $J_{r,r}$; it is the cited
Kővári–Sós–Turán-type lower bound, with the paper's explicit constant.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 4.4
(`integers-2024-A1-lem-4-4`). -/
public theorem_wanted exists_large_Jrr_free_cells {r n : ℕ} (hr : 2 ≤ r) (hn : 1 ≤ n) :
    ∃ S : Finset (Fin n × Fin n),
      (¬ ∃ R C : Finset (Fin n), R.card = r ∧ C.card = r ∧ R ×ˢ C ⊆ S) ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ ((2 : ℝ) - 2 / (r + 1)) ≤ S.card

/-- **Continuous Turán number of the equal-sign pattern.** Let $s > 0$ and $c > 0$ be real numbers
and let $P_{s,2,c} = [0, s] \times \{c, 2c\}$ be the equal-sign pattern, two horizontal segments of
length $s$ at heights $c$ and $2c$. Then, as the real number $n$ tends to infinity with $s$ and
$c$ fixed, $\operatorname{opx}(n, P_{s,2,c}) = \Theta(s^{1/2} n^{3/2})$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.7
(`integers-2024-A1-thm-4-7`); `P_{s,t,c}` as defined before it. -/
public theorem_wanted opx_equal_sign_isTheta {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (fun n : ℝ => opx n (Set.Icc 0 s ×ˢ {c, 2 * c})) =Θ[Filter.atTop]
      (fun n : ℝ => s ^ (1 / 2 : ℝ) * n ^ (3 / 2 : ℝ))

/-- **Lower bound on the volume of a staircase region.** Let $t$ be a natural number and let
$c, n$ be real numbers with $c \ge 0$ and $ct \le n$. Let $X \subseteq \mathbb{R}^t$ be the set of
points $y = (y_0, \dots, y_{t-1})$ such that $y_i < n - ic$ for every $i$, $y_{i+1} + c < y_i$ for
every $i < t - 1$, and $y_{t-1} > 0$ if $t \ge 1$. Then the $t$-dimensional Lebesgue measure of
$X$ is at least $(n/t - c)^t$, where $n/t$ is read as $0$ when $t = 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 4.8
(`integers-2024-A1-lem-4-8`), the explicit bound. -/
public theorem_wanted volume_staircase_simplex_ge {t : ℕ} {c n : ℝ} (hc : 0 ≤ c)
    (hn : c * t ≤ n) :
    ENNReal.ofReal ((n / t - c) ^ t) ≤
      MeasureTheory.volume {y : Fin t → ℝ | (∀ i : Fin t, y i < n - (i : ℕ) * c) ∧
        (∀ i : Fin t, (i : ℕ) + 1 = t → 0 < y i) ∧
        ∀ i j : Fin t, (j : ℕ) = (i : ℕ) + 1 → y j + c < y i}

/-- **Upper bound for stacked horizontal segments.** Let $t \ge 2$ be a natural number, let
$s, c > 0$ be real numbers, and let $P_{s,t,c} = [0, s] \times \{c, 2c, \dots, tc\}$ be the union
of the $t$ horizontal segments of length $s$ at heights $c, 2c, \dots, tc$. Then
$\operatorname{opx}(n, P_{s,t,c}) = O(s^{1/t} n^{2 - 1/t})$ as the real number $n$ tends to
infinity, with $s$, $t$ and $c$ fixed.

Since $s$ is fixed, the factor $s^{1/t}$ only changes the implied constant.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.9
(`integers-2024-A1-thm-4-9`); `P_{s,t,c}` as defined before Theorem 4.7. -/
public theorem_wanted opx_stacked_segments_isBigO {t : ℕ} (ht : 2 ≤ t) {s c : ℝ} (hs : 0 < s)
    (hc : 0 < c) :
    (fun n : ℝ => opx n {p : ℝ × ℝ | p.1 ∈ Set.Icc 0 s ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ p.2 = i * c}) =O[Filter.atTop]
      (fun n : ℝ => s ^ (1 / t : ℝ) * n ^ (2 - 1 / t : ℝ))

/-- **Linear bound for separated horizontal segments.** Let $k$ be a natural number and let
$a_i \le b_i$ and $y_i$ be real numbers for $i = 1, \dots, k$, such that the intervals
$[a_i, b_i]$ are pairwise disjoint and the heights $y_i$ are pairwise distinct, and let
$P = \bigcup_{i=1}^k [a_i, b_i] \times \{y_i\}$. Then the continuous Turán number satisfies
$\operatorname{opx}(n, P) = O(n)$ as the real number $n$ tends to infinity.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.10
(`integers-2024-A1-thm-4-10`). -/
public theorem_wanted opx_horizontal_segments_isBigO {k : ℕ} (a b y : Fin k → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hx : ∀ i j, i ≠ j → Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j)))
    (hy : Function.Injective y) :
    (fun n : ℝ => opx n (⋃ i, Set.Icc (a i) (b i) ×ˢ {y i})) =O[Filter.atTop] (fun n : ℝ => n)

/-- **Containment of a point pattern in a set of grid cells.** A set of cells
$A \subseteq \mathbb{N} \times \mathbb{N}$, each cell written (column, row), contains a set
$P \subseteq \mathbb{R}^2$ when there are maps $f_X, f_Y : \mathbb{R} \to \mathbb{N}$ such that
$f_X$ is strictly increasing on the set of $x$-coordinates of points of $P$, $f_Y$ is strictly
increasing on the set of $y$-coordinates of points of $P$, and $(f_X(x), f_Y(y)) \in A$ for every
$(x, y) \in P$.

For finite $P$ this is containment of the 0-1 matrix $M_P$ of $P$ (rows of $P$ listed bottom to
top; flipping the rows of both matrices preserves containment).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(0-1 matrix containment and the matrix `M_P` of a finite point set). -/
public def CellsContainPattern (A : Set (ℕ × ℕ)) (P : Set (ℝ × ℝ)) : Prop :=
  ∃ fX fY : ℝ → ℕ, StrictMonoOn fX (Prod.fst '' P) ∧ StrictMonoOn fY (Prod.snd '' P) ∧
    ∀ p ∈ P, (fX p.1, fY p.2) ∈ A

/-- **0-1 matrix extremal function of a point pattern.** For a natural number $n$ and a set
$P \subseteq \mathbb{R}^2$, $\mathrm{ex}(n, M_P)$ is the largest number of cells of the
$n \times n$ grid $\{0, \dots, n - 1\}^2$ forming a set that does not contain $P$ (cells contain
$P$ when there are strictly increasing maps from the $x$-coordinates of $P$ to columns and from the
$y$-coordinates of $P$ to rows that send every point of $P$ to a cell of the set), and $0$ if there
is no such set (as for $P = \emptyset$). For finite $P$ this is the 0-1 matrix extremal function
$\mathrm{ex}(n, M_P)$, the maximum number of ones in an $n \times n$ 0-1 matrix that does not
contain the 0-1 matrix $M_P$ of $P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definitions of `ex(n, M)` and of `M_P`). -/
public noncomputable def patternEx (n : ℕ) (P : Set (ℝ × ℝ)) : ℕ :=
  sSup {k | ∃ A : Finset (ℕ × ℕ), A ⊆ Finset.range n ×ˢ Finset.range n ∧ A.card = k ∧
    ¬ CellsContainPattern (A : Set (ℕ × ℕ)) P}

/-- **The extremal function of the empty pattern vanishes.** For every natural number $n$,
$\operatorname{ex}(n, M_\emptyset) = 0$, since every set of cells contains the empty pattern.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definitions of `ex(n, M)` and of `M_P`). -/
public theorem patternEx_empty (n : ℕ) : patternEx n ∅ = 0 := by
  have h : ∀ A : Set (ℕ × ℕ), CellsContainPattern A ∅ :=
    fun A => ⟨fun _ => 0, fun _ => 0, by simp [StrictMonoOn], by simp [StrictMonoOn], by simp⟩
  simp [patternEx, h]

/-- **The extremal function of a single point vanishes.** For every natural number $n$ and every
point $p \in \mathbb{R}^2$, the 0-1 matrix extremal function of the one-point pattern $\{p\}$ on
the $n \times n$ grid is zero: $\mathrm{ex}(n, M_{\{p\}}) = 0$. Indeed, a single point is contained
in every nonempty set of cells.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definitions of `ex(n, M)` and of `M_P`). -/
public theorem patternEx_singleton (n : ℕ) (p : ℝ × ℝ) : patternEx n {p} = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro k ⟨A, -, rfl, hA⟩
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · exact absurd ⟨fun _ => a.1, fun _ => a.2, by simp, by simp, by simpa using ha⟩ hA

/-- **Trivial upper bound for the 0-1 matrix extremal function.** Let $n$ be a natural number and
$P \subseteq \mathbb{R}^2$ a set, and let $\mathrm{ex}(n, M_P)$ be the largest number of cells of
the $n \times n$ grid $\{0, \dots, n - 1\}^2$ forming a set that does not contain $P$ ($0$ if
there is no such set). Then $\mathrm{ex}(n, M_P) \le n^2$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definitions of `ex(n, M)` and of `M_P`). -/
public theorem patternEx_le_sq (n : ℕ) (P : Set (ℝ × ℝ)) : patternEx n P ≤ n ^ 2 := by
  apply csSup_le'
  rintro k ⟨A, hA, rfl, -⟩
  simpa [sq] using Finset.card_le_card hA

/-- **Inverse Ackermann function.** For a natural number $n$, the inverse Ackermann function
$\alpha(n)$ is the least natural number $k$ with $n \le A(k, k)$, where $A$ is the two-argument
Ackermann function, given for all natural numbers $m$ and $j$ by $A(0, j) = j + 1$,
$A(m + 1, 0) = A(m, 1)$ and $A(m + 1, j + 1) = A(m, A(m + 1, j))$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)` in Keszegh's bound quoted before Corollary 3.8). -/
public def inverseAckermann (n : ℕ) : ℕ :=
  Nat.find (⟨n, (lt_ack_left n n).le⟩ : ∃ k, n ≤ ack k k)

/-- **Defining inequality of the inverse Ackermann function.** For every natural number $n$,
$n \le A(\alpha(n), \alpha(n))$, where $\alpha$ is the inverse Ackermann function and $A$ is the
two-argument Ackermann function.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)`). -/
public theorem le_ack_inverseAckermann (n : ℕ) :
    n ≤ ack (inverseAckermann n) (inverseAckermann n) :=
  Nat.find_spec (⟨n, (lt_ack_left n n).le⟩ : ∃ k, n ≤ ack k k)

/-- **Upper bound for the inverse Ackermann function.** For all natural numbers $n$ and $k$, if
$n \le A(k, k)$, where $A$ is the two-argument Ackermann function, then $\alpha(n) \le k$, where
$\alpha$ is the inverse Ackermann function.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)`). -/
public theorem inverseAckermann_le {n k : ℕ} (h : n ≤ ack k k) : inverseAckermann n ≤ k :=
  Nat.find_min' _ h

/-- **The inverse Ackermann function at 2.** The inverse Ackermann function $\alpha$ satisfies
$\alpha(2) = 1$, since $A(0, 0) = 1 < 2 \le 3 = A(1, 1)$, where $A$ is the two-argument
Ackermann function.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)`). -/
public theorem inverseAckermann_two : inverseAckermann 2 = 1 := by
  rw [inverseAckermann, Nat.find_eq_iff]
  refine ⟨by simp, fun k hk => ?_⟩
  interval_cases k
  simp [ack_zero]

/-- **The inverse Ackermann function at 8.** The inverse Ackermann function $\alpha$ satisfies
$\alpha(8) = 3$, since $A(2, 2) = 7 < 8 \le 61 = A(3, 3)$, where $A$ is the two-argument
Ackermann function.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2
(the inverse Ackermann function `α(n)`). -/
public theorem inverseAckermann_eight : inverseAckermann 8 = 3 := by
  rw [inverseAckermann, Nat.find_eq_iff]
  refine ⟨by simp, fun k hk => ?_⟩
  interval_cases k <;> simp

/-- **Continuous Turán numbers versus 0-1 matrix extremal functions.** Let $P$ be a finite subset
of $\mathbb{R}^2$. Then the continuous Turán number $\mathrm{opx}(n, P)$ and the 0-1 matrix
extremal function $\mathrm{ex}(n, M_P)$ of $P$ on the $n \times n$ grid satisfy
$\mathrm{opx}(n, P) = \Theta(\mathrm{ex}(n, M_P))$ as $n \to \infty$ through the natural numbers,
with constants depending on $P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 3.1
(`integers-2024-A1-thm-3-1`). -/
public theorem_wanted opx_isTheta_patternEx {P : Set (ℝ × ℝ)} (hP : P.Finite) :
    (fun n : ℕ => opx n P) =Θ[Filter.atTop] (fun n : ℕ => (patternEx n P : ℝ))

/-- **Lower bound for continuous Turán numbers of finite patterns.** Let $P$ be a finite subset of
$\mathbb{R}^2$. For a natural number $n$, write $\mathrm{opx}(n, P)$ for the continuous Turán
number of $P$ (the supremum of the Lebesgue measures of the open subsets of $[0, n]^2$ that do not
contain $P$, or $0$ if there are none) and $\mathrm{ex}(n, M_P)$ for the 0-1 matrix extremal
function of $P$ on the $n \times n$ grid. Then $\mathrm{ex}(n, M_P) = O(\mathrm{opx}(n, P))$ as
$n \to \infty$ through the natural numbers; that is,
$\mathrm{opx}(n, P) = \Omega(\mathrm{ex}(n, M_P))$, with constants depending on $P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 3.2
(`integers-2024-A1-thm-3-2`). -/
public theorem_wanted patternEx_isBigO_opx {P : Set (ℝ × ℝ)} (hP : P.Finite) :
    (fun n : ℕ => (patternEx n P : ℝ)) =O[Filter.atTop] (fun n : ℕ => opx n P)

/-- **Upper bound for continuous Turán numbers of finite patterns.** Let $P$ be a finite subset of
$\mathbb{R}^2$. Then the continuous Turán number $\mathrm{opx}(n, P)$ and the 0-1 matrix extremal
function $\mathrm{ex}(n, M_P)$ of $P$ on the $n \times n$ grid satisfy
$\mathrm{opx}(n, P) = O(\mathrm{ex}(n, M_P))$ as $n \to \infty$ through the natural numbers.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 3.3
(`integers-2024-A1-thm-3-3`). -/
public theorem_wanted opx_isBigO_patternEx {P : Set (ℝ × ℝ)} (hP : P.Finite) :
    (fun n : ℕ => opx n P) =O[Filter.atTop] (fun n : ℕ => (patternEx n P : ℝ))

/-- **Linear bound for permutation-like point patterns.** There is a real constant $C$ such that
for every real $c > 0$ there is a real constant $K$ with the following property. Let
$P \subseteq \mathbb{R}^2$ be a finite set of $k$ points whose $x$-coordinates are pairwise
distinct and whose $y$-coordinates are pairwise distinct, such that any two consecutive
$x$-coordinates of points of $P$ differ by at most $c$, and so do any two consecutive
$y$-coordinates. Then $\operatorname{opx}(n, P) \le K \cdot 2^{Ck} \cdot n$ for every natural
number $n$.

The paper states the bound as $2^{O(k)} n$, with the implied constant depending on $c$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.4
(`integers-2024-A1-cor-3-4`). -/
public theorem_wanted opx_permutation_pattern_le :
    ∃ C : ℝ, ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ P : Finset (ℝ × ℝ),
      Set.InjOn Prod.fst (P : Set (ℝ × ℝ)) → Set.InjOn Prod.snd (P : Set (ℝ × ℝ)) →
      (∀ p ∈ P, ∀ q ∈ P, p.1 < q.1 → (∀ r ∈ P, ¬ (p.1 < r.1 ∧ r.1 < q.1)) → q.1 - p.1 ≤ c) →
      (∀ p ∈ P, ∀ q ∈ P, p.2 < q.2 → (∀ r ∈ P, ¬ (p.2 < r.2 ∧ r.2 < q.2)) → q.2 - p.2 ≤ c) →
      ∀ n : ℕ, opx n P ≤ K * (2 : ℝ) ^ (C * P.card) * n

/-- **Upper bound for the continuous Turán number of a grid.** Let $X$ and $Y$ be finite sets of
real numbers, let $P = X \times Y$ be the grid they span and let $t = |X|$ be its number of
columns. Then $\operatorname{opx}(n, P) = O(n^{2 - 1/t})$ as the natural number $n$ tends to
infinity, where for $t = 0$ (so that $P$ is empty) the exponent $2 - 1/t$ is read as $2$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.5
(`integers-2024-A1-cor-3-5`). -/
public theorem_wanted opx_grid_isBigO (X Y : Finset ℝ) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (2 - 1 / (X.card : ℝ)))

/-- **Power saving for continuous Turán numbers of finite planar patterns.** Let
$P \subseteq \mathbb{R}^2$ be finite. Then there is a real number $\varepsilon > 0$ such that the
continuous Turán number satisfies $\operatorname{opx}(n, P) = O(n^{2 - \varepsilon})$ as the
natural number $n$ tends to infinity.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.6
(`integers-2024-A1-cor-3-6`). -/
public theorem_wanted exists_opx_isBigO_rpow {P : Set (ℝ × ℝ)} (hP : P.Finite) :
    ∃ ε : ℝ, 0 < ε ∧
      (fun n : ℕ => opx n P) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (2 - ε))

/-- **Continuous Turán number of a grid with two columns.** Let $X$ and $Y$ be finite sets of real
numbers with $|X| = 2$ and $|Y| \ge 2$, and let $P = X \times Y$ be the grid with $2$ columns and
$|Y|$ rows. Then $\operatorname{opx}(n, P) = \Theta(n^{3/2})$ as the natural number $n$ tends to
infinity.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.7
(`integers-2024-A1-cor-3-7`), first sentence. -/
public theorem_wanted opx_grid_two_columns_isTheta {X Y : Finset ℝ} (hX : X.card = 2)
    (hY : 2 ≤ Y.card) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =Θ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ))

/-- **Continuous Turán number of a grid with three columns.** Let $X$ and $Y$ be finite sets of
real numbers with $|X| = 3$ and $|Y| \ge 3$, and let $P = X \times Y$ be the grid with $3$ columns
and $|Y|$ rows. Then $\operatorname{opx}(n, P) = \Theta(n^{5/3})$ as the natural number $n$ tends
to infinity.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.7
(`integers-2024-A1-cor-3-7`), second sentence. -/
public theorem_wanted opx_grid_three_columns_isTheta {X Y : Finset ℝ} (hX : X.card = 3)
    (hY : 3 ≤ Y.card) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =Θ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ))

/-- **Almost linear bound for patterns with at most one point in each row.** Let
$P \subseteq \mathbb{R}^2$ be a finite set whose points have pairwise distinct $y$-coordinates.
Then there is a natural number $t$ such that $\operatorname{opx}(n, P) = O(n \cdot 2^{\alpha(n)^t})$
as the natural number $n$ tends to infinity, where $\operatorname{opx}$ is the continuous Turán
number and $\alpha$ is the inverse Ackermann function.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.8
(`integers-2024-A1-cor-3-8`). -/
public theorem_wanted exists_opx_isBigO_inverseAckermann {P : Set (ℝ × ℝ)} (hP : P.Finite)
    (hrow : Set.InjOn Prod.snd P) :
    ∃ t : ℕ, (fun n : ℕ => opx n P) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) * 2 ^ (inverseAckermann n ^ t))

/-- **Two-row patterns of growing width.** For each real $n$ let $Q_n \subseteq \mathbb{R}^2$
be a set all of whose points have $y$-coordinate $0$ or $1$, whose least $x$-coordinate is $0$
and whose greatest $x$-coordinate is $s(n)$. Then the following are equivalent: for every
$\varepsilon > 0$, $\operatorname{opx}(n, Q_n) \ge n^{2 - \varepsilon}$ for all sufficiently large
real $n$; and for every $\varepsilon > 0$, $s(n) \ge n^{1 - \varepsilon}$ for all sufficiently
large real $n$.

In asymptotic notation: $\operatorname{opx}(n, Q_n) = \Omega(n^{2 - o(1)})$ if and only if
$s(n) = \Omega(n^{1 - o(1)})$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1,
Proposition 6.4 (`integers-2024-A1-prop-6-4`). -/
public theorem_wanted opx_two_row_growing_iff (s : ℝ → ℝ) (Q : ℝ → Set (ℝ × ℝ))
    (hmin : ∀ n, IsLeast (Prod.fst '' Q n) 0) (hmax : ∀ n, IsGreatest (Prod.fst '' Q n) (s n))
    (hy : ∀ n, ∀ p ∈ Q n, p.2 = 0 ∨ p.2 = 1) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, n ^ (2 - ε) ≤ opx n (Q n)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, n ^ (1 - ε) ≤ s n

/-- **Saturating sets for a point pattern.** Let $n$ be a real number and let $P$ and $S$ be
subsets of $\mathbb{R}^2$. Then $S$ is saturating for $P$ in $[0, n]^2$ when $S$ is an open
subset of $[0, n]^2$ that does not contain $P$, while every open set $S'$ with
$S \subsetneq S' \subseteq [0, n]^2$ contains $P$. Here a set $T$ contains $P$ when there are
maps $f_X, f_Y : \mathbb{R} \to \mathbb{R}$ such that $f_X(x) - f_X(x') \ge x - x'$ whenever
$x > x'$ are $x$-coordinates of points of $P$, likewise $f_Y(y) - f_Y(y') \ge y - y'$ whenever
$y > y'$ are $y$-coordinates of points of $P$, and $(f_X(x), f_Y(y)) \in T$ for every
$(x, y) \in P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6
(definition of saturating sets). -/
public def IsOpxSaturating (n : ℝ) (P S : Set (ℝ × ℝ)) : Prop :=
  IsOpen S ∧ S ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n ∧ ¬ PointSetContainsPattern S P ∧
    ∀ S' : Set (ℝ × ℝ), IsOpen S' → S' ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n → S ⊂ S' →
      PointSetContainsPattern S' P

/-- **Saturation function for continuous patterns.** For a real number $n$ and a set
$P \subseteq \mathbb{R}^2$, call an open set $S \subseteq [0, n]^2$ saturating for $P$ if $S$
does not contain $P$ but every open set $S' \subseteq [0, n]^2$ properly containing $S$ contains
$P$ (containment in the sense of point-set pattern containment). The saturation function
$\operatorname{osat}(n, P)$ is the infimum of the Lebesgue measures $\mu_2(S)$ over all sets $S$
saturating for $P$, and is $0$ when no saturating set exists.

The paper leaves $\operatorname{osat}(n, P)$ undefined when no saturating set exists.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6
(definition of `osat(n, P)`). -/
public noncomputable def osat (n : ℝ) (P : Set (ℝ × ℝ)) : ℝ :=
  sInf ((fun S => (MeasureTheory.volume S).toReal) '' {S | IsOpxSaturating n P S})

/-- **The saturation function is nonnegative.** For every real number $n$ and every set
$P \subseteq \mathbb{R}^2$, $\operatorname{osat}(n, P) \ge 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6
(definition of `osat(n, P)`). -/
public theorem osat_nonneg (n : ℝ) (P : Set (ℝ × ℝ)) : 0 ≤ osat n P := by
  apply Real.sInf_nonneg
  rintro _ ⟨S, -, rfl⟩
  exact ENNReal.toReal_nonneg

/-- **Saturation function and continuous Turán number of a single point.** For every real number
$n$ and every point $p \in \mathbb{R}^2$, $\operatorname{osat}(n, \{p\}) = 0$ and
$\operatorname{opx}(n, \{p\}) = 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 6.5
(`integers-2024-A1-lem-6-5`). -/
public theorem_wanted osat_singleton_and_opx_singleton (n : ℝ) (p : ℝ × ℝ) :
    osat n {p} = 0 ∧ opx n {p} = 0

/-- **Containment of point sets in $\mathbb{R}^d$.** Let $d$ be a natural number and let
$S, P \subseteq \mathbb{R}^d$. Then $S$ contains $P$ when there are maps
$f_1, \dots, f_d : \mathbb{R} \to \mathbb{R}$ that expand distances between coordinates of points
of $P$, that is, $f_i(p_i) - f_i(q_i) \ge p_i - q_i$ for every $i$ and all $p, q \in P$ with
$p_i > q_i$, and such that $(f_1(p_1), \dots, f_d(p_d)) \in S$ for every $p \in P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of containment in `ℝ^d`). -/
public def ContainsPatternD {d : ℕ} (S P : Set (Fin d → ℝ)) : Prop :=
  ∃ f : Fin d → ℝ → ℝ,
    (∀ i, ∀ p ∈ P, ∀ q ∈ P, q i < p i → p i - q i ≤ f i (p i) - f i (q i)) ∧
    ∀ p ∈ P, (fun i => f i (p i)) ∈ S

/-- **Every set in $\mathbb{R}^d$ contains the empty pattern.** For every natural number $d$ and
every set $S \subseteq \mathbb{R}^d$, $S$ contains the empty set $\emptyset \subseteq \mathbb{R}^d$
in the sense of containment of point sets in $\mathbb{R}^d$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of containment in `ℝ^d`). -/
public theorem containsPatternD_empty {d : ℕ} (S : Set (Fin d → ℝ)) : ContainsPatternD S ∅ :=
  ⟨fun _ => id, by simp, by simp⟩

/-- **Continuous Turán number in $\mathbb{R}^d$.** For a natural number $d$, a real number $n$
and a set $P \subseteq \mathbb{R}^d$, the continuous Turán number $\mathrm{opx}(n, P, d)$ is the
supremum of the $d$-dimensional Lebesgue measures $\mu_d(S)$ over all open sets
$S \subseteq [0, n]^d$ that do not contain $P$ in the sense of containment of point sets in
$\mathbb{R}^d$; it is $0$ when there is no such set.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of `opx(n, P, d)`). -/
public noncomputable def opxD (d : ℕ) (n : ℝ) (P : Set (Fin d → ℝ)) : ℝ :=
  sSup ((fun S => (MeasureTheory.volume S).toReal) ''
    {S | IsOpen S ∧ S ⊆ Set.Icc 0 (fun _ => n) ∧ ¬ ContainsPatternD S P})

/-- **Higher-dimensional continuous Turán numbers are nonnegative.** For every dimension $d$,
real number $n$ and set $P \subseteq \mathbb{R}^d$, $\mathrm{opx}(n, P, d) \ge 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of `opx(n, P, d)`). -/
public theorem opxD_nonneg (d : ℕ) (n : ℝ) (P : Set (Fin d → ℝ)) : 0 ≤ opxD d n P := by
  apply Real.sSup_nonneg
  rintro _ ⟨S, -, rfl⟩
  exact ENNReal.toReal_nonneg

/-- **The higher-dimensional continuous Turán number of the empty pattern.** For every dimension
$d$ and every real number $n$, $\mathrm{opx}(n, \emptyset, d) = 0$: every set contains the empty
pattern, so no set is free of it.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of `opx(n, P, d)`). -/
public theorem opxD_empty (d : ℕ) (n : ℝ) : opxD d n ∅ = 0 := by
  simp [opxD, containsPatternD_empty]

/-- **Containment of a point pattern in d-dimensional grid cells.** Let $d$ be a natural number,
let $A \subseteq \mathbb{N}^d$ be a set of cells and let $P \subseteq \mathbb{R}^d$. Then $A$
contains $P$ when there are maps $f_1, \dots, f_d : \mathbb{R} \to \mathbb{N}$ such that each $f_i$
is strictly increasing on the set $\{p_i : p \in P\}$ of $i$-th coordinates of points of $P$, and
$(f_1(p_1), \dots, f_d(p_d)) \in A$ for every $p \in P$.

For finite $P$ this is containment of the $d$-dimensional 0-1 matrix $M_P$ of $P$ in the 0-1
matrix whose ones are the cells of $A$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(containment of `d`-dimensional 0-1 matrices and the matrix `M_P`). -/
public def CellsContainPatternD {d : ℕ} (A : Set (Fin d → ℕ)) (P : Set (Fin d → ℝ)) : Prop :=
  ∃ f : Fin d → ℝ → ℕ, (∀ i, StrictMonoOn (f i) ((fun p => p i) '' P)) ∧
    ∀ p ∈ P, (fun i => f i (p i)) ∈ A

/-- **Extremal function of a $d$-dimensional pattern.** For natural numbers $d$ and $n$ and a set
$P \subseteq \mathbb{R}^d$, say that a set $A$ of cells of $\mathbb{N}^d$ contains $P$ when there
are maps $f_1, \dots, f_d$ to $\mathbb{N}$, each $f_i$ strictly increasing on the $i$-th
coordinates of the points of $P$, with $(f_1(p_1), \dots, f_d(p_d)) \in A$ for every $p \in P$.
Then $\operatorname{ex}(n, M_P, d)$ is the largest number of cells of a set of cells of the grid
$\{0, \dots, n - 1\}^d$ that does not contain $P$, and is $0$ when every such set contains $P$.
For finite $P$ this is the $d$-dimensional 0-1 matrix extremal function of the matrix $M_P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definitions of `ex(n, M, d)` and of `M_P`). -/
public noncomputable def patternExD (d n : ℕ) (P : Set (Fin d → ℝ)) : ℕ :=
  sSup {k | ∃ A : Finset (Fin d → ℕ), (∀ a ∈ A, ∀ i, a i < n) ∧ A.card = k ∧
    ¬ CellsContainPatternD (A : Set (Fin d → ℕ)) P}

/-- **The $d$-dimensional extremal function of the empty pattern vanishes.** For all natural
numbers $d$ and $n$, $\operatorname{ex}(n, M_\emptyset, d) = 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definitions of `ex(n, M, d)` and of `M_P`). -/
public theorem patternExD_empty (d n : ℕ) : patternExD d n ∅ = 0 := by
  have h : ∀ A : Set (Fin d → ℕ), CellsContainPatternD A ∅ :=
    fun A => ⟨fun _ _ => 0, fun _ => by simp [StrictMonoOn], by simp⟩
  simp [patternExD, h]

/-- **The $d$-dimensional extremal function of a single point vanishes.** For all natural numbers
$d$ and $n$ and every point $p \in \mathbb{R}^d$, $\operatorname{ex}(n, M_{\{p\}}, d) = 0$, since a
single point is contained in every nonempty set of cells.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definitions of `ex(n, M, d)` and of `M_P`). -/
public theorem patternExD_singleton (d n : ℕ) (p : Fin d → ℝ) : patternExD d n {p} = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro k ⟨A, -, rfl, hA⟩
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · exact absurd ⟨fun i _ => a i, fun i => by simp, by simpa using ha⟩ hA

/-- **Higher-dimensional continuous Turán numbers are monotone under containment.** Let
$P, Q \subseteq \mathbb{R}^d$. If $Q$ contains $P$, then
$\mathrm{opx}(n, P, d) \le \mathrm{opx}(n, Q, d)$ for every real number $n$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.1
(`integers-2024-A1-lem-5-1`). -/
public theorem_wanted opxD_mono_of_containsPatternD {d : ℕ} (n : ℝ) {P Q : Set (Fin d → ℝ)}
    (h : ContainsPatternD Q P) : opxD d n P ≤ opxD d n Q

/-- **Higher-dimensional continuous Turán numbers are monotone in the side length.** For every
set $P \subseteq \mathbb{R}^d$ and all real numbers $m \le n$,
$\mathrm{opx}(m, P, d) \le \mathrm{opx}(n, P, d)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.2
(`integers-2024-A1-lem-5-2`). -/
public theorem_wanted opxD_mono_left {d : ℕ} (P : Set (Fin d → ℝ)) {m n : ℝ} (hmn : m ≤ n) :
    opxD d m P ≤ opxD d n P

/-- **Increment bound for the d-dimensional continuous Turán number.** Let $d \ge 2$ be a
natural number, let $P \subseteq \mathbb{R}^d$, and let $n, \varepsilon$ be real numbers with
$n > 0$ and $0 < \varepsilon < n$. Then the $d$-dimensional continuous Turán number
$\mathrm{opx}$ satisfies $\mathrm{opx}(n, P, d) \le \mathrm{opx}(n + \varepsilon, P, d)$ and
$\mathrm{opx}(n + \varepsilon, P, d) < \mathrm{opx}(n, P, d) + d (2n)^{d-1} \varepsilon$.

The hypothesis $d \ge 2$ is needed: for $d = 1$ and $P = \{0, L\}$ with $L > n + \varepsilon$,
every open subset of $[0, n + \varepsilon]$ avoids $P$, so
$\mathrm{opx}(n + \varepsilon, P, 1) = n + \varepsilon = \mathrm{opx}(n, P, 1) + \varepsilon$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.3
(`integers-2024-A1-lem-5-3`). -/
public theorem_wanted opxD_add_lt {d : ℕ} (hd : 2 ≤ d) (P : Set (Fin d → ℝ)) {n ε : ℝ}
    (hn : 0 < n) (hε : 0 < ε) (hεn : ε < n) :
    opxD d n P ≤ opxD d (n + ε) P ∧ opxD d (n + ε) P < opxD d n P + d * (2 * n) ^ (d - 1) * ε

/-- **Continuity of the d-dimensional continuous Turán number.** For every natural number $d$
and every $P \subseteq \mathbb{R}^d$, the $d$-dimensional continuous Turán number
$\mathrm{opx}(n, P, d)$ is a continuous function of $n$ on $(0, \infty)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Proposition 5.4
(`integers-2024-A1-prop-5-4`). -/
public theorem_wanted opxD_continuousOn {d : ℕ} (P : Set (Fin d → ℝ)) :
    ContinuousOn (fun n => opxD d n P) (Set.Ioi 0)

/-- **Projection bound for the d-dimensional continuous Turán number.** Let $d$ be a natural
number, $n$ a real number and $P \subseteq \mathbb{R}^{d+1}$, and let $\Pr(P)$ be the subset of
$\mathbb{R}^d$ obtained by dropping the last coordinate of every point of $P$. Writing
$\mathrm{opx}(n, Q, k)$ for the $k$-dimensional continuous Turán number, we have
$n \cdot \mathrm{opx}(n, \Pr(P), d) \le \mathrm{opx}(n, P, d + 1)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.5
(`integers-2024-A1-lem-5-5`); `Pr(P)` as defined before it. -/
public theorem_wanted mul_opxD_init_le {d : ℕ} (n : ℝ) (P : Set (Fin (d + 1) → ℝ)) :
    n * opxD d n (Fin.init '' P) ≤ opxD (d + 1) n P

/-- **Patterns with a constant last coordinate.** Let $P \subseteq \mathbb{R}^{d+1}$ be a set
whose points all have the same last coordinate, and let $\mathrm{Pr}(P) \subseteq \mathbb{R}^d$ be
the set obtained by deleting the last coordinate of each point of $P$. Then for every real number
$n$, $\mathrm{opx}(n, P, d + 1) = n \cdot \mathrm{opx}(n, \mathrm{Pr}(P), d)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Proposition 5.6
(`integers-2024-A1-prop-5-6`). -/
public theorem_wanted opxD_eq_mul_opxD_init {d : ℕ} (n : ℝ) {P : Set (Fin (d + 1) → ℝ)}
    (hP : ∃ z, ∀ p ∈ P, p (Fin.last d) = z) :
    opxD (d + 1) n P = n * opxD d n (Fin.init '' P)

/-- **Rational points of an embedded open planar set.** Let $m$ be a natural number and let
$P \subseteq \mathbb{R}^2$ be a nonempty open set. Let
$P' = P \times \{0\}^{m+1} \subseteq \mathbb{R}^{m+3}$, and let $Q_{P'}$ be the set of points of
$P'$ all of whose coordinates are rational. Then $\mathrm{opx}(n, Q_{P'}, m + 3) = \Theta(n^{m+3})$
as the real number $n$ tends to infinity.

Nonemptiness is added: for $P = \emptyset$ the set $Q_{P'}$ is empty.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.7
(`integers-2024-A1-cor-5-7`). -/
public theorem_wanted opxD_rational_points_embed_isTheta (m : ℕ) {P : Set (ℝ × ℝ)}
    (hP : IsOpen P) (hne : P.Nonempty) :
    (fun n : ℝ => opxD (m + 3) n {v | (v 0, v 1) ∈ P ∧
        (∀ i : Fin (m + 3), 2 ≤ (i : ℕ) → v i = 0) ∧ ∀ i, ∃ q : ℚ, v i = q}) =Θ[Filter.atTop]
      (fun n : ℝ => n ^ (m + 3))

/-- **Nonempty open patterns in dimension at least two.** Let $d \ge 2$, let
$P \subseteq \mathbb{R}^d$ be a nonempty open set, and let $Q_P$ be the set of points of $P$ all
of whose coordinates are rational. Then, as the real number $n \to \infty$,
$\mathrm{opx}(n, P, d) = \Theta(n^d)$ and $\mathrm{opx}(n, Q_P, d) = \Theta(n^d)$.

The paper states this without the hypotheses $P \neq \emptyset$ and $d \ge 2$; both are needed:
$\mathrm{opx}(n, \emptyset, d) = 0$, and for $d = 1$ the interval $P = (0, 1)$ has
$\mathrm{opx}(n, P, 1) \le 1$, since a $P$-free open set $S$ has Lebesgue measure at most $1$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.8
(`integers-2024-A1-cor-5-8`). -/
public theorem_wanted opxD_open_isTheta {d : ℕ} (hd : 2 ≤ d) {P : Set (Fin d → ℝ)}
    (hP : IsOpen P) (hne : P.Nonempty) :
    (fun n : ℝ => opxD d n P) =Θ[Filter.atTop] (fun n : ℝ => n ^ d) ∧
      (fun n : ℝ => opxD d n {p ∈ P | ∀ i, ∃ q : ℚ, p i = q}) =Θ[Filter.atTop]
        (fun n : ℝ => n ^ d)

/-- **Dilation bound for the d-dimensional continuous Turán number.** Let $d$ be a natural
number, let $P \subseteq \mathbb{R}^d$ be finite and let $c_1, c_2, q, n$ be real numbers with
$c_1 > 0$, $q > 1$ and $n > 0$. Suppose that for every coordinate $i$ and all $p, p' \in P$ with
$p_i < p'_i$ such that no $r \in P$ has $p_i < r_i < p'_i$, we have
$c_1 \le p'_i - p_i \le c_2$. Let $qP = \{q p : p \in P\}$ and
$m = \lceil q c_2 / c_1 \rceil + 1$. Then the $d$-dimensional continuous Turán number
$\mathrm{opx}$ satisfies
$$
\mathrm{opx}(n, qP, d) \le
m^d \, \mathrm{opx}(\lceil \lceil n / c_1 \rceil / m \rceil \, c_1, P, d).
$$

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.10
(`integers-2024-A1-lem-5-10`). -/
public theorem_wanted opxD_dilate_le {d : ℕ} {P : Set (Fin d → ℝ)} (hP : P.Finite)
    {c₁ c₂ q n : ℝ} (hc : 0 < c₁) (hq : 1 < q) (hn : 0 < n)
    (hgap : ∀ i, ∀ p ∈ P, ∀ p' ∈ P, p i < p' i → (∀ r ∈ P, ¬ (p i < r i ∧ r i < p' i)) →
      c₁ ≤ p' i - p i ∧ p' i - p i ≤ c₂) :
    opxD d n ((fun p => q • p) '' P) ≤
      ((⌈q * c₂ / c₁⌉ : ℝ) + 1) ^ d *
        opxD d ((⌈(⌈n / c₁⌉ : ℝ) / ((⌈q * c₂ / c₁⌉ : ℝ) + 1)⌉ : ℝ) * c₁) P

/-- **Higher-dimensional continuous Turán numbers versus extremal functions.** Let $d$ be a
natural number and let $P \subseteq \mathbb{R}^d$ be finite. Then the $d$-dimensional continuous
Turán number $\mathrm{opx}(n, P, d)$ and the $d$-dimensional 0-1 matrix extremal function
$\mathrm{ex}(n, M_P, d)$ of $P$ satisfy $\mathrm{opx}(n, P, d) = \Theta(\mathrm{ex}(n, M_P, d))$
as the natural number $n$ tends to infinity, with constants depending on $P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 5.11
(`integers-2024-A1-thm-5-11`). -/
public theorem_wanted opxD_isTheta_patternExD {d : ℕ} {P : Set (Fin d → ℝ)} (hP : P.Finite) :
    (fun n : ℕ => opxD d n P) =Θ[Filter.atTop] (fun n : ℕ => (patternExD d n P : ℝ))

/-- **Upper bound for higher-dimensional permutation-type patterns.** For every $d$ there is a
real number $C$ such that for every real $c > 0$ there is a real number $K$ with the following
property. Let $P \subseteq \mathbb{R}^d$ be a finite set of $k$ points such that, for each
coordinate $i$, distinct points of $P$ have distinct $i$-th coordinates and consecutive values of
the $i$-th coordinate on $P$ differ by at most $c$. Then
$\mathrm{opx}(n, P, d) \le K \cdot 2^{Ck} \cdot n^{d-1}$ for every natural number $n$, where
$n^{d-1}$ means $1$ when $d = 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.12
(`integers-2024-A1-cor-5-12`). -/
public theorem_wanted opxD_permutation_pattern_le (d : ℕ) :
    ∃ C : ℝ, ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ P : Finset (Fin d → ℝ),
      (∀ i, Set.InjOn (fun p : Fin d → ℝ => p i) (P : Set (Fin d → ℝ))) →
      (∀ i, ∀ p ∈ P, ∀ q ∈ P, p i < q i → (∀ r ∈ P, ¬ (p i < r i ∧ r i < q i)) →
        q i - p i ≤ c) →
      ∀ n : ℕ, opxD d n P ≤ K * (2 : ℝ) ^ (C * P.card) * (n : ℝ) ^ (d - 1)

/-- **Upper bound for higher-dimensional grid patterns.** Let $X_1, \dots, X_d$ be finite sets of
real numbers, $k_i = |X_i|$, and $P = X_1 \times \dots \times X_d \subseteq \mathbb{R}^d$. Put
$\alpha = \max_i k_i / \prod_i k_i$ if $d \ge 1$ and every $k_i$ is positive, and $\alpha = 0$
otherwise. Then $\mathrm{opx}(n, P, d) = O(n^{d - \alpha})$ as the natural number $n \to \infty$.

When some $k_i = 0$ the grid $P$ is empty and the bound reads $O(n^d)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.13
(`integers-2024-A1-cor-5-13`). -/
public theorem_wanted opxD_grid_isBigO {d : ℕ} (X : Fin d → Finset ℝ) :
    (fun n : ℕ => opxD d n (Set.univ.pi fun i => (X i : Set ℝ))) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ ((d : ℝ) -
        ((Finset.univ.sup fun i => (X i).card : ℕ) : ℝ) / ((∏ i, (X i).card : ℕ) : ℝ)))

/-- **Power saving for continuous Turán numbers of finite patterns in $\mathbb{R}^d$.** Let $d$
be a natural number and let $P \subseteq \mathbb{R}^d$ be finite. Then there is a real number
$\varepsilon > 0$ such that the $d$-dimensional continuous Turán number satisfies
$\mathrm{opx}(n, P, d) = O(n^{d - \varepsilon})$ as the natural number $n$ tends to infinity.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.14
(`integers-2024-A1-cor-5-14`). -/
public theorem_wanted exists_opxD_isBigO_rpow {d : ℕ} {P : Set (Fin d → ℝ)} (hP : P.Finite) :
    ∃ ε : ℝ, 0 < ε ∧
      (fun n : ℕ => opxD d n P) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ ((d : ℝ) - ε))

/-- **Stacked permutation patterns in three dimensions.** Let $P \subseteq \mathbb{R}^2$ be a
finite set of at least two points with pairwise distinct $x$-coordinates and pairwise distinct
$y$-coordinates, and for $i \in \{2, 3\}$ let
$P_i = \{(x, y, j) : (x, y) \in P,\ j \in \{1, \dots, i\}\} \subseteq \mathbb{R}^3$. Then, as $n$
tends to infinity through the natural numbers, $\mathrm{opx}(n, P_2, 3) = \Theta(n^{5/2})$ and
$\mathrm{opx}(n, P_3, 3) = \Theta(n^{8/3})$.

The requirement of at least two points is the paper's standing assumption on the permutation
matrix: for a single point, $P_2$ is two points on a vertical line and
$\mathrm{opx}(n, P_2, 3) \le n^2$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.15
(`integers-2024-A1-cor-5-15`). -/
public theorem_wanted opxD_permutation_stack_isTheta {P : Finset (ℝ × ℝ)} (hk : 2 ≤ P.card)
    (hx : Set.InjOn Prod.fst (P : Set (ℝ × ℝ))) (hy : Set.InjOn Prod.snd (P : Set (ℝ × ℝ))) :
    (fun n : ℕ => opxD 3 n {v | (v 0, v 1) ∈ P ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ 2 ∧ v 2 = j})
        =Θ[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (5 / 2 : ℝ)) ∧
      (fun n : ℕ => opxD 3 n {v | (v 0, v 1) ∈ P ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ 3 ∧ v 2 = j})
        =Θ[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (8 / 3 : ℝ))

/-- **Upper bound for continuous Turán numbers of stacked patterns.** Let $d \ge 2$ and $t \ge 2$
be natural numbers and let $c > 0$. For $P \subseteq \mathbb{R}^d$ let
$Q_{P,t,c} = \{(x, ic) : x \in P,\ i \in \{1, \dots, t\}\} \subseteq \mathbb{R}^{d+1}$. Then there
is a real constant $K$, depending only on $d$, $t$ and $c$, such that for every
$P \subseteq \mathbb{R}^d$ and every real $n > 0$,
$\mathrm{opx}(n, Q_{P,t,c}, d + 1) \le
K \left(\mathrm{opx}(n, P, d)^{1/t} \, n^{d + 1 - d/t} + n^d\right)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 5.16
(`integers-2024-A1-thm-5-16`); `Q_{P,t,c}` as defined before it. -/
public theorem_wanted opxD_stack_le (d t : ℕ) (hd : 2 ≤ d) (ht : 2 ≤ t) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, ∀ (P : Set (Fin d → ℝ)) (n : ℝ), 0 < n →
      opxD (d + 1) n {v | Fin.init v ∈ P ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ v (Fin.last d) = i * c} ≤
        K * (opxD d n P ^ (1 / t : ℝ) * n ^ ((d : ℝ) + 1 - d / t) + n ^ d)

/-- **Two-layer stacks of patterns with linear continuous Turán number.** Let
$P \subseteq \mathbb{R}^2$ have at least two points, and suppose that
$\mathrm{opx}(n, P) = O(n)$ as the real number $n$ tends to infinity. Let $c > 0$ and
$Q_{P,2,c} = \{(x, y, z) : (x, y) \in P,\ z \in \{c, 2c\}\} \subseteq \mathbb{R}^3$. Then
$\mathrm{opx}(n, Q_{P,2,c}, 3) = \Theta(n^{5/2})$ as the real number $n$ tends to infinity.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.17
(`integers-2024-A1-cor-5-17`), first sentence. -/
public theorem_wanted opxD_stack_two_isTheta {P : Set (ℝ × ℝ)} (hP : P.Nontrivial)
    (hlin : (fun n : ℝ => opx n P) =O[Filter.atTop] (fun n : ℝ => n)) {c : ℝ} (hc : 0 < c) :
    (fun n : ℝ => opxD 3 n {v | (v 0, v 1) ∈ P ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * c})
      =Θ[Filter.atTop] (fun n : ℝ => n ^ (5 / 2 : ℝ))

/-- **Three-layer stacks of patterns with linear continuous Turán number.** Let
$P \subseteq \mathbb{R}^2$ contain three points with pairwise distinct $x$-coordinates, and
suppose that $\mathrm{opx}(n, P) = O(n)$ as the real number $n$ tends to infinity. Let $c > 0$
and $Q_{P,3,c} = \{(x, y, z) : (x, y) \in P,\ z \in \{c, 2c, 3c\}\} \subseteq \mathbb{R}^3$. Then
$\mathrm{opx}(n, Q_{P,3,c}, 3) = \Theta(n^{8/3})$ as the real number $n$ tends to infinity.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.17
(`integers-2024-A1-cor-5-17`), second sentence. -/
public theorem_wanted opxD_stack_three_isTheta {P : Set (ℝ × ℝ)}
    (hP : ∃ p ∈ P, ∃ q ∈ P, ∃ r ∈ P, p.1 ≠ q.1 ∧ p.1 ≠ r.1 ∧ q.1 ≠ r.1)
    (hlin : (fun n : ℝ => opx n P) =O[Filter.atTop] (fun n : ℝ => n)) {c : ℝ} (hc : 0 < c) :
    (fun n : ℝ => opxD 3 n {v | (v 0, v 1) ∈ P ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c})
      =Θ[Filter.atTop] (fun n : ℝ => n ^ (8 / 3 : ℝ))

/-- **Stacked graphs of increasing functions in three dimensions.** Let $a > 0$, $b$ and $c > 0$
be real numbers and let $f : \mathbb{R} \to \mathbb{R}$ be strictly increasing on $[0, a]$ with
$(f(t) - f(s)) / (t - s) \le b$ whenever $0 \le s < t \le a$. Let
$P = \{(t, f(t)) : t \in [0, a]\}$ be the graph of $f$ over $[0, a]$ and, for $k \ge 1$, let
$Q_{P,k,c} = \{(x, y, ic) : (x, y) \in P,\ i \in \{1, \dots, k\}\} \subseteq \mathbb{R}^3$. Then,
as the real number $n \to \infty$, $\mathrm{opx}(n, Q_{P,2,c}, 3) = \Theta(n^{5/2})$ and
$\mathrm{opx}(n, Q_{P,3,c}, 3) = \Theta(n^{8/3})$.

The hypothesis $a > 0$ excludes the degenerate cases where the graph $P$ is a single point
($a = 0$) or empty ($a < 0$).

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.18
(`integers-2024-A1-cor-5-18`). -/
public theorem_wanted opxD_graph_stack_isTheta {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Icc 0 a))
    (hb : ∀ s ∈ Set.Icc 0 a, ∀ t ∈ Set.Icc 0 a, s < t → (f t - f s) / (t - s) ≤ b) :
    (fun n : ℝ => opxD 3 n {v | (∃ t ∈ Set.Icc 0 a, v 0 = t ∧ v 1 = f t) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (5 / 2 : ℝ)) ∧
      (fun n : ℝ => opxD 3 n {v | (∃ t ∈ Set.Icc 0 a, v 0 = t ∧ v 1 = f t) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (8 / 3 : ℝ))

/-- **Stacked plus signs in three dimensions.** Let $r > 0$ and $c > 0$, let
$P = \{(x, y) \in \mathbb{R}^2 : |x| \le r,\ |y| \le r,\ x = 0 \text{ or } y = 0\}$ be the plus
sign of size $r$, and for $t \in \{2, 3\}$ let
$Q_{P,t,c} = \{(x, y, ic) : (x, y) \in P,\ i \in \{1, \dots, t\}\} \subseteq \mathbb{R}^3$. Then,
as the real number $n$ tends to infinity, $\mathrm{opx}(n, Q_{P,2,c}, 3) = \Theta(n^{5/2})$ and
$\mathrm{opx}(n, Q_{P,3,c}, 3) = \Theta(n^{8/3})$.

The paper's size parameter $d$ is renamed $r$, and $r > 0$ is added: for $r = 0$, $Q_{P,2,c}$ is
two points on a vertical line and $\mathrm{opx}(n, Q_{P,2,c}, 3) \le c n^2$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.19
(`integers-2024-A1-cor-5-19`). -/
public theorem_wanted opxD_plus_stack_isTheta {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (fun n : ℝ => opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (5 / 2 : ℝ)) ∧
      (fun n : ℝ => opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (8 / 3 : ℝ))

end

end MetaMathlibExt
