/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.SpecialFunctions.Exp

namespace MetaMathlibExt

@[expose] public section

/-- **Linear chord diagrams.** A linear chord diagram on the $2n$ vertices $0, \dots, 2n-1$, laid
out on a line, is encoded by a map $\sigma$ from $\{0, \dots, 2n-1\}$ to itself that is a
fixed-point-free involution: $\sigma(i) \ne i$ and $\sigma(\sigma(i)) = i$ for every vertex $i$.
Vertex $i$ is joined by a chord to $\sigma(i)$.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Section 1 (linear chord diagrams on `2n` vertices). -/
def IsLinearChordDiagram (n : ℕ) (σ : Fin (2 * n) → Fin (2 * n)) : Prop :=
  ∀ i, σ i ≠ i ∧ σ (σ i) = i

instance (n : ℕ) : DecidablePred (IsLinearChordDiagram n) := fun σ => by
  unfold IsLinearChordDiagram; infer_instance

/-- **Endpoints of short chords.** Let $\sigma$ be a map from $\{0, \dots, 2n-1\}$ to itself (for a
linear chord diagram, vertex $i$ is joined by a chord to $\sigma(i)$). A vertex $i$ is an
endpoint of a short chord of $\sigma$ when $\sigma(i) = i - 1$ or $\sigma(i) = i + 1$, that is,
when $i$ is joined to an adjacent vertex.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Abstract and Section 1 (short chords). -/
def IsShortChordVertex {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) (i : Fin (2 * n)) : Prop :=
  (σ i : ℕ) + 1 = i ∨ (i : ℕ) + 1 = σ i

instance {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) : DecidablePred (IsShortChordVertex σ) :=
  fun i => by unfold IsShortChordVertex; infer_instance

/-- **Bubbles.** Let $\sigma$ be a map from $\{0, \dots, 2n-1\}$ to itself (for a linear chord
diagram, vertex $i$ is joined by a chord to $\sigma(i)$). For natural numbers $a$ and $p$, the
vertices $a, a+1, \dots, a+p-1$ form a bubble of size $p$ in $\sigma$ when $p \ge 1$,
$a + p \le 2n$, none of these vertices is an endpoint of a short chord of $\sigma$, the vertex
$a - 1$ is an endpoint of a short chord unless $a = 0$, and the vertex $a + p$ is an endpoint
of a short chord unless $a + p = 2n$.

So a bubble is a maximal run of consecutive vertices containing no endpoint of a short chord.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Section 1 (definition of bubbles and their size). -/
def IsBubble {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) (a p : ℕ) : Prop :=
  0 < p ∧ a + p ≤ 2 * n ∧
    (∀ i : Fin (2 * n), a ≤ (i : ℕ) → (i : ℕ) < a + p → ¬ IsShortChordVertex σ i) ∧
    (∀ i : Fin (2 * n), (i : ℕ) + 1 = a → IsShortChordVertex σ i) ∧
    (∀ i : Fin (2 * n), (i : ℕ) = a + p → IsShortChordVertex σ i)

instance {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) (p : ℕ) :
    DecidablePred (fun a => IsBubble σ a p) := fun a => by
  unfold IsBubble; infer_instance

/-- **Bubble counts.** For natural numbers $n$ and $p$, $B_{n,p}$ is the total number of bubbles of
size $p$ in all linear chord diagrams on $2n$ vertices: the sum, over all linear chord diagrams
$\sigma$ on the vertices $0, \dots, 2n-1$, of the number of vertices $a$ such that the vertices
$a, a+1, \dots, a+p-1$ form a bubble of size $p$ in $\sigma$. In particular $B_{n,0} = 0$.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Section 1 (definition of `B_{n,p}`, Table 1). -/
def bubbleCount (n p : ℕ) : ℕ :=
  ∑ σ ∈ Finset.univ.filter (IsLinearChordDiagram n),
    ((Finset.range (2 * n)).filter (fun a => IsBubble σ a p)).card

/-- **No bubbles of size one on two vertices.** $B_{1,1} = 0$: the linear chord diagrams on $2$
vertices have no bubble of size $1$. The only such diagram is a single short chord.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Table 1 (row `n = 1`). -/
theorem bubbleCount_one_one : bubbleCount 1 1 = 0 := by decide +kernel

/-- **Bubbles of size one on four vertices.** $B_{2,1} = 2$: the linear chord diagrams on $4$
vertices have $2$ bubbles of size $1$ in total.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Table 1 (row `n = 2`). -/
theorem bubbleCount_two_one : bubbleCount 2 1 = 2 := by decide +kernel

/-- **Bubbles of size four on four vertices.** $B_{2,4} = 1$: the linear chord diagrams on $4$
vertices have exactly one bubble of size $4$ in total. It consists of all four vertices of the
crossing diagram (chords $\{0, 2\}$ and $\{1, 3\}$), which has no short chord.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Table 1 (row `n = 2`). -/
theorem bubbleCount_two_four : bubbleCount 2 4 = 1 := by decide +kernel

/-- **Total number of bubbles in linear chord diagrams.** For every natural number $n \ge 2$,
let $B_{n,p}$ be the total number of bubbles of size $p$ over all linear chord diagrams on $2n$
vertices. Then
$$\sum_{p=1}^{2n} B_{n,p} = \frac{(2n-2)!\,(4n-5)}{2^{n-1}\,(n-1)!}.$$

The hypothesis $n \ge 2$ is needed: for $n = 1$ the left side is $0$ and the right side is $-1$.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Lemma 3 (`jis-2024-24.4.2-lem-3`). -/
public theorem_wanted sum_bubbleCount (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ Finset.Icc 1 (2 * n), (bubbleCount n p : ℚ)) =
      (2 * n - 2).factorial * (4 * n - 5 : ℚ) / (2 ^ (n - 1) * (n - 1).factorial)

/-- **First moment of bubble sizes in linear chord diagrams.** For every natural number
$n \ge 2$, let $B_{n,p}$ be the total number of bubbles of size $p$ over all linear chord diagrams
on $2n$ vertices. Then
$$\sum_{p=1}^{2n} p\,B_{n,p} = \frac{(2n-1)!}{2^{n-2}\,(n-2)!}.$$

The hypothesis $n \ge 2$ is added because the right side involves $(n-2)!$.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Lemma 4 (`jis-2024-24.4.2-lem-4`). -/
public theorem_wanted sum_mul_bubbleCount (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ Finset.Icc 1 (2 * n), (p : ℚ) * bubbleCount n p) =
      (2 * n - 1).factorial / (2 ^ (n - 2) * (n - 2).factorial)

/-- **Mean bubble size.** Let $B_{n,p}$ be the total number of bubbles of size $p$ in all linear
chord diagrams on $2n$ vertices. For every integer $n \ge 2$, the mean bubble size satisfies
$$\frac{\sum_{p=1}^{2n} p\,B_{n,p}}{\sum_{p=1}^{2n} B_{n,p}} = \frac{2(2n-1)(n-1)}{4n-5}.$$

The hypothesis $n \ge 2$ is added: for $n = 1$ there are no bubbles.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Theorem 5 (`jis-2024-24.4.2-thm-5`). -/
public theorem_wanted mean_bubble_size (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ Finset.Icc 1 (2 * n), (p : ℚ) * bubbleCount n p) /
        (∑ p ∈ Finset.Icc 1 (2 * n), (bubbleCount n p : ℚ)) =
      2 * (2 * n - 1) * (n - 1) / (4 * n - 5)

/-- **Formal contour-integral formula for bubble counts.** Let $G(s, w, y)$ be the power series
in $\mathbb{Q}[[s, w, y]]$ given by
$$G = \left(1 - \frac{y^2}{1 - sy + y^2}\right)^{-2} \left(\frac{1}{1 - wsy + w^2y^2} - 1\right),$$
and write $[s^a w^p y^m]\,G$ for its coefficient of $s^a w^p y^m$. For integers $n, p \ge 0$ let
$B_{n,p}$ be the total number of bubbles of size $p$ in all linear chord diagrams on $2n$
vertices. Then for all integers $n, p \ge 0$ (including $n = 0$)
$$\sum_{k \ge 0} \frac{(2k)!}{2^k\, k!}\, [s^{2k} w^p y^{2n}]\,G = B_{n,p} \quad\text{and}\quad
\sum_{k \ge 0} \frac{(2k)!}{2^k\, k!}\, [s^{2k} w^p y^{2n+1}]\,G = 0.$$

Each sum has only finitely many nonzero terms, since every power of $s$ in $G$ comes with at
least the same power of $y$. This is the termwise reading of the paper's formal contour
integral: integrating $x^{-1} e^{x^2/2} G(t/x, w, y)$ over $x$ and then replacing $t^{2k}$ by
$\int_0^\infty t^{2k} e^{-t}\,dt = (2k)!$ turns $s^{2k}$ into $(2k)!/(2^k k!)$. The literal
integrals diverge.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Theorem 1 (`jis-2024-24.4.2-thm-1`). -/
public theorem_wanted bubbleCount_formal_contour_integral :
    let s : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 0
    let w : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 1
    let y : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 2
    let G : MvPowerSeries (Fin 3) ℚ :=
      ((1 - y ^ 2 * (1 - s * y + y ^ 2)⁻¹) ^ 2)⁻¹ * ((1 - w * s * y + w ^ 2 * y ^ 2)⁻¹ - 1)
    (∀ n p : ℕ, (∑ᶠ k : ℕ, ((2 * k).factorial / (2 ^ k * k.factorial) : ℚ) *
        MvPowerSeries.coeff (Finsupp.single 0 (2 * k) + Finsupp.single 1 p +
          Finsupp.single 2 (2 * n)) G) = bubbleCount n p) ∧
    ∀ n p : ℕ, (∑ᶠ k : ℕ, ((2 * k).factorial / (2 ^ k * k.factorial) : ℚ) *
        MvPowerSeries.coeff (Finsupp.single 0 (2 * k) + Finsupp.single 1 p +
          Finsupp.single 2 (2 * n + 1)) G) = 0

/-- **Closed form of the bubble generating function.** In $\mathbb{Q}[[t, w, y]]$ let
$D = 1 - w(1 - wy)$ and let $I(t, w, y)$ be the power series
$$I = \frac{(1-w)^2 (1-wy)^2}{(1+w^2y)\,D^2}
\exp\!\left(\frac{y}{2}\left(\frac{tw}{1+w^2y}\right)^2\right) +
\left(\frac{(2 - w(y+2)(1 + y(1 - w(2-wy))))\,wy}{D^2} + \frac{(1-wy)\,t^2 w y^3}{D}\right)
\exp\!\left(\frac{t^2 y}{2}\right),$$
and write $[t^m w^p y^n]\,I$ for its coefficient of $t^m w^p y^n$. For integers $n, p \ge 0$ let
$B_{n,p}$ be the total number of bubbles of size $p$ in all linear chord diagrams on $2n$
vertices. Then for all integers $n \ge 1$ and $p \ge 0$
$$\sum_{m \ge 0} m!\, [t^m w^p y^n]\,I = B_{n,p}.$$

The sum has only finitely many nonzero terms, since $t$ occurs in $I$ only as $t^2$ times a
factor $y$. Replacing $t^m$ by $m! = \int_0^\infty t^m e^{-t}\,dt$ reads the formula as a formal
Laplace transform in $t$, as in the paper's proofs of Lemmas 3 and 4, so that the left side is
the coefficient of $y^n w^p$ of the paper's $B(y, w) = \sum_{n,p} B_{n,p} y^n w^p$. The case
$n = 0$ is excluded: the printed formula has constant term $1$ while $B_{0,0} = 0$ (the paper's
residue computation in its contour variable $x$ omits the residue $-1$ at $x = 0$; Theorem 1
gives constant term $0$).

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Corollary 2 (`jis-2024-24.4.2-cor-2`). -/
public theorem_wanted bubbleCount_formal_laplace_closed_form :
    let t : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 0
    let w : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 1
    let y : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 2
    let D : MvPowerSeries (Fin 3) ℚ := 1 - w * (1 - w * y)
    let integrand : MvPowerSeries (Fin 3) ℚ :=
      (1 - w) ^ 2 * (1 - w * y) ^ 2 * ((1 + w ^ 2 * y) * D ^ 2)⁻¹ *
          PowerSeries.subst ((2⁻¹ : ℚ) • (y * (t * w * (1 + w ^ 2 * y)⁻¹) ^ 2)) (PowerSeries.exp ℚ) +
        ((2 - w * (y + 2) * (1 + y * (1 - w * (2 - w * y)))) * (D ^ 2)⁻¹ * (w * y) +
            (1 - w * y) * D⁻¹ * (t ^ 2 * w * y ^ 3)) *
          PowerSeries.subst ((2⁻¹ : ℚ) • (t ^ 2 * y)) (PowerSeries.exp ℚ)
    ∀ n p : ℕ, 1 ≤ n →
      (∑ᶠ m : ℕ, (m.factorial : ℚ) *
        MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 p + Finsupp.single 2 n)
          integrand) = bubbleCount n p

/-- **Limiting density of bubble sizes in linear chord diagrams.** Let $B_{n,p}$ be the total
number of bubbles of size $p$ over all linear chord diagrams on $2n$ vertices. Let $x$ be a real
number with $0 < x \le 2$, and let $(p_n)_{n \ge 0}$ be natural numbers with $p_0 = 0$,
$p_n \le 2n - 2$ for every $n \ge 1$, and $p_n / (n - 1) \to x$ as $n \to \infty$. Then
$$\frac{(n-1)\,B_{n,p_n}}{\sum_{p=1}^{2n-2} B_{n,p}} \to \frac{e\,(6-x)}{2\,(4e-2)}\,e^{-x/2}$$
as $n \to \infty$. The sum in the denominator leaves out the bubble sizes $2n - 1$ and $2n$; a
bubble of size $2n$ is a whole diagram without short chords.

The paper writes $B_{n,x(n-1)}$; since $x(n-1)$ need not be an integer, the limit is read along
integer sizes $p_n$ with $p_n/(n-1) \to x$, the scaling the paper's proof uses.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Theorem 6 (`jis-2024-24.4.2-thm-6`). -/
public theorem_wanted tendsto_bubbleCount_density (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 2)
    (p : ℕ → ℕ) (hp : ∀ n, p n ≤ 2 * n - 2)
    (hpx : Filter.Tendsto (fun n : ℕ => (p n : ℝ) / ((n : ℝ) - 1)) Filter.atTop (nhds x)) :
    Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) - 1) * bubbleCount n (p n) /
        ∑ q ∈ Finset.Icc 1 (2 * n - 2), (bubbleCount n q : ℝ))
      Filter.atTop
      (nhds (Real.exp 1 * (6 - x) / (2 * (4 * Real.exp 1 - 2)) * Real.exp (-x / 2)))

end

end MetaMathlibExt
