/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Basic

/-!
Statements from Evans and Hendel on recursions of the rows of the circuit array: Section 3
(annihilators). A polynomial `p = ∑ aᵢ Xⁱ` acts on a sequence `G : ℕ → K` through the translation
operator `E(G_s) = G_{s+1}` as `(p(E) G)_s = ∑ aᵢ G_{s+i}`.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Annihilator of a sequence.** Let $K$ be a semiring, $p = \sum_i a_i X^i \in K[X]$ and
$G \colon \mathbb{N} \to K$ a sequence, and let $E$ be the translation operator
$E(G_s) = G_{s+1}$. The operator $p(E)$ annihilates $G$ when $\sum_i a_i G_{s+i} = 0$ for every
$s \ge 0$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 3 (definitions of the translation operator and of an annihilator). -/
def AnnihilatesSeq {K : Type*} [Semiring K] (p : K[X]) (G : ℕ → K) : Prop :=
  ∀ s : ℕ, p.sum (fun i a => a * G (s + i)) = 0

/-- **Every operator annihilates the zero sequence.** For every semiring $K$ and every polynomial
$p \in K[X]$, the operator $p(E)$ annihilates the zero sequence, where $E$ is the translation
operator $E(G_s) = G_{s+1}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 3 (definition of an annihilator). -/
theorem annihilatesSeq_zero {K : Type*} [Semiring K] (p : K[X]) : AnnihilatesSeq p (0 : ℕ → K) := by
  intro s
  simp [Polynomial.sum]

/-- **The characteristic polynomial annihilates the solutions of its recurrence.** Let $K$ be a
field, $d \ge 0$ and $a_0, \dots, a_{d-1} \in K$. If a sequence $G \colon \mathbb{N} \to K$
satisfies $G_{n+d} = \sum_{i=0}^{d-1} a_i G_{n+i}$ for every $n \ge 0$, then the characteristic
polynomial $X^d - \sum_{i=0}^{d-1} a_i X^i$ of this recurrence annihilates $G$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.4 (`fq-2024-hendel08232024rev2-lem-3.4`). -/
public theorem_wanted annihilatesSeq_charPoly_of_isSolution {K : Type*} [Field K]
    (E : LinearRecurrence K) (G : ℕ → K) (hG : E.IsSolution G) :
    AnnihilatesSeq E.charPoly G

/-- **The operator $E - c$ annihilates the powers of $c$.** Let $K$ be a field, $c \in K$, and let
$E$ be the translation operator $E(G_s) = G_{s+1}$ on sequences $G \colon \mathbb{N} \to K$. Then
the operator $E - c$, that is, $p(E)$ for the polynomial $p = X - c \in K[X]$, annihilates the
sequence $s \mapsto c^s$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.7 (`fq-2024-hendel08232024rev2-lem-3.7`), part (i). -/
public theorem_wanted annihilatesSeq_X_sub_C_pow {K : Type*} [Field K] (c : K) :
    AnnihilatesSeq (X - C c) (fun s => c ^ s)

/-- **The Addition-Multiplication Lemma for annihilators.** Let $E$ be the translation operator
$E(G_s) = G_{s+1}$ on sequences. (i) Let $K$ be a field, $I$ a finite index set, and for each
$i \in I$ let $A_i \in K[X]$, $G_i \colon \mathbb{N} \to K$ and $c_i \in K$. If $A_i(E)$
annihilates $G_i$ for every $i \in I$, then $\prod_{i \in I} A_i(E)$ annihilates the sequence
$s \mapsto \sum_{i \in I} c_i G_i(s)$. (ii) Let $p_1, p_2 \in \mathbb{C}[X]$ be nonzero
polynomials and $G_1, G_2 \colon \mathbb{N} \to \mathbb{C}$ sequences such that $p_1(E)$
annihilates $G_1$ and $p_2(E)$ annihilates $G_2$. If $r_{1,1}, \dots, r_{1,m}$ and
$r_{2,1}, \dots, r_{2,n}$ are the complex roots of $p_1$ and $p_2$, listed with multiplicity,
then $\prod_{j=1}^{m} \prod_{j'=1}^{n} (E - r_{1,j} r_{2,j'})$ annihilates the termwise product
$s \mapsto G_1(s) G_2(s)$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.8 (`fq-2024-hendel08232024rev2-lem-3.8`); part (ii) quoted from Jarden. -/
public theorem_wanted annihilatesSeq_sum_prod_and_mul :
    (∀ {K : Type*} [Field K] {ι : Type*} (I : Finset ι) (A : ι → K[X]) (G : ι → ℕ → K)
        (c : ι → K), (∀ i ∈ I, AnnihilatesSeq (A i) (G i)) →
        AnnihilatesSeq (∏ i ∈ I, A i) (fun s => ∑ i ∈ I, c i * G i s)) ∧
      ∀ (p₁ p₂ : ℂ[X]) (G₁ G₂ : ℕ → ℂ), p₁ ≠ 0 → p₂ ≠ 0 →
        AnnihilatesSeq p₁ G₁ → AnnihilatesSeq p₂ G₂ →
        AnnihilatesSeq ((p₁.roots ×ˢ p₂.roots).map (fun r => X - C (r.1 * r.2))).prod
          (fun s => G₁ s * G₂ s)

/-! ### Section 2: the circuit array

The circuit array is read off a triangular grid of resistances that is reduced one row at a time
(Steps 1-5 of Section 2: a `Δ`-`Y` transformation on every upright triangle, series on the boundary,
`Y`-`Δ` on the remaining out-stars). A labelling of a grid is a function `T r d e`, the resistance of
edge `e` of the upright triangle in row `r` (from the top) and diagonal `d` (from the left), with
`1 ≤ d ≤ r`. The grid here has no bottom row: the paper reads the circuit array off an all-one
`n`-grid with `n ≥ 4j - 2`, whose bottom edges never reach the entries in column `j`. Values at
indices outside `1 ≤ d ≤ r` are junk. -/

/-- **Edges of an upright triangle.** An upright triangle of the grid has three edges: the left
edge $L$, the right edge $R$ and the base $B$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 2 (edge labels `L`, `R`, `B`). -/
inductive CircuitEdge
  | left
  | right
  | base

/-- **Delta-wye resistance function.** For elements $x$, $y$, $z$ of a field $K$, the delta-wye
resistance function is $\Delta(x, y, z) = \frac{xy}{x + y + z}$.

Division follows the convention $a / 0 = 0$, so $\Delta(x, y, z) = 0$ when $x + y + z = 0$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.1). -/
def circuitDelta {K : Type*} [Field K] (x y z : K) : K :=
  x * y / (x + y + z)

/-- **The Y-Δ resistance function.** For elements $a$, $b$, $c$ of a field $K$, the $Y$-$\Delta$
resistance function is $Y(a, b, c) = (ab + bc + ca)/a$.

When $a = 0$ the value is $0$, by the convention $x/0 = 0$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.1). -/
def circuitY {K : Type*} [Field K] (a b c : K) : K :=
  (a * b + b * c + c * a) / a

/-- **Top delta-wye arm.** For an upright triangle whose left, right and base edges carry the
values $L$, $R$, $B$ in a field $K$, the top arm is $\Delta(L, R, B) = \frac{LR}{L + R + B}$, where
$\Delta$ is the delta-wye resistance function: the arm of the equivalent star from the centre of
the triangle to its top vertex.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Figure 2 (`Y₁₂ = Δ(L, R, B)`). -/
def circuitTopArm {K : Type*} [Field K] (t : CircuitEdge → K) : K :=
  circuitDelta (t .left) (t .right) (t .base)

/-- **Bottom-right delta-wye arm.** For an upright triangle whose left, right and base edges carry
the values $L$, $R$, $B$ in a field $K$, the bottom-right arm is
$\Delta(R, B, L) = \frac{RB}{R + B + L}$, where $\Delta$ is the delta-wye resistance function: the
arm of the equivalent star from the centre of the triangle to its bottom-right vertex.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Figure 2 (`Y₄ = Δ(R, B, L)`). -/
def circuitRightArm {K : Type*} [Field K] (t : CircuitEdge → K) : K :=
  circuitDelta (t .right) (t .base) (t .left)

/-- **Bottom-left delta-wye arm.** For an upright triangle whose left, right and base edges carry
the values $L$, $R$, $B$ in a field $K$, the bottom-left arm is
$\Delta(B, L, R) = \frac{BL}{B + L + R}$, where $\Delta$ is the delta-wye resistance function: the
arm of the equivalent star from the centre of the triangle to its bottom-left vertex.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Figure 2 (`Y₈ = Δ(B, L, R)`). -/
def circuitLeftArm {K : Type*} [Field K] (t : CircuitEdge → K) : K :=
  circuitDelta (t .base) (t .left) (t .right)

/-- **Left-perimeter function.** Let $K$ be a field, let $\Delta(x, y, z) = xy/(x + y + z)$ be the
delta-wye resistance function, and for an upright triangle $t$ write $L_t$, $R_t$, $B_t \in K$ for
the values on its left, right and base edges. For triangles $t$ and $u$, the left-perimeter
function is $\mathcal{P}(t, u) = \Delta(B_t, L_t, R_t) + \Delta(L_u, R_u, B_u)$, the series
resistance of the bottom-left arm of $t$ and the top arm of $u$.

In the row reduction of a labelling $T$ it is applied to $t = T_{r,1}$ and $u = T_{r+1,1}$, where
$T_{r,d}$ is the triangle in row $r$ and diagonal $d$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.2). -/
def circuitPerimeter {K : Type*} [Field K] (t u : CircuitEdge → K) : K :=
  circuitLeftArm t + circuitTopArm u

/-- **Left-edge function.** Let $K$ be a field, let $\Delta(x, y, z) = xy/(x + y + z)$ and
$Y(a, b, c) = (ab + bc + ca)/a$ be the delta-wye and wye-delta resistance functions, and for an
upright triangle $t$ write $L_t$, $R_t$, $B_t \in K$ for the values on its left, right and base
edges. For triangles $t$, $u$, $v$, the left-edge function is
$\mathcal{L}(t, u, v) = Y(\Delta(R_t, B_t, L_t), \Delta(B_u, L_u, R_u), \Delta(L_v, R_v, B_v))$,
the wye-delta transform of the star formed by the bottom-right arm of $t$, the bottom-left arm of
$u$ and the top arm of $v$, with the arm of $t$ first.

In the row reduction of a labelling $T$ it is applied to $t = T_{r,d-1}$, $u = T_{r,d}$ and
$v = T_{r+1,d}$ for $d \ne 1$, where $T_{r,d}$ is the triangle in row $r$ and diagonal $d$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.5). -/
def circuitLeftEdge {K : Type*} [Field K] (t u v : CircuitEdge → K) : K :=
  circuitY (circuitRightArm t) (circuitLeftArm u) (circuitTopArm v)

/-- **Right-edge function.** Let $K$ be a field, let $\Delta(x, y, z) = xy/(x + y + z)$ and
$Y(a, b, c) = (ab + bc + ca)/a$ be the delta-wye and wye-delta resistance functions, and for an
upright triangle $t$ write $L_t$, $R_t$, $B_t \in K$ for the values on its left, right and base
edges. For triangles $t$, $u$, $v$, the right-edge function is
$\mathcal{R}(t, u, v) = Y(\Delta(B_u, L_u, R_u), \Delta(R_t, B_t, L_t), \Delta(L_v, R_v, B_v))$,
the wye-delta transform of the star formed by the bottom-left arm of $u$, the bottom-right arm of
$t$ and the top arm of $v$, with the arm of $u$ first.

In the row reduction of a labelling $T$ it is applied to $t = T_{r,d}$, $u = T_{r,d+1}$ and
$v = T_{r+1,d+1}$ for $d \ne r$, where $T_{r,d}$ is the triangle in row $r$ and diagonal $d$. This
follows Steps 2-5 and Figure 2; the displayed equation (2.4) instead uses $T_{r+1,d}$ in place of
$T_{r+1,d+1}$ and puts the arm of $t$ first, which gives $C_{1,2} = 29/36$ against Table 1's
$13/12$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.4) (corrected as above). -/
def circuitRightEdge {K : Type*} [Field K] (t u v : CircuitEdge → K) : K :=
  circuitY (circuitLeftArm u) (circuitRightArm t) (circuitTopArm v)

/-- **Base-edge function.** Let $K$ be a field. For a triangle with left, right and base
resistances $L$, $R$, $B$ in $K$, its top arm is $\Delta(L, R, B)$, its bottom-right arm is
$\Delta(R, B, L)$ and its bottom-left arm is $\Delta(B, L, R)$, where
$\Delta(x, y, z) = xy/(x + y + z)$. For triangles $t$, $u$, $v$, the base-edge function is
$\mathcal{B}(t, u, v) = Y(a, b, c) = (ab + bc + ca)/a$, where $a$ is the top arm of $t$, $b$ is
the bottom-right arm of $u$ and $c$ is the bottom-left arm of $v$. In a row reduction, for a row
$r$ and a diagonal $d$, the triangles $t$, $u$, $v$ are those in row $r + 2$ and diagonal $d + 1$,
in row $r + 1$ and diagonal $d$, and in row $r + 1$ and diagonal $d + 1$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.3). -/
def circuitBaseEdge {K : Type*} [Field K] (t u v : CircuitEdge → K) : K :=
  circuitY (circuitTopArm t) (circuitRightArm u) (circuitLeftArm v)

/-- **Row reduction of a labelled triangular grid.** Let $K$ be a field and let $T$ be a labelling
that assigns a value $T_{r,d,e} \in K$ to the edge $e$ (left $L$, right $R$ or base $B$) of the
upright triangle in row $r$ (from the top) and diagonal $d$ (from the left); write $T_{r,d}$ for
that triangle and $\Delta(x, y, z) = xy/(x + y + z)$ for the delta-wye resistance function. The
reduced labelling $T'$ is given by $T'_{r,1,L} = \mathcal{P}(T_{r,1}, T_{r+1,1})$ and
$T'_{r,d,L} = \mathcal{L}(T_{r,d-1}, T_{r,d}, T_{r+1,d})$ for $d \ne 1$, where $\mathcal{P}$ is the
left-perimeter function and $\mathcal{L}$ the left-edge function; by $T'_{r,r,R}$ equal to the
bottom-right arm $\Delta(R, B, L)$ of $T_{r,r}$ plus the top arm $\Delta(L, R, B)$ of
$T_{r+1,r+1}$, and $T'_{r,d,R} = \mathcal{R}(T_{r,d}, T_{r,d+1}, T_{r+1,d+1})$ for $d \ne r$, where
$\mathcal{R}$ is the right-edge function; and by
$T'_{r,d,B} = \mathcal{B}(T_{r+2,d+1}, T_{r+1,d}, T_{r+1,d+1})$, where $\mathcal{B}$ is the
base-edge function.

Here $r$ and $d$ range over all natural numbers, with $d - 1$ truncated at $0$; only the values
with $1 \le d \le r$ are meaningful.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 2 (row reduction, equations (2.2)-(2.5)). -/
def circuitReduce {K : Type*} [Field K] (T : ℕ → ℕ → CircuitEdge → K) :
    ℕ → ℕ → CircuitEdge → K
  | r, d, .left =>
      if d = 1 then circuitPerimeter (T r 1) (T (r + 1) 1)
      else circuitLeftEdge (T r (d - 1)) (T r d) (T (r + 1) d)
  | r, d, .right =>
      if d = r then circuitRightArm (T r r) + circuitTopArm (T (r + 1) (r + 1))
      else circuitRightEdge (T r d) (T r (d + 1)) (T (r + 1) (d + 1))
  | r, d, .base => circuitBaseEdge (T (r + 2) (d + 1)) (T (r + 1) d) (T (r + 1) (d + 1))

/-- **Reduced circuit grids.** Let $K$ be a field, and for each $m$ let either a boundary value
$\beta_m \in K$ be given or none. The labellings $T^m$, which assign a value $T^m_{r,d,e} \in K$ to
the edge $e$ (left $L$, right $R$ or base $B$) of the upright triangle in row $r$ and diagonal $d$,
are defined by recursion on $m$: $T^0$ is identically $1$, and $T^{m+1}$ is the row reduction of
$T^m$, except that if $\beta_{m+1}$ is given then every left edge with $d = 1$ and every right edge
with $d = r$ takes the value $\beta_{m+1}$.

With no boundary values given this is the numerical reduction of the all-one grid; in
Definitions 2.4 and 2.5 the boundary values are variables.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 2 (reductions `T^m`, Definitions 2.4 and 2.5). -/
def circuitGrid {K : Type*} [Field K] (bdry : ℕ → Option K) : ℕ → ℕ → ℕ → CircuitEdge → K
  | 0 => fun _ _ _ => 1
  | m + 1 => fun r d e =>
      match e with
      | .left =>
          if d = 1 then (bdry (m + 1)).getD (circuitReduce (circuitGrid bdry m) r d .left)
          else circuitReduce (circuitGrid bdry m) r d .left
      | .right =>
          if d = r then (bdry (m + 1)).getD (circuitReduce (circuitGrid bdry m) r d .right)
          else circuitReduce (circuitGrid bdry m) r d .right
      | .base => circuitReduce (circuitGrid bdry m) r d .base

/-- **Circuit array of a boundary assignment.** Let $K$ be a field and let $\beta$ assign to each
natural number $m$ either nothing or a value $\beta(m) \in K$. Let $T^0$ be the all-one triangular
grid and, for $m \ge 1$, let $T^m$ be obtained from $T^{m-1}$ by one row reduction followed, when
$\beta(m)$ is given, by setting every boundary edge (left edges on diagonal $1$, right edges on
diagonal $r$ in row $r$) to $\beta(m)$. For natural numbers $i$ and $j$, the entry $C_{i,j}$ of the
circuit array of $\beta$ is the resistance of the left edge (for even $i$) or the right edge (for
odd $i$) of the triangle of $T^j$ in row $2j - 1$ and diagonal $j - \lfloor (i+1)/2 \rfloor$, with
subtraction truncated at $0$. The entries are meaningful for $j \ge 1$ and $0 \le i \le 2(j - 1)$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.3. -/
def circuitArrayOf {K : Type*} [Field K] (bdry : ℕ → Option K) (i j : ℕ) : K :=
  circuitGrid bdry j (2 * j - 1) (j - (i + 1) / 2) (if Even i then .left else .right)

/-- **Circuit array.** The circuit array $C_{i,j} \in \mathbb{Q}$ is the circuit array of the
reductions of the all-one triangular grid with no boundary edge replaced: $C_{i,j}$ is the left
edge (for even $i$) or the right edge (for odd $i$) of the triangle in row $2j - 1$ and diagonal
$j - \lfloor (i+1)/2 \rfloor$ of the all-one grid reduced $j$ times, with subtraction truncated
at $0$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.3 and Table 1. -/
def circuitArray (i j : ℕ) : ℚ :=
  circuitArrayOf (fun _ => none) i j

/-- **One-variable circuit array.** The one-variable circuit array $C^X_{i,j}$, with entries in
the field $\mathbb{Q}(X)$ of rational functions in one variable over $\mathbb{Q}$, is the circuit
array of the reductions of the all-one triangular grid in which, after the first reduction, every
boundary edge is set to $(X - 3)/X$, and no boundary edge is replaced after any later reduction.
Thus $C^X_{i,j}$ is the left edge (for even $i$) or the right edge (for odd $i$) of the triangle
in row $2j - 1$ and diagonal $j - \lfloor (i+1)/2 \rfloor$ of this grid reduced $j$ times, with
subtraction truncated at $0$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.4 and Table 2. -/
noncomputable def circuitArrayX (i j : ℕ) : RatFunc ℚ :=
  circuitArrayOf (fun m => if m = 1 then some ((RatFunc.X - 3) / RatFunc.X) else none) i j

/-- **Variables of the multivariable circuit array.** For a natural number $m$, $X_m$ is the
indeterminate $X_m$ regarded as an element of the field of fractions
$\mathbb{Q}(X_0, X_1, X_2, \dots)$ of the polynomial ring $\mathbb{Q}[X_0, X_1, X_2, \dots]$ in
countably many variables.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5 (the variables `X_i`). -/
noncomputable def circuitVar (m : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  algebraMap (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ)) (MvPolynomial.X m)

/-- **Multivariable circuit array.** Reduce the all-one triangular grid row by row as in Section 2,
and after the $m$-th reduction, for every $m \ge 1$, set every boundary edge (the left edges on the
first diagonal and the right edges on the last diagonal) to the variable $X_m$ of the field of
rational functions over $\mathbb{Q}$ in $X_0, X_1, \dots$. The multivariable circuit array
$C^M_{i,j}$ (Table 3) is the circuit array read off these grids: for $j \ge 1$ and
$0 \le i \le 2(j-1)$, it is the left edge for even $i$, or the right edge for odd $i$, of the
triangle in row $2j - 1$ and diagonal $j - \lfloor (i+1)/2 \rfloor$ of the $j$-times reduced
grid (other indices give junk values). In particular $C^M_{2(m-1),m} = X_m$ for every $m \ge 1$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5 and Table 3. -/
noncomputable def circuitArrayM (i j : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  circuitArrayOf (fun m => if m = 0 then none else some (circuitVar m)) i j

/-- **First entries of the circuit array.** The circuit array satisfies $C_{0,1} = 2/3$,
$C_{0,2} = 26/27$, $C_{1,2} = 13/12$ and $C_{2,2} = 1/2$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Table 1. -/
theorem circuitArray_small :
    circuitArray 0 1 = 2 / 3 ∧ circuitArray 0 2 = 26 / 27 ∧ circuitArray 1 2 = 13 / 12 ∧
      circuitArray 2 2 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [circuitArray, circuitArrayOf, circuitGrid, circuitReduce, circuitPerimeter,
      circuitLeftEdge, circuitRightEdge, circuitBaseEdge, circuitTopArm, circuitRightArm,
      circuitLeftArm, circuitDelta, circuitY]

/-- **First entry of the one-variable circuit array.** The one-variable circuit array $C^X$, with
entries in the field $\mathbb{Q}(X)$ of rational functions over $\mathbb{Q}$, satisfies
$C^X_{0,1} = (X - 3)/X$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.4 and Proposition 4.1 (iv). -/
theorem circuitArrayX_zero_one : circuitArrayX 0 1 = (RatFunc.X - 3) / RatFunc.X := by
  simp [circuitArrayX, circuitArrayOf, circuitGrid]

/-- **First entries of the left diagonal of the multivariable circuit array.** The multivariable
circuit array $C^M$, with values in the field of rational functions over $\mathbb{Q}$ in the
variables $X_0, X_1, \dots$, satisfies $C^M_{0,1} = X_1$ and $C^M_{2,2} = X_2$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5. -/
theorem circuitArrayM_diagonal :
    circuitArrayM 0 1 = circuitVar 1 ∧ circuitArrayM 2 2 = circuitVar 2 := by
  constructor <;> simp [circuitArrayM, circuitArrayOf, circuitGrid]

/-! ### Section 4 -/

/-- **Column recursion for the one-variable circuit array.** Extend the one-variable circuit array
$C^X$, with entries in the field $\mathbb{Q}(X)$ of rational functions over $\mathbb{Q}$, to integer
row indices by $C_{i,j} = C^X_{i,j}$ for $i \ge 0$ and $C_{i,j} = 1$ for $i < 0$. For an integer
$i$ and a natural number $j$, let $\tau_{i,j}$ be the triangle with left edge $C_{i,j}$ and right
and base edges $C_{i-1,j}$. Let $\mathcal{P}$, $\mathcal{L}$ and $\mathcal{R}$ be the
left-perimeter, left-edge and right-edge functions of the reduction. Then:
(i) $C_{2(c-1),c} = \mathcal{P}(\tau_{2(c-2),c-1}, \tau_{2(c-2),c-1})$ for every natural number
$c \ge 2$;
(ii) $C_{2(c-1),j} = \mathcal{L}(\tau_{2(c-1),j-1}, \tau_{2c-4,j-1}, \tau_{2c-4,j-1})$ for all
natural numbers $c$, $j$ with $2 \le c < j$;
(iii) $C_{2c-3,j} = \mathcal{R}(\tau_{2c-4,j-1}, \tau_{2c-6,j-1}, \tau_{2c-6,j-1})$ for all
natural numbers $c$, $j$ with $2 \le c \le j$;
(iv) $C^X_{0,1} = (X - 3)/X$.

Here $\mathcal{R}$ is the right-edge function of the reduction algorithm, not the misprinted
display (2.4), and the printed $C_{2(c-1-4),j-1}$ in (iii) is read as $C_{2(c-1)-4,j-1}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Proposition 4.1 (`fq-2024-hendel08232024rev2-prop-4.1`). -/
public theorem_wanted circuitArrayX_inductive :
    let C : ℤ → ℕ → RatFunc ℚ := fun i j => if i < 0 then 1 else circuitArrayX i.toNat j
    let tri : ℤ → ℕ → CircuitEdge → RatFunc ℚ := fun i j e =>
      match e with
      | .left => C i j
      | .right => C (i - 1) j
      | .base => C (i - 1) j
    (∀ c : ℕ, 2 ≤ c →
        C (2 * ((c : ℤ) - 1)) c = circuitPerimeter (tri (2 * ((c : ℤ) - 2)) (c - 1))
          (tri (2 * ((c : ℤ) - 2)) (c - 1))) ∧
      (∀ c j : ℕ, 2 ≤ c → c < j →
        C (2 * ((c : ℤ) - 1)) j = circuitLeftEdge (tri (2 * ((c : ℤ) - 1)) (j - 1))
          (tri (2 * ((c : ℤ) - 1) - 2) (j - 1)) (tri (2 * ((c : ℤ) - 1) - 2) (j - 1))) ∧
      (∀ c j : ℕ, 2 ≤ c → c ≤ j →
        C (2 * ((c : ℤ) - 1) - 1) j = circuitRightEdge (tri (2 * ((c : ℤ) - 1) - 2) (j - 1))
          (tri (2 * ((c : ℤ) - 1) - 4) (j - 1)) (tri (2 * ((c : ℤ) - 1) - 4) (j - 1))) ∧
      circuitArrayX 0 1 = (RatFunc.X - 3) / RatFunc.X

/-- **Row zero of the one-variable circuit array.** For every natural number $s \ge 1$, the
one-variable circuit array $C^X$, with entries in the field $\mathbb{Q}(X)$ of rational functions
over $\mathbb{Q}$, satisfies $C^X_{0,s} = (3 \cdot 9^{s-2} X - 1)/(3 \cdot 9^{s-2} X)$, with an
integer exponent (so $9^{s-2} = 1/9$ when $s = 1$), and the circuit array $C$ satisfies
$C_{0,s} = (9^s/3 - 1)/(9^s/3)$ in $\mathbb{Q}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.4 (`fq-2024-hendel08232024rev2-cor-4.4`) with (2.6). -/
public theorem_wanted circuitArrayX_row_zero (s : ℕ) (hs : 1 ≤ s) :
    circuitArrayX 0 s = (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X - 1) / (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X) ∧
      circuitArray 0 s = ((9 : ℚ) ^ s / 3 - 1) / ((9 : ℚ) ^ s / 3)

/-- **Row one of the one-variable circuit array.** For every natural number $s \ge 2$, the
one-variable circuit array $C^X$, with entries in the field $\mathbb{Q}(X)$ of rational functions
over $\mathbb{Q}$, satisfies $C^X_{1,s} = (3 \cdot 9^{s-2} X - 1)/(3 \cdot 9^{s-2} X - 3)$.

The printed denominator $3 \cdot 9^{s-2} X$ is the row-zero formula; Table 2 has
$(3X - 1)/(3X - 3)$ at $s = 2$, which is $13/12$ at $X = 9$, not $26/27$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.5 (`fq-2024-hendel08232024rev2-cor-4.5`), denominator corrected from Table 2. -/
public theorem_wanted circuitArrayX_row_one (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayX 1 s =
      (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X - 1) / (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X - 3)

/-- **Row two of the one-variable circuit array.** For every natural number $s \ge 2$, the
one-variable circuit array $C^X$, with entries in the field $\mathbb{Q}(X)$ of rational functions
over $\mathbb{Q}$, satisfies
$C^X_{2,s} = (c_{2,0}(s) - c_{2,1}(s) X + c_{2,2}(s) X^2)/(9^{s-2} X - 1)^2$, where
$c_{2,0}(s) = 27 \cdot 9^{s-3} - 1$, $c_{2,1}(s) = 24(2s - 3) \cdot 9^{s-3}$ and
$c_{2,2}(s) = 81 \cdot 81^{s-3} - 3 \cdot 9^{s-3}$, with integer exponents (so $9^{s-3} = 1/9$
and $81^{s-3} = 1/81$ when $s = 2$).

The printed $c_{2,2}(X^2)$ is read as $c_{2,2}(s) X^2$, as in Remark 4.7.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.6 (`fq-2024-hendel08232024rev2-cor-4.6`). -/
public theorem_wanted circuitArrayX_row_two (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayX 2 s =
      ((27 * 9 ^ ((s : ℤ) - 3) - 1) - 24 * (2 * (s : RatFunc ℚ) - 3) * 9 ^ ((s : ℤ) - 3) * RatFunc.X +
          (81 * 81 ^ ((s : ℤ) - 3) - 3 * 9 ^ ((s : ℤ) - 3)) * RatFunc.X ^ 2) /
        (9 ^ ((s : ℤ) - 2) * RatFunc.X - 1) ^ 2

/-- **Row 0 of the multivariable circuit array.** Let $C^M$ be the multivariable circuit array, with
values in the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$.
For every integer $s \ge 1$, $C^M_{0,s} = (9^{s-1} - 1 + X_1)/9^{s-1}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.8 (`fq-2024-hendel08232024rev2-cor-4.8`). -/
public theorem_wanted circuitArrayM_row_zero (s : ℕ) (hs : 1 ≤ s) :
    circuitArrayM 0 s = (9 ^ (s - 1) - 1 + circuitVar 1) / 9 ^ (s - 1)

/-- **Row 1 of the multivariable circuit array.** Let $C^M$ be the multivariable circuit array, with
values in the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$.
For every integer $s \ge 2$,
$C^M_{1,s} = (9^{s-1} - 1 + X_1)/\bigl(3(X_1 + 3 \cdot 9^{s-2} - 1)\bigr)$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.10 (`fq-2024-hendel08232024rev2-cor-4.10`). -/
public theorem_wanted circuitArrayM_row_one (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayM 1 s = (9 ^ (s - 1) - 1 + circuitVar 1) / (3 * (circuitVar 1 + 3 * 9 ^ (s - 2) - 1))

/-- **Row 2 of the multivariable circuit array.** Let $C^M$ be the multivariable circuit array, with
values in the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$.
For every integer $s \ge 2$,
$$C^M_{2,s} = \frac{\sum_{i,j} c_{i,j}(s) X_1^i X_2^j}{(3 \cdot 9^{s-2} - 1 + X_1)^2},$$
where the sum runs over the six coefficients $c_{2,1}(s) = 9^{s-2}$, $c_{2,0}(s) = 9^{s-2} - 1$,
$c_{1,1}(s) = 4 \cdot 9^{s-2}$, $c_{1,0}(s) = 2 + (16(s-2) - 2) \cdot 9^{s-2}$,
$c_{0,1}(s) = 4 \cdot 9^{s-2}$ and
$c_{0,0}(s) = -1 + 9 \cdot 81^{s-2} - (8 + 16(s-2)) \cdot 9^{s-2}$.
Moreover, writing $E$ for the translation operator on rational sequences, the shifted coefficient
sequences $s \mapsto c_{i,j}(s+2)$, $s \ge 0$, are annihilated as in Table 4: $c_{0,0}$ by
$(E-81)(E-9)^2(E-1)$, $c_{0,1}$ by $(E-1)(E-9)$, $c_{1,0}$ by $(E-9)^2(E-1)$, $c_{1,1}$ by
$E-9$, $c_{2,0}$ by $(E-1)(E-9)$ and $c_{2,1}$ by $E-9$.

The paper's base case is $s = 3$; the identity also holds at $s = 2$. The recursions column of
Table 4 is omitted (its $X_1^0 X_2^1$ entry $G_s = 10G_{s-1} - G_{s-2}$ is misprinted for
$-9G_{s-2}$).

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.12 (`fq-2024-hendel08232024rev2-cor-4.12`) and Table 4. -/
public theorem_wanted circuitArrayM_row_two :
    (∀ s : ℕ, 2 ≤ s →
      circuitArrayM 2 s =
        (9 ^ (s - 2) * circuitVar 1 ^ 2 * circuitVar 2 + (9 ^ (s - 2) - 1) * circuitVar 1 ^ 2 +
            4 * 9 ^ (s - 2) * circuitVar 1 * circuitVar 2 +
            (2 + (16 * ((s : FractionRing (MvPolynomial ℕ ℚ)) - 2) - 2) * 9 ^ (s - 2)) * circuitVar 1 +
            4 * 9 ^ (s - 2) * circuitVar 2 +
            (-1 + 9 * 81 ^ (s - 2) - (8 + 16 * ((s : FractionRing (MvPolynomial ℕ ℚ)) - 2)) * 9 ^ (s - 2))) /
          (3 * 9 ^ (s - 2) - 1 + circuitVar 1) ^ 2) ∧
      AnnihilatesSeq ((X - C 81) * (X - C 9) ^ 2 * (X - C 1))
        (fun s : ℕ => -1 + 9 * (81 : ℚ) ^ s - (8 + 16 * (s : ℚ)) * 9 ^ s) ∧
      AnnihilatesSeq ((X - C 1) * (X - C 9)) (fun s : ℕ => 4 * (9 : ℚ) ^ s) ∧
      AnnihilatesSeq ((X - C 9) ^ 2 * (X - C 1)) (fun s : ℕ => 2 + (16 * (s : ℚ) - 2) * 9 ^ s) ∧
      AnnihilatesSeq (X - C 9) (fun s : ℕ => 4 * (9 : ℚ) ^ s) ∧
      AnnihilatesSeq ((X - C 1) * (X - C 9)) (fun s : ℕ => (9 : ℚ) ^ s - 1) ∧
      AnnihilatesSeq (X - C 9) (fun s : ℕ => (9 : ℚ) ^ s)

end

end MetaMathlibExt
