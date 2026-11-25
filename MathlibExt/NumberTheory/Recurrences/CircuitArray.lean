/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import MathlibExt.Algebra.LinearRecurrence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The circuit array of Evans and Hendel and its row zero

Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the Rows of
the Circuit Array*, Fibonacci Quarterly 62 (2024), read the circuit array off a triangular grid of
unit resistances that is reduced one row at a time by delta-wye and wye-delta transformations
(Section 2). This file defines that reduction, the circuit array of a choice of boundary values,
the numerical circuit array and the one-variable circuit array, and proves the closed form of
their row zero (Corollary 4.4).

## Main definitions

* `MetaMathlibExt.circuitGrid`: the labellings `T^m` of the grid after `m` reductions.
* `MetaMathlibExt.circuitArrayOf`: the circuit array of a choice of boundary values.
* `MetaMathlibExt.circuitArray`: the circuit array `C_{i,j}` in `ℚ` (Table 1).
* `MetaMathlibExt.circuitArrayX`: the one-variable circuit array `C^X_{i,j}` in `ℚ(X)` (Table 2).

## Main statements

* `MetaMathlibExt.circuitArrayX_row_zero`: for `s ≥ 1`,
  `C^X_{0,s} = (3 · 9 ^ (s - 2) X - 1) / (3 · 9 ^ (s - 2) X)`, with an integer exponent, and
  `C_{0,s} = (9 ^ s / 3 - 1) / (9 ^ s / 3)`.

## Proof

Write `a = d - 1` and `b = r - d` for the distances of the triangle in row `r` and diagonal `d`
from the left and right boundaries. A reduction computes each edge from the triangles next to it,
so after `m` reductions the left edges with `m ≤ a` and `m ≤ b + 1`, the right edges with
`m ≤ a + 1` and `m ≤ b`, and the bases with `m ≤ a + 1` and `m ≤ b + 1` are still `1`. The entry
`C_{0,k+1}` is the left edge of the triangle with `a = b = k` after `k + 1` reductions, the front
of the left boundary, which the right boundary has not reached. Behind the front the right and
base edges are `1` and ahead of it every edge is `1`, so the left-edge function turns a front
value `f` into `(8 + f) / 9`. Hence `f - 1` is divided by `9` at each reduction, starting from the
boundary value `(X - 3) / X`, or `2 / 3` for the numerical array.
-/

namespace MetaMathlibExt

@[expose] public section

/-! ### Section 2: the circuit array

The circuit array is read off a triangular grid of resistances that is reduced one row at a time
(Steps 1-5 of Section 2: a `Δ`-`Y` transformation on every upright triangle, series on the boundary,
`Y`-`Δ` on the remaining out-stars). A labelling of a grid is a function `T r d e`, the resistance
of edge `e` of the upright triangle in row `r` (from the top) and diagonal `d` (from the left), with
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

/-! ### Row zero -/

section RowZero

variable {K : Type*} [Field K]

/-- The entry `C_{0, k+1}` of a circuit array is the left edge of the triangle in row `2k + 1` and
diagonal `k + 1` of the grid reduced `k + 1` times. -/
private theorem circuitArrayOf_zero_succ (bdry : ℕ → Option K) (k : ℕ) :
    circuitArrayOf bdry 0 (k + 1) = circuitGrid bdry (k + 1) (2 * k + 1) (k + 1) .left := by
  rw [circuitArrayOf, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
    show k + 1 - (0 + 1) / 2 = k + 1 by omega]
  simp only [Even.zero, ite_true]

private theorem circuitGrid_succ_left (bdry : ℕ → Option K) (m r d : ℕ) (hd : d ≠ 1) :
    circuitGrid bdry (m + 1) r d .left =
      circuitLeftEdge (circuitGrid bdry m r (d - 1)) (circuitGrid bdry m r d)
        (circuitGrid bdry m (r + 1) d) := by
  simp [circuitGrid, circuitReduce, hd]

private theorem circuitGrid_succ_right (bdry : ℕ → Option K) (m r d : ℕ) (hd : d ≠ r) :
    circuitGrid bdry (m + 1) r d .right =
      circuitRightEdge (circuitGrid bdry m r d) (circuitGrid bdry m r (d + 1))
        (circuitGrid bdry m (r + 1) (d + 1)) := by
  simp [circuitGrid, circuitReduce, hd]

private theorem circuitGrid_succ_base (bdry : ℕ → Option K) (m r d : ℕ) :
    circuitGrid bdry (m + 1) r d .base =
      circuitBaseEdge (circuitGrid bdry m (r + 2) (d + 1)) (circuitGrid bdry m (r + 1) d)
        (circuitGrid bdry m (r + 1) (d + 1)) := by
  simp [circuitGrid, circuitReduce]

private theorem circuitGrid_one_left (bdry : ℕ → Option K) (r : ℕ) :
    circuitGrid bdry 1 r 1 .left =
      (bdry 1).getD (circuitPerimeter (fun _ => 1) (fun _ => 1)) := by
  simp [circuitGrid, circuitReduce]

variable [CharZero K]

private theorem circuitLeftEdge_one :
    circuitLeftEdge (fun _ => (1 : K)) (fun _ => 1) (fun _ => 1) = 1 := by
  norm_num [circuitLeftEdge, circuitY, circuitRightArm, circuitLeftArm, circuitTopArm,
    circuitDelta]

private theorem circuitRightEdge_one :
    circuitRightEdge (fun _ => (1 : K)) (fun _ => 1) (fun _ => 1) = 1 := by
  norm_num [circuitRightEdge, circuitY, circuitRightArm, circuitLeftArm, circuitTopArm,
    circuitDelta]

private theorem circuitBaseEdge_one :
    circuitBaseEdge (fun _ => (1 : K)) (fun _ => 1) (fun _ => 1) = 1 := by
  norm_num [circuitBaseEdge, circuitY, circuitRightArm, circuitLeftArm, circuitTopArm,
    circuitDelta]

/-- After `m` reductions, the edges at distance at least `m` from both boundaries are still `1`:
writing `a = d - 1` and `b = r - d`, the left edge is `1` when `m ≤ a` and `m ≤ b + 1`, the right
edge when `m ≤ a + 1` and `m ≤ b`, and the base when `m ≤ a + 1` and `m ≤ b + 1`. -/
private theorem circuitGrid_eq_one (bdry : ℕ → Option K) (m : ℕ) :
    (∀ r d, m + 1 ≤ d → m + d ≤ r + 1 → circuitGrid bdry m r d .left = 1) ∧
      (∀ r d, m ≤ d → m + d ≤ r → circuitGrid bdry m r d .right = 1) ∧
      (∀ r d, m ≤ d → m + d ≤ r + 1 → circuitGrid bdry m r d .base = 1) := by
  induction m with
  | zero => exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨hL, hR, hB⟩ := ih
    have hA : ∀ r d, m + 1 ≤ d → m + d ≤ r → circuitGrid bdry m r d = fun _ => 1 := by
      intro r d h1 h2
      funext e
      cases e
      · exact hL r d h1 (by omega)
      · exact hR r d (by omega) h2
      · exact hB r d (by omega) (by omega)
    refine ⟨fun r d h1 h2 => ?_, fun r d h1 h2 => ?_, fun r d h1 h2 => ?_⟩
    · rw [circuitGrid_succ_left bdry m r d (by omega), hA r (d - 1) (by omega) (by omega),
        hA r d (by omega) (by omega), hA (r + 1) d (by omega) (by omega)]
      exact circuitLeftEdge_one
    · rw [circuitGrid_succ_right bdry m r d (by omega), hA r d (by omega) (by omega),
        hA r (d + 1) (by omega) (by omega), hA (r + 1) (d + 1) (by omega) (by omega)]
      exact circuitRightEdge_one
    · rw [circuitGrid_succ_base bdry m r d, hA (r + 2) (d + 1) (by omega) (by omega),
        hA (r + 1) d (by omega) (by omega), hA (r + 1) (d + 1) (by omega) (by omega)]
      exact circuitBaseEdge_one

private theorem circuitGrid_eq_one_fun (bdry : ℕ → Option K) (m r d : ℕ) (h1 : m + 1 ≤ d)
    (h2 : m + d ≤ r) : circuitGrid bdry m r d = fun _ => 1 := by
  obtain ⟨hL, hR, hB⟩ := circuitGrid_eq_one bdry m
  funext e
  cases e
  · exact hL r d h1 (by omega)
  · exact hR r d (by omega) h2
  · exact hB r d (by omega) (by omega)

private theorem front_step (c x : K) (hx : x ≠ 0) (hc : c ≠ 3 * x) :
    circuitY (circuitDelta 1 1 (1 - c / x)) (circuitDelta 1 1 1) (circuitDelta 1 1 1) =
      1 - c / (9 * x) := by
  obtain ⟨D, rfl⟩ : ∃ D, c = 3 * x - D := ⟨3 * x - c, by ring⟩
  have hD : D ≠ 0 := by rintro rfl; exact hc (by ring)
  have e1 : (1 + 1 + (1 - (3 * x - D) / x) : K) = D / x := by field_simp; ring
  rw [circuitY, circuitDelta, circuitDelta, e1]
  field_simp
  ring

/-- The front of the left boundary: after `k + 1` reductions, the left edge of the triangle on
diagonal `k + 1` (at distance `k` from the left boundary) of a row `r ≥ 2k + 1` is
`1 - c / 9 ^ k`, where `1 - c` is the left boundary value after the first reduction. -/
private theorem circuitGrid_front (bdry : ℕ → Option K) (c : K)
    (h1 : (bdry 1).getD (2 / 3) = 1 - c) (hc : ∀ k : ℕ, c ≠ 3 * 9 ^ k) (k : ℕ) :
    ∀ r : ℕ, 2 * k + 1 ≤ r → circuitGrid bdry (k + 1) r (k + 1) .left = 1 - c / 9 ^ k := by
  induction k with
  | zero =>
    intro r _
    have hP : circuitPerimeter (fun _ => (1 : K)) (fun _ => 1) = 2 / 3 := by
      norm_num [circuitPerimeter, circuitLeftArm, circuitTopArm, circuitDelta]
    rw [circuitGrid_one_left, hP, h1, pow_zero, div_one]
  | succ k ih =>
    intro r hr
    obtain ⟨_, hR, hB⟩ := circuitGrid_eq_one bdry (k + 1)
    rw [circuitGrid_succ_left bdry (k + 1) r (k + 1 + 1) (by omega),
      circuitGrid_eq_one_fun bdry (k + 1) r (k + 1 + 1) (by omega) (by omega),
      circuitGrid_eq_one_fun bdry (k + 1) (r + 1) (k + 1 + 1) (by omega) (by omega),
      show k + 1 + 1 - 1 = k + 1 by omega]
    simp only [circuitLeftEdge, circuitRightArm, circuitLeftArm, circuitTopArm]
    rw [hR r (k + 1) le_rfl (by omega), hB r (k + 1) le_rfl (by omega), ih r (by omega)]
    rw [front_step c (9 ^ k) (pow_ne_zero _ (by norm_num)) (hc k), pow_succ']

end RowZero

/-- **Row zero of the one-variable circuit array.** For every natural number $s \ge 1$, the
one-variable circuit array $C^X$, with entries in the field $\mathbb{Q}(X)$ of rational functions
over $\mathbb{Q}$, satisfies $C^X_{0,s} = (3 \cdot 9^{s-2} X - 1)/(3 \cdot 9^{s-2} X)$, with an
integer exponent (so $9^{s-2} = 1/9$ when $s = 1$), and the circuit array $C$ satisfies
$C_{0,s} = (9^s/3 - 1)/(9^s/3)$ in $\mathbb{Q}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.4 (`fq-2024-hendel08232024rev2-cor-4.4`) with (2.6). -/
theorem circuitArrayX_row_zero (s : ℕ) (hs : 1 ≤ s) :
    circuitArrayX 0 s =
        (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X - 1) / (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X) ∧
      circuitArray 0 s = ((9 : ℚ) ^ s / 3 - 1) / ((9 : ℚ) ^ s / 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  constructor
  · have hc : ∀ n : ℕ, 3 / (RatFunc.X : RatFunc ℚ) ≠ 3 * 9 ^ n := by
      intro n h
      rw [div_eq_iff hX] at h
      have h' : (9 : RatFunc ℚ) ^ n * RatFunc.X = 1 := by linear_combination -h / 3
      have hp : ((9 : Polynomial ℚ) ^ n * Polynomial.X : Polynomial ℚ) = 1 := by
        apply RatFunc.algebraMap_injective ℚ
        rw [map_mul, map_pow, map_one, RatFunc.algebraMap_X, map_ofNat]
        exact h'
      simpa using congrArg (Polynomial.eval 0) hp
    have h1 : ((fun m => if m = 1 then some ((RatFunc.X - 3) / RatFunc.X) else none :
        ℕ → Option (RatFunc ℚ)) 1).getD (2 / 3) = 1 - 3 / RatFunc.X := by
      simp only [ite_true, Option.getD_some]
      field_simp
    rw [circuitArrayX, circuitArrayOf_zero_succ,
      circuitGrid_front _ (3 / RatFunc.X) h1 hc k (2 * k + 1) le_rfl,
      show (((k + 1 : ℕ) : ℤ) - 2) = (k : ℤ) - 1 by push_cast; ring,
      zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]
    field_simp
    ring
  · have hc : ∀ n : ℕ, (1 / 3 : ℚ) ≠ 3 * 9 ^ n := by
      intro n h
      have : (1 : ℚ) ≤ 9 ^ n := one_le_pow₀ (by norm_num)
      linarith
    rw [circuitArray, circuitArrayOf_zero_succ,
      circuitGrid_front _ (1 / 3) (by norm_num) hc k (2 * k + 1) le_rfl]
    field_simp
    ring

end

end MetaMathlibExt
