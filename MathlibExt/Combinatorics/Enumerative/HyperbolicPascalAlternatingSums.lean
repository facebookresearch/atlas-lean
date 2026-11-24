/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Induction

/-!
# Weighted alternating sums in the generalized hyperbolic Pascal triangle

`ghptRow_weighted_alternating_sum` expresses the sum with alternating weights in terms
of the ordinary and alternating sums of the rows constructed by `ghptRow`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Interior step of the generalized hyperbolic Pascal triangle.** Fix $q \in \mathbb{N}$ and a
type $R$ with an addition. A vertex is recorded as a pair $(c, x)$ of a type code $c \in \mathbb{N}$
(code $0$ for the wingers at the ends of a row, $1$ for type $A$ and $2$ for type $B$) and a
value $x \in R$. Given a list $v_0, v_1, \dots, v_m$ of such pairs with $m \ge 1$ and
$v_i = (c_i, x_i)$, the interior step lists, from left to right and for $i = 1, \dots, m$, the
type-$A$ vertex $(1, x_{i-1} + x_i)$, followed, when $i < m$, by $d_i$ copies of the type-$B$
vertex $(2, x_i)$, where $d_i = q - 4$ if $c_i = 1$ and $d_i = q - 3$ otherwise (both differences
truncated at $0$). A list with fewer than two entries gives the empty list.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Section 1 (construction of the
triangle linked to `{4, q}`). -/
def ghptInterior {R : Type*} [Add R] (q : ℕ) : List (ℕ × R) → List (ℕ × R)
  | u :: v :: [] => [(1, u.2 + v.2)]
  | u :: v :: w :: rest =>
    (1, u.2 + v.2) :: (List.replicate (if v.1 = 1 then q - 4 else q - 3) (2, v.2) ++
      ghptInterior q (v :: w :: rest))
  | _ => []

/-- **Rows of the generalized hyperbolic Pascal triangle.** Fix $q \in \mathbb{N}$, a type $R$ with
an addition, and leg sequences $\alpha, \beta \colon \mathbb{N} \to R$ (left and right). Row $n$ is
a list of pairs (type code, value) as in the interior step, defined for every $q$ by recursion:
row $1$ is $(0, \alpha_1), (0, \beta_1)$, and for $n \ge 1$ row $n + 1$ is $(0, \alpha_{n+1})$,
followed by the interior step applied to row $n$, followed by $(0, \beta_{n+1})$. Row $0$ (the
indeterminate root $\Omega$) is represented by the empty list. For $q \ge 5$, row $n$ lists from
left to right the vertices of row $n$ of the generalized hyperbolic Pascal triangle linked to the
hyperbolic mosaic $\{4, q\}$, with code $0$ for the wingers.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Section 1 (construction of the
triangle linked to `{4, q}`, Figure 1). -/
def ghptRow {R : Type*} [Add R] (q : ℕ) (α β : ℕ → R) : ℕ → List (ℕ × R)
  | 0 => []
  | 1 => [(0, α 1), (0, β 1)]
  | n + 2 => (0, α (n + 2)) :: (ghptInterior q (ghptRow q α β (n + 1)) ++ [(0, β (n + 2))])

/-- **Rows 3 and 4 of an example generalized hyperbolic Pascal triangle.** In the generalized
hyperbolic Pascal triangle linked to $\{4, 5\}$ (so $q = 5$) with legs $\alpha_n = 3n$ and
$\beta_n = 3^n$ in $\mathbb{N}$, the values of the entries of row $3$, from left to right, are
$9, 12, 6, 15, 27$, and those of row $4$ are $12, 21, 12, 18, 6, 6, 21, 15, 42, 81$.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Figure 1. -/
theorem ghptRow_figure_one :
    (ghptRow 5 (fun n => 3 * n) (fun n => 3 ^ n) 3).map Prod.snd = [9, 12, 6, 15, 27] ∧
      (ghptRow 5 (fun n => 3 * n) (fun n => 3 ^ n) 4).map Prod.snd =
        [12, 21, 12, 18, 6, 6, 21, 15, 42, 81] := by
  decide +kernel

/-- **Weighted alternating row sums of the generalized hyperbolic Pascal triangle.** Let
$q, n \in \mathbb{N}$, let $\alpha, \beta \colon \mathbb{N} \to \mathbb{C}$ and let
$v, w \in \mathbb{C}$. Let $x_0, x_1, \dots, x_{\ell - 1}$ be the values, from left to right, of
the entries of row $n$ of the recursively defined generalized hyperbolic Pascal triangle with
parameter $q$ and legs $\alpha$ and $\beta$ (for $q \ge 5$, the triangle linked to the hyperbolic
mosaic $\{4, q\}$), and put $\hat s_n = \sum_i x_i$, $\tilde s_n = \sum_i (-1)^i x_i$ and
$\tilde s_{(v,w),n} = \sum_{i \text{ even}} v x_i + \sum_{i \text{ odd}} w x_i$. Then
$\tilde s_{(v,w),n} = \frac{\hat s_n + \tilde s_n}{2} v + \frac{\hat s_n - \tilde s_n}{2} w$ and
$\tilde s_{(v,w),n} = \frac{v + w}{2} \hat s_n + \frac{v - w}{2} \tilde s_n$.

The identities do not use the structure of the rows; they hold for every $q$ and $n$.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Corollary 2
(`integers-2024-A84-cor-2`). -/
theorem ghptRow_weighted_alternating_sum (q n : ℕ) (α β : ℕ → ℂ) (v w : ℂ) :
    let r := (ghptRow q α β n).map Prod.snd
    let alt := (r.mapIdx fun i x => (-1) ^ i * x).sum
    let weighted := (r.mapIdx fun i x => (if Even i then v else w) * x).sum
    weighted = (r.sum + alt) / 2 * v + (r.sum - alt) / 2 * w ∧
      weighted = (v + w) / 2 * r.sum + (v - w) / 2 * alt := by
  intro r alt weighted
  suffices h : weighted = (v + w) / 2 * r.sum + (v - w) / 2 * alt by
    exact ⟨h.trans (by ring), h⟩
  dsimp only [weighted, alt]
  generalize r = l
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    simp only [List.mapIdx_concat, List.sum_append, List.sum_singleton, ih]
    by_cases hi : Even l.length <;> simp [neg_one_pow_eq_ite, hi] <;> ring

end

end MetaMathlibExt
