/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Complex.Basic

/-!
# Alternating sums in the generalized hyperbolic Pascal triangle

Statements from Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the
Generalized Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84: the identity
relating a linear recurrence `f` and an inhomogeneous recurrence `G` with the same
coefficients (Theorem 1, Corollary 1, quoted from the authors' earlier paper), and the
weighted alternating row sums of the generalized hyperbolic Pascal triangle linked to the
mosaic `{4, q}` (Corollary 2).

The recurrence (10) for the alternating row sums (Theorem 2), its generating function
(Theorem 3) and explicit formula (Theorem 4) are not stated: they fail for simple leg
sequences (see the audit table).
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
an addition, and leg sequences $\alpha, \beta \colon \mathbb{N} \to R$ (left and right). Row $n$ of
the generalized hyperbolic Pascal triangle linked to the mosaic $\{4, q\}$ is the list of its
vertices from left to right, each recorded as a pair (type code, value) as in the interior step,
with code $0$ for the wingers. Row $1$ is $(0, \alpha_1), (0, \beta_1)$, and for $n \ge 1$ row
$n + 1$ is $(0, \alpha_{n+1})$, followed by the interior step applied to row $n$, followed by
$(0, \beta_{n+1})$. Row $0$ (the indeterminate root $\Omega$) is represented by the empty list.

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

/-- **Convolution identity for an inhomogeneous linear recurrence.** Let $k \in \mathbb{N}$ and let
$A, f, G, w \colon \mathbb{N} \to \mathbb{C}$ be sequences such that, for every $m \ge k$,
$f_m = \sum_{i=1}^{k} A_i f_{m-i}$ and $G_m = \sum_{i=1}^{k} A_i G_{m-i} + w_{m-k}$. Then for
every $n \ge k$,

$$\sum_{j=0}^{k-1} f_j G_{n+k-j} =
\sum_{j=0}^{k-1} \sum_{i=0}^{k-1-j} f_{n-j} A_{j+1+i} G_{k-1-i} +
\sum_{j=0}^{k-2} \sum_{i=1}^{k-1-j} f_j A_i G_{n+k-j-i} + \sum_{j=0}^{n} f_{n-j} w_j.$$

The identity is quoted from Belbachir–Rami–Szalay 2022; its hypotheses $A_k \neq 0$ and
$k \ge 1$ are not needed.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Theorem 1
(`integers-2024-A84-thm-1`). -/
public theorem_wanted linearRecurrence_inhomogeneous_identity (k : ℕ) (A f G w : ℕ → ℂ)
    (hf : ∀ n, k ≤ n → f n = ∑ i ∈ Finset.Icc 1 k, A i * f (n - i))
    (hG : ∀ n, k ≤ n → G n = ∑ i ∈ Finset.Icc 1 k, A i * G (n - i) + w (n - k))
    {n : ℕ} (hn : k ≤ n) :
    ∑ j ∈ Finset.range k, f j * G (n + k - j) =
      ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (k - j), f (n - j) * A (j + 1 + i) * G (k - 1 - i) +
        ∑ j ∈ Finset.range (k - 1), ∑ i ∈ Finset.Icc 1 (k - 1 - j),
          f j * A i * G (n + k - j - i) +
        ∑ j ∈ Finset.range (n + 1), f (n - j) * w j

/-- **Explicit formula for an inhomogeneous linear recurrence.** Let $k \in \mathbb{N}$ and let
$A, f, G, w \colon \mathbb{N} \to \mathbb{C}$ be sequences such that, for every $m \ge k$,
$f_m = \sum_{i=1}^{k} A_i f_{m-i}$ and $G_m = \sum_{i=1}^{k} A_i G_{m-i} + w_{m-k}$. Suppose
moreover that $f_j = 0$ for every $j < k - 1$ and $f_{k-1} = 1$. Then for every $n \ge k - 1$,

$$G_{n+1} = \sum_{j=0}^{k-1} \sum_{i=0}^{k-1-j} f_{n-j} A_{j+1+i} G_{k-1-i} +
\sum_{j=0}^{n} f_{n-j} w_j.$$

For $k = 0$ the index $k - 1$ is read as $0$, so the hypotheses cannot all hold. The source
states the formula for $n \ge k$, as a consequence of its Theorem 1.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Corollary 1
(`integers-2024-A84-cor-1`). -/
public theorem_wanted linearRecurrence_inhomogeneous_explicit (k : ℕ) (A f G w : ℕ → ℂ)
    (hf : ∀ n, k ≤ n → f n = ∑ i ∈ Finset.Icc 1 k, A i * f (n - i))
    (hG : ∀ n, k ≤ n → G n = ∑ i ∈ Finset.Icc 1 k, A i * G (n - i) + w (n - k))
    (hf₀ : ∀ j, j + 1 < k → f j = 0) (hf₁ : f (k - 1) = 1) {n : ℕ} (hn : k ≤ n + 1) :
    G (n + 1) =
      ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (k - j), f (n - j) * A (j + 1 + i) * G (k - 1 - i) +
        ∑ j ∈ Finset.range (n + 1), f (n - j) * w j

/-- **Weighted alternating row sums of the generalized hyperbolic Pascal triangle.** Let
$q, n \in \mathbb{N}$, let $\alpha, \beta \colon \mathbb{N} \to \mathbb{C}$ and let
$v, w \in \mathbb{C}$. Let $x_0, x_1, \dots, x_{\ell - 1}$ be the values of the entries of row $n$
of the generalized hyperbolic Pascal triangle linked to $\{4, q\}$ with legs $\alpha$ and $\beta$,
from left to right, and put $\hat s_n = \sum_i x_i$, $\tilde s_n = \sum_i (-1)^i x_i$ and
$\tilde s_{(v,w),n} = \sum_{i \text{ even}} v x_i + \sum_{i \text{ odd}} w x_i$. Then
$\tilde s_{(v,w),n} = \frac{\hat s_n + \tilde s_n}{2} v + \frac{\hat s_n - \tilde s_n}{2} w$ and
$\tilde s_{(v,w),n} = \frac{v + w}{2} \hat s_n + \frac{v - w}{2} \tilde s_n$.

The identities do not use the structure of the rows; they hold for every $q$ and $n$.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Corollary 2
(`integers-2024-A84-cor-2`). -/
public theorem_wanted ghptRow_weighted_alternating_sum (q n : ℕ) (α β : ℕ → ℂ) (v w : ℂ) :
    let r := (ghptRow q α β n).map Prod.snd
    let alt := (r.mapIdx fun i x => (-1) ^ i * x).sum
    let weighted := (r.mapIdx fun i x => (if Even i then v else w) * x).sum
    weighted = (r.sum + alt) / 2 * v + (r.sum - alt) / 2 * w ∧
      weighted = (v + w) / 2 * r.sum + (v - w) / 2 * alt

end

end MetaMathlibExt
