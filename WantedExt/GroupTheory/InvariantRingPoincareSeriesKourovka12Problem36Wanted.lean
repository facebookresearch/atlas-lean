/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Poincaré series of modular invariant rings (Kourovka Notebook Problem 12.36)

Kourovka Notebook, Archive of Solved Problems, Problem 12.36 (D. Carlisle, P. H. Kropholler): for `G
≤ GL(V)`, `V` an `n`-dimensional space over `𝔽ₚ`, the Poincaré series `∑ₘ bₘ tᵐ` of `T = S(V*)^G`
has a Laurent expansion `∑_{i ≥ -n} aᵢ (1 - t)ⁱ` about `t = 1` with `a_{-n} = 1/|G|`. Conjecture:
`a_{-n+1} = r/(2|G|)`, where `r = ∑_W ((p - 1) α_W + s_W - 1)` over the maximal subspaces `W` of
`V`, `|G_W| = p^{α_W} s_W` with `p ∤ s_W`, and `G_W` is the pointwise stabilizer of `W`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.InvariantRingPoincareSeriesKourovka12Problem36Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.36 (D.
Carlisle, P. H. Kropholler). UnsolvedMath record UM-00700855 (`KOU-12.36`), dataset
ulamai/UnsolvedMath v1.8.0.

`V = 𝔽ₚⁿ` with `G` acting on column vectors, `S(V*) = 𝔽ₚ[x₀, …, x_{n-1}]` (coordinate functions),
and `T` consists of the polynomials `f` with `f(g x) = f(x)` (formal linear substitution) for all `g
∈ G`; `bₘ = dim Tₘ`. The Laurent expansion is encoded by polynomials `A, B ∈ ℚ[t]` with `B(1) ≠ 0`
and `B (1 - t)ⁿ P = A` in `ℚ⟦t⟧`. For every `G` such `A, B` exist: `P` is rational (Hilbert-Serre)
and, as the problem states, `(1 - t)ⁿ P` has no pole at `t = 1`. Any two such pairs `(A, B)`, `(A₂,
B₂)` satisfy `A B₂ = A₂ B` (multiply `B (1 - t)ⁿ P = A` by `B₂`), so the rational function `A/B = (1
- t)ⁿ P = ∑ᵢ aᵢ₋ₙ (1 - t)ⁱ` is determined by `G` and the stated value is `a_{-n+1} = -(A/B)'(1)` for
every choice. Maximal subspaces are the coatoms of the subspace lattice (for `n = 0` there are none,
`r = 0`, and both sides vanish). For `n = 1` and `|G| = d` the statement reads `(d - 1)/(2d) = (d -
1)/(2d)`.
-/

open MvPolynomial

/-- **Linear substitution by a matrix.** For natural numbers $p$ and $n$ and an $n \times n$ matrix
$g$ over $\mathbb{Z}/p\mathbb{Z}$, the linear substitution by $g$ is the
$\mathbb{Z}/p\mathbb{Z}$-algebra endomorphism of the polynomial ring
$(\mathbb{Z}/p\mathbb{Z})[x_0, \dots, x_{n-1}]$ that sends each variable $x_i$ to
$\sum_j g_{ij} x_j$. Viewing polynomials as functions on $V = (\mathbb{Z}/p\mathbb{Z})^n$, it sends
$f$ to the function $x \mapsto f(gx)$. -/
noncomputable def linSubst {p n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod p)) :
    MvPolynomial (Fin n) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin n) (ZMod p) :=
  aeval fun i => ∑ j, C (g i j) * X j

/-- **Homogeneous component of the invariant ring.** For natural numbers $p$ and $n$, a subgroup
$G$ of $\mathrm{GL}_n(\mathbb{Z}/p\mathbb{Z})$ and $m \in \mathbb{N}$, the degree-$m$ component
$T_m$ of the invariant ring $T$ of $G$ is the $\mathbb{Z}/p\mathbb{Z}$-submodule of the polynomial
ring $(\mathbb{Z}/p\mathbb{Z})[x_0, \dots, x_{n-1}]$ consisting of the homogeneous polynomials $f$
of degree $m$ that are fixed by the linear substitution $x_i \mapsto \sum_j g_{ij} x_j$ of every
$g \in G$, that is, with $f(gx) = f(x)$ as polynomials for all $g \in G$, where
$x = (x_0, \dots, x_{n-1})$ is the column vector of variables. -/
noncomputable def invariantComponent {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p))) (m : ℕ) :
    Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)) :=
  homogeneousSubmodule (Fin n) (ZMod p) m ⊓
    ⨅ g ∈ G, LinearMap.ker
      ((linSubst (g : Matrix (Fin n) (Fin n) (ZMod p))).toLinearMap - LinearMap.id)

/-- **Poincaré series of the invariant ring.** For natural numbers $p$ and $n$ and a subgroup $G$
of $\mathrm{GL}_n(\mathbb{Z}/p\mathbb{Z})$, the Poincaré series of the invariant ring $T$ of $G$
is the formal power series $P(t) = \sum_{m \ge 0} b_m t^m$ over $\mathbb{Q}$, where $b_m$ is the
rank over $\mathbb{Z}/p\mathbb{Z}$ (the dimension, when $p$ is prime) of the degree-$m$
homogeneous component $T_m$ of $T$. -/
noncomputable def poincareSeries {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p))) :
    PowerSeries ℚ :=
  PowerSeries.mk fun m => (Module.finrank (ZMod p) (invariantComponent G m) : ℚ)

/-- **Pointwise stabilizer.** For natural numbers $p$ and $n$, a subgroup $G$ of
$\mathrm{GL}_n(\mathbb{Z}/p\mathbb{Z})$ and a submodule $W$ of $V = (\mathbb{Z}/p\mathbb{Z})^n$,
the pointwise stabilizer $G_W$ of $W$ in $G$ is the set of all $g \in G$ with $g w = w$ for every
$w \in W$, where $g$ acts on column vectors by matrix multiplication. -/
def pointwiseStabilizer {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p)))
    (W : Submodule (ZMod p) (Fin n → ZMod p)) : Set (GL (Fin n) (ZMod p)) :=
  {g | g ∈ G ∧ ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) (ZMod p)).mulVec w = w}

/-- **Hyperplane term.** For natural numbers $p$ and $n$, a subgroup $G$ of
$\mathrm{GL}_n(\mathbb{Z}/p\mathbb{Z})$ and a submodule $W$ of $V = (\mathbb{Z}/p\mathbb{Z})^n$, let
$N$ be the number of elements of the pointwise stabilizer $G_W$ of $W$ in $G$ (taken to be $0$
if $G_W$ is infinite), let $\alpha_W$ be the exponent of $p$ in the prime factorization of $N$
(which is $0$ unless $p$ is prime and $N \ne 0$), and let $s_W = N / p^{\alpha_W}$, so that
$N = p^{\alpha_W} s_W$ and $p \nmid s_W$ when $p$ is prime and $N \ne 0$. The hyperplane term of
$W$ is the rational number $(p - 1) \alpha_W + s_W - 1$. -/
noncomputable def hyperplaneTerm {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p)))
    (W : Submodule (ZMod p) (Fin n → ZMod p)) : ℚ :=
  let N := Nat.card (pointwiseStabilizer G W)
  (((p - 1) * N.factorization p : ℕ) : ℚ) + ((N / p ^ N.factorization p : ℕ) : ℚ) - 1

/-- **Hyperplane sum.** For natural numbers $p$ and $n$ and a subgroup $G$ of
$\mathrm{GL}_n(\mathbb{Z}/p\mathbb{Z})$, the hyperplane sum of $G$ is the rational number
$r = \sum_W ((p - 1) \alpha_W + s_W - 1)$, where $W$ runs over the maximal proper submodules
of $V = (\mathbb{Z}/p\mathbb{Z})^n$ (the hyperplanes of $V$ when $p$ is prime) and
$(p - 1) \alpha_W + s_W - 1$ is the hyperplane term of $W$: here $N_W$ is the number of elements
of the pointwise stabilizer $G_W$ of $W$ in $G$ (taken to be $0$ if $G_W$ is infinite),
$\alpha_W$ is the exponent of $p$ in the prime factorization of $N_W$ (which is $0$ unless $p$
is prime and $N_W \ne 0$), and $s_W = N_W / p^{\alpha_W}$, so that $N_W = p^{\alpha_W} s_W$.
The sum is defined to be $0$ if infinitely many of its terms are nonzero, which can happen only
for $p = 0$. -/
noncomputable def hyperplaneSum {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p))) : ℚ :=
  ∑ᶠ (W : Submodule (ZMod p) (Fin n → ZMod p)) (_ : IsCoatom W), hyperplaneTerm G W

/-- **Carlisle–Kropholler conjecture on the second Laurent coefficient (Kourovka 12.36).** The
statement that for every prime $p$, every $n \in \mathbb{N}$ and every subgroup $G$ of
$\mathrm{GL}_n(\mathbb{F}_p)$, with $P(t)$ the Poincaré series of the invariant ring of $G$ and
$r$ the hyperplane sum of $G$, there are polynomials $A, B \in \mathbb{Q}[t]$ with $B(1) \ne 0$
and $B(t) (1 - t)^n P(t) = A(t)$ in $\mathbb{Q}[[t]]$ such that
$$\frac{A(1) B'(1) - A'(1) B(1)}{B(1)^2} = \frac{r}{2 |G|}.$$

Here $(1 - t)^n P(t) = A(t) / B(t) = a_{-n} + a_{-n+1} (1 - t) + \cdots$, where
$P(t) = \sum_{i \ge -n} a_i (1 - t)^i$ is the Laurent expansion of $P$ at $t = 1$, so the left
side is $a_{-n+1} = -(A / B)'(1)$, and the conjecture says $a_{-n+1} = r / (2 |G|)$. -/
def poincareSeriesSecondCoefficient : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (n : ℕ) (G : Subgroup (GL (Fin n) (ZMod p))),
    ∃ A B : Polynomial ℚ, B.eval 1 ≠ 0 ∧
      ((B * (1 - Polynomial.X) ^ n : Polynomial ℚ) : PowerSeries ℚ) * poincareSeries G =
        (A : PowerSeries ℚ) ∧
      (A.eval 1 * (Polynomial.derivative B).eval 1 - (Polynomial.derivative A).eval 1 * B.eval 1) /
          B.eval 1 ^ 2 = hyperplaneSum G / (2 * Nat.card G)

/-- **Benson–Crawley-Boevey hyperplane formula (Kourovka 12.36).** For every prime $p$, every
$n \in \mathbb{N}$ and every subgroup $G$ of $\mathrm{GL}_n(\mathbb{F}_p)$, with $P(t)$ the
Poincaré series of the invariant ring of $G$ and $r$ the hyperplane sum of $G$, there are
polynomials $A, B \in \mathbb{Q}[t]$ with $B(1) \ne 0$ and $B(t) (1 - t)^n P(t) = A(t)$ in
$\mathbb{Q}[[t]]$ such that
$$\frac{A(1) B'(1) - A'(1) B(1)}{B(1)^2} = \frac{r}{2 |G|}.$$
That is, the Carlisle–Kropholler conjecture on the second Laurent coefficient holds: the
coefficient $a_{-n+1}$ in the expansion $P(t) = \sum_{i \ge -n} a_i (1 - t)^i$ equals
$r / (2 |G|)$.

Resolved true: the Kourovka Archive records the conjecture as proved by Benson and Crawley-Boevey
(Bull. London Math. Soc. 27 (1995)), with a second proof by Neeman (Comment. Math. Helv. 70 (1995))
based on the Grothendieck-Riemann-Roch theorem. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 12.36 (D. Carlisle, P. H. Kropholler); resolution: D. J. Benson
and W. W. Crawley-Boevey, Bull. London Math. Soc. 27 (1995), no. 5, 435-440; A. Neeman, Comment.
Math. Helv. 70 (1995), no. 3, 339-349, Kourovka Archive, Problem 12.36: the conjecture is proved.
-/
public theorem_wanted poincareSeriesSecondCoefficient_holds : poincareSeriesSecondCoefficient

end MathlibExt.GroupTheory.InvariantRingPoincareSeriesKourovka12Problem36Wanted
