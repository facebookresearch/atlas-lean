# Power series identities over complete non-archimedean fields

This node is still to be broken down. It covers the evaluation of power series identities at points of
a complete non-archimedean field, which the page on
[the p-adic exponential](p-adic-exponential.md) applies on the balls $\mathfrak{m}_K^r$ and
$1 + \mathfrak{m}_K^r$. Let $K$ be a field complete for a non-archimedean absolute value (if it is trivial, a
series converges only when its terms are eventually $0$, and the statements below are finite identities).

- **Series.** A series $\sum_n a_n$ in $K$ converges if and only if $a_n \to 0$, and then every
  rearrangement converges to the same sum, as does every partition of the terms into finitely or
  infinitely many convergent subseries.
- **Products.** If $\sum_n a_n$ and $\sum_n b_n$ converge, their Cauchy product
  $\sum_n \sum_{i + j = n} a_i b_j$ converges to the product of the sums. Hence, for power series
  $f, g \in K[[X]]$ converging at $x \in K$, the product $fg$ converges at $x$ and $(fg)(x) = f(x)g(x)$;
  the same holds in several variables, for the double series of $f(X)g(Y)$ at $(x, y)$.
- **Substitution.** Let $f = \sum_n a_n X^n$ and $g = \sum_{m \ge 1} b_m X^m$ in $K[[X]]$, and $x \in K$
  with $b_m x^m \to 0$ and $\lvert a_n \rvert \rho^n \to 0$ for $\rho = \sup_m \lvert b_m x^m \rvert$. Then
  $f \circ g$ converges at $x$ and $(f \circ g)(x) = f(g(x))$. Proof by regrouping: the terms
  $c_{n,k} = a_n [X^k](g^n) x^k$ tend to $0$, since $\lvert c_{n,k} \rvert \le \lvert a_n \rvert \rho^n$ controls large $n$ and,
  for each $n \ge 1$, $\lvert c_{n,k} \rvert \le \lvert a_n \rvert \rho^{n-1} \sup_{m \ge k/n} \lvert b_m x^m \rvert$, while the row $n = 0$ has
  the single term $c_{0,0} = a_0$; so the double series
  can be summed in either order, over $n$ for each $k$ (a finite sum, giving the coefficients of $f \circ g$) or over
  $k$ for each $n$ (giving $a_n g(x)^n$).
- **Formal identities.** In $\mathbb{Q}[[X]]$, with $\exp(X) = \sum_{k \ge 0} X^k/k!$ and
  $\log(1 + X) = \sum_{k \ge 1} (-1)^{k+1} X^k/k$, one has $\exp(\log(1 + X)) = 1 + X$ and
  $\log(\exp(X)) = X$, the latter meaning $\log(1 + (\exp(X) - 1)) = X$. They are proved coefficientwise in
  $\mathbb{Q}[[X]]$ (formal derivatives, constant terms, and the invertibility of the linear coefficient for the
  inverse), not by the local constancy of $p$-adic functions with vanishing derivative, which fails in general.

The domains matter: convergence of the two series is not enough for a composition identity. In
$\mathbb{Q}_2$, $\log(-1)$ converges and equals $0$, while $\exp(0) = 1$; the identities hold on balls on
which the substitution conditions above are met, such as $\lvert x \rvert < p^{-1/(p-1)}$ for $\exp$ and
$\lvert x - 1 \rvert < p^{-1/(p-1)}$ for $\log$, for the absolute value extending the normalized one of $\mathbb{Q}_p$ (Conrad,
Theorem 8.13 and Example 8.14).

## Expansion

A good expansion has pages for the convergence criterion and rearrangements, for Cauchy products and the
evaluation of products of power series, for substitution, and for the two formal identities, each citing a
pinned source with locators besides those below.

It also writes out these steps of its own proof:

- the formal logarithmic derivative and the chain rule in $\mathbb{Q}[[X]]$, the coefficient recursion and the uniqueness of solutions of $F' = F$, $F(0) = 1$, for the formal identities.
- completeness and the summation of families tending to $0$ in any order (Conrad, §2, Theorems 2.5 and 2.9, Corollaries 2.10 and 2.11), for the convergence criterion, Cauchy products and substitution.

## Depends on

- [Exponential of a power series with zero constant coefficient](../../RingTheory/formal-power-series/exponential-of-multivariate-formal-power-series/exp-of-constant-coeff-zero.md), for the formal exponential
- [The logarithm series ln(1 + T)](../zeta-l-functions/multiple-zeta-values/q-analogues-of-multiple-zeta-values/part-05/log-one-add-series.md), for the formal logarithm over $\mathbb{Q}$
- [Nonarchimedean criterion for absolute values](absolute-values-on-fields/is-nonarchimedean-iff-nat-cast-le-one.md), for non-archimedean absolute values and the ultrametric inequality
- [Complete uniform space](../../Topology/uniform-spaces/complete-space.md), for the completeness of the field, for all the items
- [Ultrametric distance](../../Topology/metric-spaces/is-ultrametric-dist.md), for the non-archimedean absolute value as an ultrametric distance, for all the items

## Proof depends on

- [Partial derivative of the formal exponential](../../RingTheory/formal-power-series/exponential-of-multivariate-formal-power-series/pderiv-exp-of-constant-coeff-zero.md), for $(\exp w)' = w' \exp w$ in the formal identities

## Sources

- K. Conrad, "Infinite series in p-adic fields", expository notes,
  <https://kconrad.math.uconn.edu/blurbs/gradnumthy/infseriespadic.pdf>: §2 (for $K$ complete for a nontrivial
  non-archimedean absolute value: Theorem 2.5, rearrangements; Theorem 2.9 and Corollary 2.10, double series;
  Corollary 2.11, Cauchy products), §3, Theorem 3.1 (sums and products of power series at a point), and §8,
  Theorem 8.13 and Example 8.14, pp. 30–31 (the exponential and logarithm are inverse on
  $\{\lvert x \rvert < p^{-1/(p-1)}\}$; in $\mathbb{Q}_2$, $\log(-1) = 0$ and $e^{\log x} = -x$ for $x \equiv 3 \bmod 4$). For
  a general formal-to-numerical composition theorem Conrad refers to F. Q. Gouvêa, *p-adic Numbers*, 2nd ed.,
  pp. 99–101, and does not prove one.
- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: the proof of Lemma III.2.4 (the exponential and
  logarithm series on neighbourhoods of $0$ and $1$, mutually inverse there; the local application, not the
  general convergence and substitution statements above).
- J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020),
  <https://www.jmilne.org/math/CourseNotes/ANT.pdf>: Example 7.29 (convergence of $\exp$ on
  $\mathbb{Q}_p$).
