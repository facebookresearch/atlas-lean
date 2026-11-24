# Power series identities over complete non-archimedean fields

This node is still to be broken down. It covers the evaluation of power series identities at points of
a complete non-archimedean field, which the page on
[the p-adic exponential](p-adic-exponential.md) applies on the balls $\mathfrak{m}_K^r$ and
$1 + \mathfrak{m}_K^r$. Let $K$ be a field complete for a non-archimedean absolute value.

- **Series.** A series $\sum_n a_n$ in $K$ converges if and only if $a_n \to 0$, and then every
  rearrangement converges to the same sum, as does every partition of the terms into finitely or
  infinitely many convergent subseries.
- **Products.** If $\sum_n a_n$ and $\sum_n b_n$ converge, their Cauchy product
  $\sum_n \sum_{i + j = n} a_i b_j$ converges to the product of the sums. Hence, for power series
  $f, g \in K[[X]]$ converging at $x \in K$, the product $fg$ converges at $x$ and $(fg)(x) = f(x)g(x)$;
  the same holds in several variables, for the double series of $f(X)g(Y)$ at $(x, y)$.
- **Substitution.** Let $f = \sum_n a_n X^n$ and $g = \sum_{m \ge 1} b_m X^m$ in $K[[X]]$, and $x \in K$
  with $b_m x^m \to 0$ and $\lvert a_n \rvert \rho^n \to 0$ for $\rho = \sup_m \lvert b_m x^m \rvert$. Then
  $f \circ g$ converges at $x$ and $(f \circ g)(x) = f(g(x))$.
- **Formal identities.** In $\mathbb{Q}[[X]]$, with $\exp(X) = \sum_{k \ge 0} X^k/k!$ and
  $\log(1 + X) = \sum_{k \ge 1} (-1)^{k+1} X^k/k$, one has $\exp(\log(1 + X)) = 1 + X$ and
  $\log(\exp(X)) = X$, the latter meaning $\log(1 + (\exp(X) - 1)) = X$.

The domains matter: convergence of the two series is not enough for a composition identity. In
$\mathbb{Q}_2$, $\log(-1)$ converges and equals $0$, while $\exp(0) = 1$; the identities hold on balls on
which the substitution conditions above are met.

A good expansion has pages for the convergence criterion and rearrangements, for Cauchy products and the
evaluation of products of power series, for substitution, and for the two formal identities, each citing a
pinned source with locators besides those below.

## Depends on

- [Exponential of a power series with zero constant coefficient](../../RingTheory/formal-power-series/exponential-of-multivariate-formal-power-series/exp-of-constant-coeff-zero.md), for the formal exponential
- Not yet a page: fields complete for a non-archimedean absolute value, for all the items

## Proof depends on

- Not yet a page: the formal derivative and the uniqueness of solutions of $F' = F$, $F(0) = 1$ in $\mathbb{Q}[[X]]$, for the formal identities
- Not yet a page: the ultrametric inequality and completeness, for the convergence criterion, Cauchy products and substitution

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: the proof of Lemma III.2.4 (the exponential and
  logarithm series on neighbourhoods of $0$ and $1$, mutually inverse there).
- J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020),
  <https://www.jmilne.org/math/CourseNotes/ANT.pdf>: Example 7.29 (convergence of $\exp$ on
  $\mathbb{Q}_p$).
