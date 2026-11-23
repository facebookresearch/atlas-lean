# Dirichlet form of a sub-Markovian generator on a finite set

Let $S$ be a finite set, $m : S \to \mathbb{R}$ a weight and $Q$ a real $S \times S$ matrix, with
[killing rate](killing-rate.md) $k(x) = -\sum_y Q(x, y)$. For $f, g : S \to \mathbb{R}$ define

$$\mathcal E(f, g) = \frac{1}{2} \sum_{x, y} m(x) Q(x, y) \bigl(f(x) - f(y)\bigr)\bigl(g(x) - g(y)\bigr) + \sum_x m(x) k(x) f(x) g(x),$$

which is equation (1.2.27) of Fukushima, Oshima and Takeda on a finite set. The diagonal entries
of $Q$ contribute only through $k$. Fukushima, Oshima and Takeda assume $m$ symmetrising,
$m(x) Q(x, y) = m(y) Q(y, x)$ (their (1.2.26)); the formula makes sense for every $(m, Q)$, and
without detailed balance it is the form of the $m$-symmetrised generator (the Markov property
below does not need detailed balance).

On a finite set every bilinear form is closed. When $m > 0$, the off-diagonal entries of $Q$ are
nonnegative and $k \ge 0$, the form is a Dirichlet form on $\ell^2(m)$ (see
[the Markov property](form-unit-contraction-le.md)). Strictly positive weights are needed for
this reading: with a zero weight, functions that agree wherever $m > 0$ are the same element of
$\ell^2(m)$ but can have different energies (for $m = (1, 0)$ and
$Q = \begin{pmatrix} -1 & 1 \\ 0 & 0 \end{pmatrix}$, the functions $0$ and $(0, 1)$ have energies
$0$ and $\frac12$). A [rate matrix](../finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md) is the conservative case
$k = 0$.

## Background

- [Detailed balance](../finite-continuous-time-markov-chains/stationarity-and-detailed-balance-for-finite-con/is-detailed-balance.md): the reversibility condition $m(x) Q(x,y) = m(y) Q(y,x)$ under which
  $\mathcal E(f, g) = -\langle f, Q g \rangle_m$ ([the generator form](form-eq-neg-sum-mul-mul-vec.md)).
- [The Dirichlet form of a reversible matrix](../mixing-times-of-markov-chains/sum-mul-sub-mul-vec-eq.md): Sinclair's identity
  $\sum \pi g (g - P g) = \tfrac12 \sum \pi(x) P(x,y) (g(x) - g(y))^2$, the kernel case $Q = P - 1$ of
  this form ([bridge](form-sub-one-self-eq-sum-mul-sub-mul-vec.md)).
- [Laplacian Rayleigh quotient of a spectral expander](../../../GraphTheory/graph-families-and-operations/expander-graphs/laplacian-rayleigh-quotient.md): for a graph with adjacency matrix $A$,
  degree matrix $D$ and Laplacian $L = D - A$, the generator $Q = A - D = -L$ with $m = 1$ gives
  the quadratic form $f^\top L f$ of the graph Laplacian.

## Sources

- M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd revised and extended ed., de Gruyter Studies in Mathematics 19, de Gruyter, 2011, Example 1.2.5, equations (1.2.26) and (1.2.27).
