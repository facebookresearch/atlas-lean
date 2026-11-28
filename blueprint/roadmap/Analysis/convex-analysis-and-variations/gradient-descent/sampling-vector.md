# Sampling vector

Let $n \ge 1$ and let $v=(v_1,\ldots,v_n)$ be a real random vector with law
$\mathcal D$ on $\mathbb R^n$. It is a **sampling vector** if each coordinate
is integrable and has mean one: for every $i=1,\ldots,n$,

$$
\mathbb E_{\mathcal D}|v_i| < \infty,
\qquad \mathbb E_{\mathcal D}[v_i] = 1.
$$

The expectations are with respect to the joint law $\mathcal D$. The
coordinates need not be nonnegative or independent, and their sum need not
be $n$ on each draw. This is a first-moment condition; it does not require
finite second moments.

## Depends on

- [Probability measure](../../../Probability/foundations/probability-measures/is-probability-measure.md)
- [Law of a random element](../../../Probability/foundations/probability-measures/probability-measure-map.md)
- [Expected value of a random variable](../../../Probability/foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Sources

- R. M. Gower, N. Loizou, X. Qian, A. Sailanbayev, E. Shulgin, and
  P. Richtárik, [*SGD: General Analysis and Improved Rates*](https://arxiv.org/html/1901.09401v4),
  arXiv:1901.09401v4, Section 1.2, Definition 1.1 and equation (3).
