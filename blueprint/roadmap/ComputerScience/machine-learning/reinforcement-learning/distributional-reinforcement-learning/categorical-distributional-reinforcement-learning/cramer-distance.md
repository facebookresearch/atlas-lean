# Cramér distance

The Cramér distance between two laws on the real line is the $L^2$ distance between their cumulative distribution functions. Its maximum over state–action pairs is the metric in which projected categorical operators contract.

For a Borel probability measure $\nu$ on $\mathbb{R}$ let $F_\nu(t) = \nu((-\infty, t])$ be its cumulative distribution function (Mathlib's `ProbabilityTheory.cdf`). The Cramér distance is

$$\ell_2(\nu_1, \nu_2) = \Bigl( \int_{\mathbb{R}} \bigl(F_{\nu_1}(t) - F_{\nu_2}(t)\bigr)^2 \, dt \Bigr)^{1/2} \in [0, \infty],$$

and for [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md) the supremum Cramér metric is

$$\bar \ell_2(\eta, \mu) = \max_{(x,a) \in \mathcal{X} \times \mathcal{A}} \ell_2\bigl(\eta^{(x,a)}, \mu^{(x,a)}\bigr).$$

$\ell_2$ is an extended metric on Borel probability measures on $\mathbb{R}$, and $\bar \ell_2$ one on $\mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$. They are finite on laws with finite first moments, where $\ell_2^2(\nu_1, \nu_2) \le \int |t| \, \nu_1(dt) + \int |t| \, \nu_2(dt)$, and on laws supported in a common interval $[c, d]$, where $\ell_2^2 \le d - c$. Only differences of distribution functions are square integrable: a single $F_\nu$ never is, since it tends to $1$.

## Depends on

- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)

## Proof depends on

None.

## Expansion

Symmetry is clear, and the triangle inequality is Minkowski's inequality in $L^2(\mathbb{R})$ applied to differences of distribution functions. If $\ell_2(\nu_1, \nu_2) = 0$ then $F_{\nu_1} = F_{\nu_2}$ almost everywhere, hence everywhere by right continuity, and a distribution function determines its Borel probability measure. Since $|F_{\nu_1} - F_{\nu_2}| \le 1$, $\ell_2^2 \le \int |F_{\nu_1} - F_{\nu_2}|$. On $(-\infty, 0)$ this is at most $\int_{-\infty}^0 (F_{\nu_1} + F_{\nu_2})$, and on $[0, \infty)$ at most $\int_0^\infty ((1 - F_{\nu_1}) + (1 - F_{\nu_2}))$; together these equal the sum of the first absolute moments. If both laws live in $[c, d]$, the integrand vanishes outside $[c, d)$ and is at most $1$. Rowland and coauthors define $\ell_2$ on all of $\mathscr{P}(\mathbb{R})$ without remarking that it can be infinite.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.1, Definition 3; Appendix C, proof of Proposition 1 (the inner product of distribution-function differences).
