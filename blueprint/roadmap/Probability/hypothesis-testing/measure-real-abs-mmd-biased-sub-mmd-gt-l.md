# Large-deviation bound for the biased empirical MMD

Let $\mathcal{X}$ be a measurable space and $H$ a real reproducing kernel Hilbert space of functions on $\mathcal{X}$ whose feature map $x \mapsto k(x, \cdot)$ is strongly measurable and whose kernel satisfies $0 \le k(x, y) \le K$ for all $x, y$. Let $P, Q$ be probability measures on $\mathcal{X}$, let $m, n \ge 1$, and let $X = (x_1, \dots, x_m)$ be i.i.d. with law $P$ and $Y = (y_1, \dots, y_n)$ i.i.d. with law $Q$, independent of $X$ (that is, $(X, Y)$ has law $P^{\otimes m} \otimes Q^{\otimes n}$). Then for every $\varepsilon > 0$,

$$\Pr\Big\{\big|\mathrm{MMD}_b[X, Y] - \mathrm{MMD}[P, Q]\big| > 2\Big(\sqrt{K/m} + \sqrt{K/n}\Big) + \varepsilon\Big\} \le 2 \exp\Big(-\frac{\varepsilon^2 m n}{2K(m + n)}\Big).$$

When $K = 0$ the exponent is read as $0$ and the bound is $2$.

Here $\mathrm{MMD}_b$ is the distance between the empirical kernel mean embeddings and MMD the population maximum mean discrepancy over the unit ball of the RKHS. The bound is distribution-free: the deviation threshold does not depend on $P$ or $Q$. The paper uses it to show that its MMD tests are consistent against every fixed alternative, with Type II error decreasing at rate $O(m^{-1/2})$ when $m = n$ (Section 4.1, after Corollary 9); the level of the first test comes from the companion bound under $P = Q$ (Theorem 8).

## Informally uses

- [McDiarmid's inequality](../concentration-inequalities/mcdiarmid-s-inequality/README.md): the proof (Appendix A.2) applies it to the uniform deviation, whose bounded differences are $2\sqrt{K}/m$ and $2\sqrt{K}/n$.
- [Rademacher average of a ball of linear predictors](../../ComputerScience/machine-learning/generalization-bounds-and-concentration/rademacher-average-linear-ball-le.md): after symmetrisation, the proof bounds the Rademacher averages of the unit ball of the RKHS by $\sqrt{K/m}$ and $\sqrt{K/n}$, the kernel case of this bound.

## Background

- [Kernel mean embeddings and maximum mean discrepancy](../convergence-of-measures/kernel-mean-embeddings-and-maximum-mean-discrepa/README.md): the definitions of $\mathrm{MMD}$ and $\mathrm{MMD}_b$ and the identity $\mathrm{MMD}_b = \|\mu_X - \mu_Y\|$.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*, J. Mach. Learn. Res. 13 (2012), 723–773, Theorem 7.
