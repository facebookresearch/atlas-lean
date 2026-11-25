# Maximum mean discrepancy

Let $X$ be a measurable space and $H$ a real reproducing kernel Hilbert space of functions on $X$. For measures $P$ and $Q$ on $X$, the maximum mean discrepancy is

$$\mathrm{MMD}(P, Q) = \sup_{\|f\|_H \le 1} \Big(\int f \, dP - \int f \, dQ\Big),$$

with each integral read as $0$ when $f$ is not integrable and the supremum taken to be $0$ when the set of values is unbounded. When the feature map is Bochner integrable for both $P$ and $Q$, $\mathrm{MMD}(P, Q) = \|\mu_P - \mu_Q\|_H$, the distance between the mean embeddings.

## Idea

The MMD measures how differently two distributions integrate test functions, using the unit ball of $H$ as the test class. The choice of an RKHS makes the supremum explicit: $\int f \, dP - \int f \, dQ = \langle f, \mu_P - \mu_Q \rangle$, when both feature maps are Bochner integrable; by the Cauchy–Schwarz inequality it is maximised at $f = (\mu_P - \mu_Q)/\|\mu_P - \mu_Q\|$ when $\mu_P \ne \mu_Q$, and every test function gives $0$ when $\mu_P = \mu_Q$. Expanding the square gives a formula in the kernel alone, $\mathrm{MMD}(P, Q)^2 = \mathbb{E}\, k(x, x') - 2\, \mathbb{E}\, k(x, y) + \mathbb{E}\, k(y, y')$ for independent $x, x' \sim P$ and $y, y' \sim Q$, which samples can estimate. For probability measures with Bochner-integrable feature maps, the MMD is symmetric, vanishes on the diagonal and satisfies the triangle inequality; it separates probability measures exactly when the kernel is characteristic. It is the statistic of the kernel two-sample test.

## Statements

- [Maximum mean discrepancy over the unit ball of an RKHS](mmd.md)
- [The MMD is the distance between mean embeddings](mmd-eq-norm-sub.md): characterisation: distance between mean embeddings
- [The unit ball attains the norm of a vector](is-greatest-inner-closed-ball.md): lemma used for the characterisation
- [The MMD vanishes on the diagonal](mmd-self.md): basic property
- [Symmetry of the MMD](mmd-comm.md): basic property: symmetry
- [Triangle inequality for the MMD](mmd-le-add.md): basic property: triangle inequality
- [Population MMD in terms of the kernel](mmd-sq-eq.md): formula in terms of the kernel

## Background

- [Kernel mean embedding](../kernel-mean-embedding/README.md)

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*, Journal of Machine Learning Research (2012).
