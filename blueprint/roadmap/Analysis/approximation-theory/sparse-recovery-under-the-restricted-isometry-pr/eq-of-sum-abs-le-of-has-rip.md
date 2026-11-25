# Exact recovery of sparse vectors by $\ell_1$ minimization

Let $\iota$ be a finite index set, $s \ge 1$, and $\Phi \in \mathbb{R}^{m \times \iota}$ with the
[restricted isometry property](has-rip.md) of order $2s$ with a constant $\delta < \sqrt{2} - 1$.
If $x \in \mathbb{R}^\iota$ has at most $s$ nonzero entries, then every $\hat x$ with
$\Phi \hat x = \Phi x$ and $\|\hat x\|_1 \le \|x\|_1$ equals $x$; so $x$ is the unique solution of
$\min \{\|\tilde x\|_1 : \Phi \tilde x = \Phi x\}$.

In the source this is the case $x = x_s$ of the error bound (4) of Theorem 1.2. It also follows by
combining the two results below.

## Background

- [Restricted isometry implies the restricted nullspace property](restricted-nullspace-of-has-rip.md): the hypothesis $\delta_{2s} < \sqrt{2} - 1$ gives the restricted nullspace property over the support of $x$.
- [Exact recovery by basis pursuit](../../../Probability/linear-models-multivariate/exact-recovery-by-basis-pursuit/basis-pursuit-unique-iff-restricted-null.md): the restricted nullspace property is equivalent to exact recovery of every vector with that support.
- [Noiseless recovery, $\ell_1$ error](sum-abs-sub-le-of-has-rip.md): the source's route, the stable bound (4) applied to an $s$-sparse $x$.

## Sources

- E. J. Candès, *The restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, Theorem 1.2, last sentence: "if $x$ is $s$-sparse, the recovery is exact"
