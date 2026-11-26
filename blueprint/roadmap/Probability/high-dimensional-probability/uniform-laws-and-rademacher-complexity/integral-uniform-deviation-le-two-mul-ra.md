# Symmetrization bound

For a countable class $\mathcal{F}$ of measurable functions bounded by $b$ and $n \ge 1$
independent samples from a probability measure $P$,

$$\mathbb{E}\big[\|P_n - P\|_{\mathcal{F}}\big] \le 2\, \mathcal{R}_n(\mathcal{F}).$$

The source states the bound $\mathbb{E}[\Phi(\|P_n - P\|_{\mathcal{F}})] \le
\mathbb{E}[\Phi(2\|S_n\|_{\mathcal{F}})]$ for every convex nondecreasing $\Phi$; this is the case
$\Phi(t) = t$. Countability makes the suprema measurable.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §4.2 (a uniform law via Rademacher complexity), the symmetrization step.

## Background

- [Uniform deviation of empirical means](uniform-deviation.md) and [Rademacher complexity](rademacher-complexity.md): the two quantities compared.
