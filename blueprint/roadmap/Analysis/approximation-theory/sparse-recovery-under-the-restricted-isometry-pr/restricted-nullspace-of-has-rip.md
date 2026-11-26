# Restricted isometry implies the restricted nullspace property

Let $\iota$ be a finite index set, $s \ge 1$, and $\Phi \in \mathbb{R}^{m \times \iota}$ with the
[restricted isometry property](has-rip.md) of order $2s$ with a constant $\delta < \sqrt{2} - 1$
(that is, $\delta_{2s} < \sqrt{2} - 1$). Then $\Phi$ has the [restricted nullspace property](../../../Probability/linear-models-multivariate/exact-recovery-by-basis-pursuit/restricted-nullspace.md) over
every set $S$ of at most $s$ indices: the only $h$ with $\Phi h = 0$ and
$\|h_{S^c}\|_1 \le \|h_S\|_1$ is $h = 0$. Indeed $\delta < \sqrt{2} - 1$ is equivalent to
$\rho = \sqrt{2}\,\delta / (1 - \delta) < 1$.

## Informally uses

- [The null-space property under restricted isometry](sum-abs-le-of-mul-vec-eq-zero.md): with $\rho < 1$, a kernel vector in the cone $\|h_{S^c}\|_1 \le \|h_S\|_1$ satisfies $\|h_{S^c}\|_1 \le \rho \|h_{S^c}\|_1$, so it vanishes.

## Sources

- E. J. Candès, *The restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, Lemma 2.2 with $\rho < 1$
