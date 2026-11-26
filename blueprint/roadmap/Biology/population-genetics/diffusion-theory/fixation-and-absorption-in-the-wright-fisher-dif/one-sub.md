# Reflecting a Wright–Fisher solution negates the selection coefficient

Let $\sigma$ be real, $\mu$ a measure on $\Omega$ and $(\mathcal{F}_t)_{t \ge 0}$ a filtration. If
$(X_t)_{t \ge 0}$ solves the
[martingale problem for the Wright–Fisher diffusion](is-wright-fisher-solution.md) with selection
coefficient $\sigma$ with respect to $(\mathcal{F}_t)$ and $\mu$, then $(1 - X_t)_{t \ge 0}$, the
frequency of the other allele, solves it with selection coefficient $-\sigma$, with respect to the
same filtration and the same measure.

The [generator identity](generator-neg-one-sub.md) $(L_{-\sigma} f)(1 - y) = (L_\sigma g)(y)$ with
$g(z) = f(1 - z)$, which is twice continuously differentiable when $f$ is, turns the martingales
required of $1 - X$ into martingales of $X$. Only the solution property is transported: no new
process is constructed and no uniqueness in law is claimed. For $\sigma = 0$ this is the
[neutral case](../absorption-of-the-neutral-wright-fisher-martinga/is-wright-fisher-solution-one-sub.md).

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer
  (2004), ch. 4.
