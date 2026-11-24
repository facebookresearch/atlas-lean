# Kimura's loss probability, process form

Let $\sigma$ and $x$ be real, $\mu$ a probability measure on $\Omega$, $(\mathcal{F}_t)_{t \ge 0}$ a
filtration and $(X_t)_{t \ge 0}$ a
[solution of the Wright–Fisher martingale problem](is-wright-fisher-solution.md) with selection
coefficient $\sigma$ with respect to $(\mathcal{F}_t)$ and $\mu$, with $X_0 = x$ almost surely. Then
the probability that the allele is eventually lost is

$$\mu(\exists t_0,\ \forall t \ge t_0,\ X_t = 0) = 1 - u_\sigma(x),$$

where $u_\sigma$ is [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md):
$u_\sigma(x) = (1 - e^{-2\sigma x}) / (1 - e^{-2\sigma})$ for $\sigma \ne 0$ and $u_0(x) = x$. Since
$X$ takes values in $[0, 1]$, $x$ lies in $[0, 1]$. The loss probability of $X$ is the
[fixation probability](measure-real-fixation.md) of the reflected process $1 - X$, which
[solves the martingale problem with $-\sigma$](one-sub.md) and starts at $1 - x$; Kimura's
symmetry $u_{-\sigma}(1 - x) = 1 - u_\sigma(x)$
([fixation probability under a change of sign](../selection-and-dominance-in-kimura-s-fixation-pro/kimura-fixation-neg.md))
gives the formula.

## Sources

- M. Kimura, *On the probability of fixation of mutant genes in a population*, Genetics 47 (1962),
  713–719.
- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer
  (2004), ch. 4.
