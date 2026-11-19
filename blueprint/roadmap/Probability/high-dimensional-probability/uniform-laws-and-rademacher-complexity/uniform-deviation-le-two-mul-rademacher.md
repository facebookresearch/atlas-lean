# Uniform law via Rademacher complexity

Let $\mathcal{F}$ be a countable class of measurable functions with $|f| \le b$ for some
$b > 0$. For every $n \ge 1$ and $\delta \ge 0$, with probability at least
$1 - e^{-n\delta^2/(2b^2)}$ over $n$ independent samples from a probability measure $P$,

$$\|P_n - P\|_{\mathcal{F}} \le 2\, \mathcal{R}_n(\mathcal{F}) + \delta.$$

In particular, if $\mathcal{R}_n(\mathcal{F}) \to 0$ then $\mathcal{F}$ is a Glivenko–Cantelli
class.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §4.2 (a uniform law via Rademacher complexity).

## Informally uses

- [Symmetrization bound](integral-uniform-deviation-le-two-mul-ra.md): the bound in expectation.
- [McDiarmid's inequality](../../concentration-inequalities/mcdiarmid-s-inequality/README.md): concentrates $\|P_n - P\|_{\mathcal{F}}$ around its mean, with bounded differences $2b/n$.

## Background

- [Concentration of the uniform deviation](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/bounded-differences-uniform-deviation.md): the same bounded-differences step for losses, in machine learning.
