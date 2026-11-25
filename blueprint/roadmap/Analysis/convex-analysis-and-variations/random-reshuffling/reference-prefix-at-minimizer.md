# Random reshuffling reference prefix at a minimizer

Use the finite-sum objective $f$, step size $\gamma$ and permutation
convention of the [epoch iteration](reshuffling-epoch-iteration.md). Fix a
global minimizer $x_\star$ of $f$, so $f(x_\star)\le f(x)$ for all
$x\in\mathbb R^d$. For the order $\pi_t$ of epoch $t$ and each integer
$0\le i\lt n$, the reference point after the first $i$ positions is

$$
x_{\star,t}^{i}
= x_\star-\gamma\sum_{0\le j\lt i}\nabla f_{\pi_t(j)}(x_\star).
$$

The empty sum is the zero vector, so $x_{\star,t}^{0}=x_\star$. Equation
(4) gives the nonempty proper prefixes $1\le i\le n-1$; when $n=1$ there
are none, and the only reference point here is the empty prefix.

The formula is deterministic for a given order. In a reshuffled epoch it
uses the same realized $\pi_t$ as the actual iterates, not a separate draw.
Every gradient in the reference sum is evaluated at $x_\star$, not at the
current inner iterate $x_t^j$ or the current reference point. The reference
prefix is therefore not defined by running the inner iteration from
$x_\star$, and it does not set the next epoch's iterate.

## Depends on

- [Random reshuffling epoch iteration](reshuffling-epoch-iteration.md) for the objective, step size and epoch order.
- [Gradient of a function on Euclidean coordinate space](../../../Probability/stochastic-calculus/fokker-planck-equation/grad.md) for the component gradients at the minimizer.

## Sources

- Konstantin Mishchenko, Ahmed Khaled and Peter Richtárik,
  [*Random Reshuffling: Simple Analysis with Vast Improvements*](https://arxiv.org/pdf/2006.05988v3#page=5),
  arXiv:2006.05988v3, §3.1, p. 5, equation (4), with the empty prefix
  included by convention.
