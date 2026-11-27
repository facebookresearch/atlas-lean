# Spectral gap of a finite Markov kernel, in Dirichlet-form terms

Let $S$ be a finite set and $P$ a real $S \times S$ matrix, with [Dirichlet form](form-sub-one.md)
$\mathcal E_{\pi, P - I}(f, f) = \frac{1}{2} \sum_{x, y} \pi(x) P(x, y) (f(x) - f(y))^2$ when the rows
of $P$ sum to $1$ (in general the [form](form.md) of the generator $P - I$), and let
$\operatorname{Var}_\pi$ be the [variance](weighted-variance.md).
For a probability vector $\pi$ on a finite state space (here $S$: $\pi \ge 0$, $\sum_x \pi(x) = 1$),

$$\lambda(P, \pi) = \inf \Bigl\{ \frac{\mathcal E_{\pi, P - I}(f, f)}{\operatorname{Var}_\pi(f)} : f : S \to \mathbb{R},\ \operatorname{Var}_\pi(f) \ne 0 \Bigr\},$$

the infimum being read as $0$ when the set is empty (one-point spaces) or unbounded below.

When $P$ is stochastic ($P \ge 0$ with rows summing to $1$) and some function has nonzero variance,
the spectral gap is the largest constant $c$ in the Poincaré inequality $c \operatorname{Var}_\pi(f) \le \mathcal E(f, f)$ ([statement](spectral-gap-mul-weighted-variance-le.md),
[optimality](le-spectral-gap.md)); when every function has zero variance (for instance on a one-point space) the infimum is over
the empty set and equals $0$.
For an irreducible chain on at least two states, reversible with respect to $\pi > 0$, it is the second
smallest eigenvalue of $I - P$.

## Background

- [A Poincaré inequality bounds the spectral gap](../canonical-paths-and-multicommodity-flow/one-le-mul-one-sub-of-poincare.md): Sinclair's eigenvalue form of the same
  inequality; [Sinclair's Poincaré hypothesis is a lower bound on the spectral gap](inv-le-spectral-gap-iff-poincare.md)
  identifies his hypothesis with $1/B \le \lambda$.
- [Random walks on finite groups](../../random-walks/random-walks-on-finite-groups/README.md): Diaconis's walks, whose spectral gaps are read off
  representation theory and bound mixing through the same Poincaré inequality.

## Sources

- P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite Markov chains*, Annals of Applied Probability 6 (1996), 695–750, equation (1.4).
