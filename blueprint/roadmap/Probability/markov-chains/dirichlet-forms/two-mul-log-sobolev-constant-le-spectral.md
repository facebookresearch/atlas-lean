# The log-Sobolev constant is at most half the spectral gap

Let $S$ be a finite set, $\pi$ a probability vector on $S$ with $\pi(x) > 0$ for every $x$, and $P$
a real $S \times S$ matrix with nonnegative entries and rows summing to $1$. Then

$$2\, \alpha(P, \pi) \le \lambda(P, \pi),$$

where $\alpha$ is the [log-Sobolev constant](log-sobolev-constant.md) and $\lambda$ the [spectral
gap](spectral-gap.md). Diaconis and Saloff-Coste prove this (Lemma 3.1) by expanding
$\mathcal L(1 + \varepsilon g)$ to second order, and state it for irreducible chains with
stationary $\pi$; neither irreducibility nor stationarity is needed. For a non-stationary $\pi$ the
constants are those of the symmetric form $\frac{1}{2} \sum_{x, y} \pi(x) P(x, y) (f(x) - f(y))^2$,
which equals Diaconis and Saloff-Coste's $\langle (I - P) f, f \rangle_\pi$ only when $\pi$ is
stationary. On a one-point space both constants are $0$.

## Background

- [Spectral gap of a finite Markov kernel](spectral-gap.md) and
  [log-Sobolev constant](log-sobolev-constant.md): the two variational constants compared.
- [Logarithmic Sobolev inequality](../../concentration-inequalities/transport-cost-inequalities/satisfies-log-sobolev.md):
  in the diffusion setting the analogous comparison is that a log-Sobolev inequality implies a
  Poincaré inequality.

## Sources

- P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite Markov chains*, Annals of Applied Probability 6 (1996), 695–750, Lemma 3.1.
