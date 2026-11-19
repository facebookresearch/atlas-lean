# Chernoff bound for expander walks

There is an absolute constant $C > 0$ with the following property. Let $G$ be a simple graph on a finite nonempty set $V$ of $N$ vertices that is a [spectral expander](is-spectral-expander.md) of degree $d \ge 1$ with parameter $\lambda$, let $f : V \to [0, 1]$ have mean $\mu(f) = \frac1N \sum_v f(v)$, and let $V_0, \dots, V_t$ be a [random walk](walk-prob.md) with $t$ steps from a uniformly random start vertex. Then for every $\varepsilon > 0$,

$$\Pr\Big[\Big\lvert \frac{1}{t + 1} \sum_{i=0}^{t} f(V_i) - \mu(f) \Big\rvert \ge \lambda + \varepsilon\Big] \le 2 \exp\big(-C \varepsilon^2 (t + 1)\big)$$

(S. Vadhan, *Pseudorandomness* (2012), Theorem 4.22, $2 e^{-\Omega(\varepsilon^2 t)}$ for a walk $V_1, \dots, V_t$ of $t$ vertices; the bound is due to D. Gillman, SIAM J. Comput. 27 (1998)).

Unlike the hitting property, the approximation error here is $\lambda + \varepsilon$, so the bound is useful only when $\lambda$ is small, which powering the graph achieves. It gives randomness-efficient error reduction for two-sided-error (BPP) algorithms.

## Background

- [Hitting property of expander walks](hitting-property-of-expander-walks.md): the one-sided
  analogue.
- [Bounded-error probabilistic classes RP and BPP](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/README.md):
  the application to BPP error reduction.
