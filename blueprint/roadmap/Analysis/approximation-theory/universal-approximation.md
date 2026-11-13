# Universal approximation theorem

Let $n$ be a natural number, let $\mathbb{R}^n$ carry its
standard inner product $\langle \cdot, \cdot \rangle$, let $K \subseteq \mathbb{R}^n$ be compact,
and let $\sigma : \mathbb{R} \to \mathbb{R}$ be continuous and not a polynomial, that is, there is
no real polynomial $p$ with $\sigma(x) = p(x)$ for all real $x$. Then for every function
$f : \mathbb{R}^n \to \mathbb{R}$ that is continuous on $K$ and every $\varepsilon > 0$ there exist
$m \in \mathbb{N}$, real numbers $c_1, \dots, c_m$ and $b_1, \dots, b_m$, and vectors
$w_1, \dots, w_m \in \mathbb{R}^n$ such that
$\left| f(x) - \sum_{i=1}^{m} c_i \, \sigma(\langle w_i, x \rangle + b_i) \right| < \varepsilon$
for every $x \in K$.

In words: single-hidden-layer feedforward networks with a continuous, non-polynomial activation
approximate every continuous function uniformly on every compact set.

## Sources

- `universal-approximation-s1` from https://en.wikipedia.org/wiki/Universal_approximation_theorem; the continuous-activation case of M. Leshno, V. Ya. Lin, A. Pinkus and S. Schocken, *Multilayer feedforward networks with a nonpolynomial activation function can approximate any function*, Neural Networks 6(6) (1993), 861–867, doi:10.1016/S0893-6080(05)80131-5, which allows any locally bounded, piecewise continuous activation that is not almost everywhere equal to a polynomial; for continuous activations this is the same as the pointwise non-polynomial hypothesis.
