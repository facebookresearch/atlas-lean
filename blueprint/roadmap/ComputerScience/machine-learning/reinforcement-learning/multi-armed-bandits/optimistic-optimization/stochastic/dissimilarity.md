# Dissimilarity

A *dissimilarity* on a set $\mathcal X$ is a function $\ell \colon \mathcal X \times \mathcal X \to [0, \infty)$ with
$\ell(x, x) = 0$ for every $x \in \mathcal X$. It need not be symmetric, vanish only on the diagonal, or satisfy the
triangle inequality. The *diameter* of a nonempty set $A \subseteq \mathcal X$ is
$\operatorname{diam}(A) = \sup_{x, y \in A} \ell(x, y)$, which may be $+\infty$, and the open *$\ell$-ball* of radius
$\varepsilon > 0$ centered at $x$ is

$$
B(x, \varepsilon) = \{y \in \mathcal X : \ell(x, y) < \varepsilon\};
$$

it contains $x$.

A [semi-metric](../semi-metric.md) is a dissimilarity, with the same balls.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 4.1, Definition 2.
