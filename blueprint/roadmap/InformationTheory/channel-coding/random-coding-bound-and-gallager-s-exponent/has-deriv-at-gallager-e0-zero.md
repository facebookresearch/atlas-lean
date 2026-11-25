# Derivative of $E_0$ at $\rho = 0$ is the mutual information

For every discrete memoryless channel $W$ on finite alphabets and every input law $p$,

$$\frac{\partial E_0(\rho, p)}{\partial \rho}\Big|_{\rho = 0} = I(X; Y) \cdot \ln 2,$$

where $(X, Y)$ has the joint law $p(a) W(b \mid a)$ and $I(X; Y)$ is the
[mutual information](../../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md) in bits. The factor $\ln 2$ converts bits to
nats: $E_0$ is defined with the natural logarithm, so its slope is the mutual information in nats,
which is Gallager's $I(\mathbf p)$.

Gallager states this in Theorem 2 under the assumption $I(\mathbf p) \ne 0$, which he needs for the
strict inequalities (27) and (28); this statement holds without it.

## Informally uses

- [Derivative of $E_0$ at $\rho = 0$, explicit form](has-deriv-at-gallager-e0-zero-nats.md): the
  derivative as $\sum p W \ln W - \sum q \ln q$.
- [Mutual information as a difference of entropies](../../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information-eq.md):
  $I(X; Y) = H(X) + H(Y) - H(X, Y)$ in bits, expanded with $-xy \ln(xy) = -y\, x \ln x - x\, y \ln y$.

## Background

- [Shannon entropy](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md):
  the entropies in that expansion.

- [Kullback–Leibler divergence on a finite space](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md):
  the mutual information is the divergence of the joint law from the product of its marginals.

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Theorem 2, equation (29).
