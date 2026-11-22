# Smoothness of compactly supported parameter integrals

Let $X$ be a second-countable topological space whose $\sigma$-algebra contains the open sets, and
$\mu$ a measure on $X$ finite on compact sets. Let $M$ and $P$ be real normed spaces, $E$ a real
Banach space, $c : X \to M$ continuous, $w : X \to \mathbb{R}$ continuous with compact support and
$\Psi : M \times P \to E$ smooth with compact support. Then
$p \mapsto \int_X w(x)\, \Psi(c(x), p)\, d\mu(x)$ is smooth on $P$.

## Idea

Differentiating under the integral sign is allowed when the derivatives of the integrand in the
parameter have an integrable dominating function; then each derivative of the integral is the
integral of the derivative. Here every derivative of $\Psi$ is bounded, since $\Psi$ has compact
support, so all parameter derivatives of the integrand are bounded by multiples of $|w|$, which is
integrable because $w$ is continuous with compact support and $\mu$ is finite on compact sets.

## Statements

- [Smoothness of compactly supported parameter integrals](cont-diff-integral-smul-comp-of-cont-dif.md)
