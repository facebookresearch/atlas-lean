# Positive random coding exponent below the mutual information

Let $W$ be a discrete memoryless channel on finite alphabets and $p$ an input law. If a rate $R$
(in nats per channel use) is smaller than the mutual information $I(X; Y) \ln 2$ of $p$ and $W$
in nats, then there is $0 < \rho \le 1$ with

$$E_0(\rho, p) - \rho R > 0.$$

So the exponent $\max_{0 \le \rho \le 1} (E_0(\rho, p) - \rho R)$ of the random coding bound is
positive at every rate below $I(p; W)$. The function $\rho \mapsto E_0(\rho, p) - \rho R$ vanishes at
$0$ and has positive slope $I(p; W) - R$ there, so it is positive just to the right of $0$.
Gallager reaches the same conclusion through the parametric form of $E(R, \mathbf p)$, which also
uses the concavity (30).

## Informally uses

- [$E_0$ vanishes at $\rho = 0$](gallager-e0-zero.md)
- [Derivative of $E_0$ at $\rho = 0$ is the mutual information](has-deriv-at-gallager-e0-zero.md)

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Section III, discussion after equation (36): $E(R, \mathbf p) > 0$ for
  $R < I(\mathbf p)$.
