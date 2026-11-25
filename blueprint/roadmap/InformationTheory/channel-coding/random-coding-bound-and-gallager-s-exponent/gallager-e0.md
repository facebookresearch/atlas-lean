# Gallager's function $E_0(\rho, p)$

Let $W$ be a discrete memoryless channel with finite alphabets $\mathcal A$, $\mathcal B$ and let
$p$ be a law on the inputs. Gallager's function is

$$E_0(\rho, p) = -\ln \sum_{b \in \mathcal B} \Big(\sum_{a \in \mathcal A} p(a)\, W(b \mid a)^{1/(1+\rho)}\Big)^{1+\rho},$$

with the natural logarithm, so $E_0$ is in nats. It is the exponent of the
[random coding bound](random-coding-avg-error-le.md), where $0 \le \rho \le 1$. The definition is
meaningful for $\rho > -1$; at $\rho = -1$ the convention $1/0 = 0$ gives it a value with no
meaning, outside every range used here.

## Background

- [Gallager's inner sum](gallager-inner.md): the inner sum $g_b(\rho)$.
- [Mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md): $E_0$ vanishes at
  $\rho = 0$ and its slope there is the mutual information of $p$ and $W$ (in nats).

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, equation (20).
