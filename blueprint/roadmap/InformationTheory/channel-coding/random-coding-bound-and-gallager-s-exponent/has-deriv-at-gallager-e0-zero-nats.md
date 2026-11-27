# Derivative of $E_0$ at $\rho = 0$, explicit form

For every discrete memoryless channel $W$ on finite alphabets and every input law $p$, the
function $\rho \mapsto E_0(\rho, p)$ is differentiable at $\rho = 0$ with derivative

$$\sum_{a, b} p(a)\, W(b \mid a) \ln W(b \mid a) - \sum_b q(b) \ln q(b), \qquad q(b) = \sum_a p(a) W(b \mid a).$$

This is the mutual information of the input and output in nats, written as
$H(Y) - H(Y \mid X)$; [the next result](has-deriv-at-gallager-e0-zero.md) identifies it with the
mutual information in bits, times $\ln 2$.

## Informally uses

- [Derivative of one summand of $E_0$ at $\rho = 0$](has-deriv-at-gallager-inner-rpow.md):
  differentiate the sum over $b$ term by term.
- [$E_0$ vanishes at $\rho = 0$](gallager-e0-zero.md): the sum inside the logarithm is $1$ at
  $\rho = 0$, so the derivative of $-\ln$ of it is minus its derivative.

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Theorem 2, equation (29).
