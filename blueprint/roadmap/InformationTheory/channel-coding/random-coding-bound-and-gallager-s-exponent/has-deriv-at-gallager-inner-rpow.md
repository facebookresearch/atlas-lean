# Derivative of one summand of $E_0$ at $\rho = 0$

Fix an output $b$ and write $q(b) = \sum_a p(a) W(b \mid a)$. The function
$\rho \mapsto g_b(\rho)^{1+\rho}$ has derivative

$$q(b) \ln q(b) - \sum_a p(a)\, W(b \mid a) \ln W(b \mid a)$$

at $\rho = 0$. If $q(b) > 0$ this follows from the derivative of $f^g$ with $f(0) = q(b) > 0$. If
$q(b) = 0$, every term $p(a) W(b \mid a)$ vanishes, so $g_b(\rho) = 0$ for all $\rho > -1$, and
both the derivative and the displayed value are $0$.

## Informally uses

- [Derivative of $w^{1/(1+\rho)}$ at $\rho = 0$](has-deriv-at-rpow-one-div-one-add.md): termwise
  derivative of the inner sum, $g_b'(0) = -\sum_a p(a) W(b \mid a) \ln W(b \mid a)$.
- [Gallager's inner sum at $\rho = 0$](gallager-inner-zero.md): $g_b(0) = q(b)$.
