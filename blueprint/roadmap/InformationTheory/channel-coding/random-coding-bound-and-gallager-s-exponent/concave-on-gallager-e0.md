# Concavity of $E_0$ in $\rho$

For every discrete memoryless channel $W$ on finite alphabets and every input law $p$, the function
$\rho \mapsto E_0(\rho, p)$ is concave on $(-1, \infty)$.

Gallager's equation (30) states $\partial^2 E_0 / \partial \rho^2 \le 0$ for $\rho \ge 0$ (assuming
$I(\mathbf p) \ne 0$), with a characterisation of equality, and proves it with Hölder's inequality
in his appendix. This is stronger in its range and hypotheses (the interval
$(-1, \infty)$, no differentiability, no assumption on $I(\mathbf p)$) and omits the equality case.

The proof follows the same route. For $\rho = a \rho_1 + b \rho_2$ ($a + b = 1$, $a, b > 0$) put
$\mu = a(1 + \rho_1)/(1 + \rho)$. Hölder over the inputs gives
$g_y(\rho) \le g_y(\rho_1)^{\mu} g_y(\rho_2)^{1-\mu}$, hence
$g_y(\rho)^{1+\rho} \le (g_y(\rho_1)^{1+\rho_1})^{a} (g_y(\rho_2)^{1+\rho_2})^{b}$, and Hölder over the
outputs bounds the sum by the product of the two sums to the powers $a$ and $b$. Taking $-\ln$ gives
$E_0(\rho) \ge a E_0(\rho_1) + b E_0(\rho_2)$.

## Informally uses

- [Hölder's inequality, geometric-mean form](sum-rpow-mul-rpow-le.md): used twice, over the inputs
  and over the outputs.
- [The sum inside $E_0$ is positive](sum-gallager-inner-rpow-pos.md): the logarithms are of
  positive numbers.

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Theorem 2, equation (30), proved in the Appendix.
