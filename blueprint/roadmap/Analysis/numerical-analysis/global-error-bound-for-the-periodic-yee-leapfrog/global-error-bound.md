# Global error bound expression for the periodic Yee scheme

For real $\rho, T, L, c, M_t, M_x, \Delta t, h, E_0$, the global error bound expression is the number

$$\sqrt{\frac{1 + \rho}{1 - \rho}}\,\left(E_0 + \frac{T \sqrt{L}\,\bigl(M_t\,\Delta t^2 + c\,M_x\,h^2\bigr)}{6}\right),$$

with real division by zero equal to $0$ and $\sqrt{y} = 0$ for $y < 0$. It is defined for all real arguments and is not by itself an error bound: at $\rho = 1$ the prefactor is $\sqrt{2/0} = 0$, so the expression is $0$ even when the initial mismatch $E_0$ is nonzero, while the error at [step zero](leapfrog-pair-error-zero.md) equals that mismatch.

It bounds the pair error of the periodic Yee leapfrog scheme under the hypotheses of the global error estimate: a nonempty grid of $N$ cells, spacings $h, \Delta t > 0$ and speed $c > 0$, period $L = N h$, a smooth periodic solution whose third time and space derivatives are bounded by $M_t, M_x \ge 0$, the Courant bound $c\,\Delta t / h \le \rho < 1$, a step $n$ with $n\,\Delta t \le T$, and $E_0$ the initial pair mismatch.
