# Consistency bound expression for the periodic Yee scheme

For real $L, \Delta t, c, M_t, M_x, h$, the consistency bound expression is

$$\eta = \frac{\sqrt{L}\,\Delta t\,\bigl(M_t\,\Delta t^2 + c\,M_x\,h^2\bigr)}{24},$$

with $\sqrt{L} = 0$ for $L < 0$. It is defined for all real arguments and can be negative, for example for $\Delta t < 0$ or $M_t, M_x < 0$. It bounds the one-step residuals of the scheme only for admissible data: positive spacings and speed, a smooth periodic solution of period $L > 0$, and nonnegative third-derivative bounds $M_t, M_x$.
