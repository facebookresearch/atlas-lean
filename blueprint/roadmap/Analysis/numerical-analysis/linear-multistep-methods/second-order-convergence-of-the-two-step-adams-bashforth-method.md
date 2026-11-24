# Second-order convergence of the two-step Adams-Bashforth method

This node covers the convergence of the simplest explicit multistep method. Let $f : [0, T] \times \mathbb{R}^d \to \mathbb{R}^d$ be continuous
and Lipschitz in its second argument, and let the solution $y$ of $y' = f(t, y)$, $y(0) = y_0$, be three times continuously differentiable on
$[0, T]$. For a step $h = T/N$ define

$$y_{n+2} = y_{n+1} + h\Big(\tfrac32 f(t_{n+1}, y_{n+1}) - \tfrac12 f(t_n, y_n)\Big), \qquad t_n = nh .$$

If the numerical starting values satisfy $|y_0 - y(0)| + |y_1 - y(h)| \le Kh^2$, then
$\max_{0 \le n \le N}|y_n - y(t_n)| \le Ch^2$ with $C$ independent of $h$.

## Depends on

- [First-order convergence of the explicit Euler method](../euler-method/explicit-euler-first-order-convergence.md)

## Expansion

A good expansion bounds the local truncation error by Taylor's theorem, proves zero-stability from the roots $1$ and $0$ of the first
characteristic polynomial, and combines them in a discrete Gronwall argument. Backward differentiation formulas, A-stability and Dahlquist's
barriers are separate nodes.

## Sources

- E. Hairer, S. P. Nørsett and G. Wanner, *Solving Ordinary Differential Equations I: Nonstiff Problems*, 2nd edition, Springer, 1993, for multistep methods.
