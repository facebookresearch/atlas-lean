# Second-order convergence of the two-step Adams-Bashforth method

This node covers the convergence of the simplest explicit multistep method. Let $f : [0, T] \times \mathbb{R}^d \to \mathbb{R}^d$ be continuous
and Lipschitz in its second argument, and let the solution $y$ of $y' = f(t, y)$, $y(0) = \eta$, be three times continuously differentiable on
$[0, T]$. For a step $h = T/N$ define

$$Y_{n+2} = Y_{n+1} + h\Big(\tfrac32 f(t_{n+1}, Y_{n+1}) - \tfrac12 f(t_n, Y_n)\Big), \qquad t_n = nh .$$

If the numerical starting values $Y_0, Y_1$ satisfy $|Y_0 - \eta| + |Y_1 - y(h)| \le Kh^2$, then
$\max_{0 \le n \le N}|Y_n - y(t_n)| \le Ch^2$ with $C$ independent of $h$.

## Expansion

The order and zero-stability of the method, and the convergence theorem for scalar equations with its $O(h^p)$ error bound, are pages linked
below. A good expansion adds the vector-valued form of the error bound for perturbed linear difference equations, for $\mathbb{R}^d$-valued
sequences in any norm, so that the convergence theorem applies to systems.

## Proof depends on

- [Orders, error constants and stability intervals of the Adams methods](adams-methods/orders-and-stability-intervals-of-adams-methods.md)
- [The two-step Adams–Bashforth method is zero-stable](adams-methods/two-step-adams-bashforth-method-is-zero-stable.md)
- [Dahlquist equivalence theorem](dahlquist-equivalence-theorem.md)

## Sources

- E. Hairer, S. P. Nørsett and G. Wanner, *Solving Ordinary Differential Equations I: Nonstiff Problems*, 2nd edition, Springer, 1993, for multistep methods.
