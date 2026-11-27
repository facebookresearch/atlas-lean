# Global error bound for the θ-method

Let $f$ be continuous on $[x_0, X_M] \times \mathbb{R}$ with $|f(x, y) - f(x, z)| \le L|y - z|$ for all $x$ and all real $y, z$, for a constant $L > 0$ (if $f$ satisfies this with $L = 0$, it satisfies it with every $L > 0$; for $\theta > 0$ and $\theta L h < 1$ each implicit step has exactly one solution), let the solution $y$ of $y' = f(x, y)$, $y(x_0) = y_0$ be three times continuously differentiable on $[x_0, X_M]$, with $M_2 = \max |y''|$ and $M_3 = \max |y'''|$, and let $e_n = y(x_n) - y_n$ be the global error of the [θ-method](theta-method.md) with step $h$, where $\theta L h < 1$. Then for $n = 0, \dots, N$

$$|e_n| \le |e_0| \exp\Big(L\, \frac{x_n - x_0}{1 - \theta L h}\Big) + \frac{h}{L}\Big(\Big|\frac12 - \theta\Big| M_2 + \frac{h}{3} M_3\Big)\Big[\exp\Big(L\, \frac{x_n - x_0}{1 - \theta L h}\Big) - 1\Big].$$

So with $e_0 = 0$ the error is $O(h^2)$ for the trapezium rule $\theta = 1/2$ and $O(h)$ for every other $\theta$.

## Depends on

- [The θ-method](theta-method.md)

## Related topics

- [First-order convergence of the explicit Euler method](explicit-euler-first-order-convergence.md): the case $\theta = 0$.

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 2.2, the detailed proof for $\theta = 0$ ending in (20) and the bound (21) for general $\theta$, quoted there with the proof left to the reader. The bound is printed there with $(\frac12 - \theta)$; the absolute value is needed for $\theta > 1/2$. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
