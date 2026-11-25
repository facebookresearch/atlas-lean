# Slowest decay rate of a convectively cooled slab

This node covers the small-Biot-number limit that justifies the lumped thermal model for a slab. Let $\theta(x, t)$, the excess
temperature over the ambient, solve $\theta_t = \alpha\theta_{xx}$ on $(0, L) \times (0, \infty)$ with $\theta_x(0, t) = 0$,
$-k\,\theta_x(L, t) = h\,\theta(L, t)$ and $\theta(x, 0) = \theta_0$, where $\alpha, k, h, L > 0$ and $\theta_0$ is a constant, and let
$\mathrm{Bi} = hL/k$. Then

$$\theta(x, t) = \sum_{n\ge1} C_n \cos\!\Big(\frac{\lambda_n x}{L}\Big)\exp\!\Big(-\lambda_n^2\frac{\alpha t}{L^2}\Big),\qquad C_n = \frac{4\theta_0\sin\lambda_n}{2\lambda_n + \sin 2\lambda_n},$$

where $\lambda_n \in ((n-1)\pi, (n-\tfrac12)\pi)$ is the unique root there of $\lambda\tan\lambda = \mathrm{Bi}$. The slowest rate satisfies
$\lambda_1^2 \le \mathrm{Bi}$ and $\lambda_1^2/\mathrm{Bi} \to 1$ as $\mathrm{Bi} \to 0$, so it approaches the lumped rate $hA/(\rho c V) = \mathrm{Bi}\,\alpha/L^2$.

## Depends on

- [Heat equation](../heat-equation/README.md)

## Expansion

A good expansion proves the eigenfunction expansion from the Sturm-Liouville problem with Robin data, the location and
uniqueness of each $\lambda_n$, and the two statements about $\lambda_1$, then states the uniform comparison between $\theta$ and the lumped
solution in a chosen norm as a separate quantitative node.

## Sources

- T. L. Bergman, A. S. Lavine, F. P. Incropera and D. P. DeWitt, *Fundamentals of Heat and Mass Transfer*, 7th edition, Wiley, 2011, for transient conduction and the lumped capacitance method.
