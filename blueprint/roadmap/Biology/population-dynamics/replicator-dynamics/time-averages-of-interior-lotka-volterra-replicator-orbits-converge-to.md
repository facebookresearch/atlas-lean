# Time averages of interior orbits converge to the interior equilibrium

For the replicator equation $\dot x_i = x_i((Ax)_i - x\cdot Ax)$ on $S_n$, if the equation is permanent, then there is a unique rest point $z$ in the interior of $S_n$ and the time averages along every interior orbit converge to it,

$$\frac1T\int_0^T x_i(t)\, dt \to z_i \qquad (T \to \infty,\ i = 1, \dots, n)$$

(Hofbauer and Sigmund 2003, Theorem 4, eq. (11)); if an interior orbit has $\omega$-limit points on the boundary, its time average need not converge. For the Lotka–Volterra system $\dot x_i = x_i(r_i + (Ax)_i)$ with invertible $A$ and interior equilibrium $x^* = -A^{-1}r$, integrating $\frac{d}{dt}\log x_i = r_i + (Ax)_i$ over a period of a periodic orbit of period $T$ gives $\frac1T\int_0^T x(t)\, dt = x^*$, and the same argument applied to an orbit that stays in a compact subset of the open orthant shows that its long-time averages converge to $x^*$ (Hofbauer and Sigmund 1998, Sec. 5.2). For the predator–prey system $\dot x = x(\alpha - \beta y)$, $\dot y = y(\delta x - \gamma)$ this gives Volterra's averages over a period: $\frac1T\int_0^T x = \gamma/\delta$ and $\frac1T\int_0^T y = \alpha/\beta$ (Hofbauer and Sigmund 1998, Sec. 2.3).

## Depends on

- [Rest points in the interior are equalizers](../../../Biology/population-dynamics/replicator-dynamics/is-rest-point-iff.md)
- [Solution of the replicator equation](is-solution.md)
- [Rest point of the replicator equation](is-rest-point.md)
- [Generalized Lotka–Volterra vector field](../replicator-and-lotka-volterra-equivalence/lv-field.md)

## Expansion

1. Permanence of the replicator equation, interior rest points as solutions of $(Ax)_1 = \dots = (Ax)_n$, $\sum_i x_i = 1$.
2. The integration argument: $\frac1T(\log x_i(T) - \log x_i(0)) \to 0$ for an orbit bounded away from the boundary, so every accumulation point $\bar x$ of the time averages satisfies $(A\bar x)_i = (A\bar x)_j$ for all $i, j$.
3. Uniqueness of the interior rest point under permanence, and convergence of the time averages.
4. The Lotka–Volterra form for periodic and for compactly contained orbits.
5. Volterra's averages for the predator–prey system, and Volterra's third law: harvesting that reduces both growth rates in proportion to the populations raises the average prey and lowers the average predator.

## Sources

- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. 40 (2003), 479–519, Theorem 4 and the remark after it. <https://doi.org/10.1090/S0273-0979-03-00988-1>
- J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge University Press, 1998, Secs. 2.3 and 5.2. <https://doi.org/10.1017/CBO9781139173179>
