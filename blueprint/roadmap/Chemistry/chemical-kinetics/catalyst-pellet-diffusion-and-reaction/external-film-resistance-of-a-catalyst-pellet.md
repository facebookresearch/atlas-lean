# External film resistance of a catalyst pellet

Let $k \ge 0$ be the first-order rate constant, $c_b \ge 0$ the bulk concentration and $\eta > 0$ the internal
effectiveness factor, normalized at the pellet surface concentration $c_s$, so that the rate per unit pellet volume is
$\eta k c_s$. Let $k_m > 0$ be the external film coefficient, let $S_p, V_p > 0$ be the external surface area and volume of the
pellet, and put $K_f = (S_p/V_p)\,k_m$, the film coefficient per unit pellet volume. The steady surface balance
$\eta k c_s = K_f (c_b - c_s)$ has the unique solution

$$c_s = \frac{K_f\,c_b}{\eta k + K_f}, \qquad\text{so the observed rate is } k_{\mathrm{obs}} c_b
\text{ with } k_{\mathrm{obs}} = \frac{\eta k K_f}{\eta k + K_f} .$$

For $k > 0$, $1/k_{\mathrm{obs}} = 1/(\eta k) + 1/K_f$ and $k_{\mathrm{obs}}/k \to \eta$ as $K_f \to \infty$; for every
$k \ge 0$, $k_{\mathrm{obs}} \to \eta k$ as $K_f \to \infty$. At $k = 0$ the observed rate is zero directly, and the
reciprocal identity is not used. For $k > 0$, the overall effectiveness factor, normalized at the bulk concentration, is
$k_{\mathrm{obs}}/k$; it must not be substituted for $\eta$ in these formulas. For example, internal $\eta = 1/2$, $k = 2$ and
$K_f = 3$ give $k_{\mathrm{obs}} = 3/4$ and overall factor $3/8$, while using $3/8$ as $\eta$ would give $3/5$.

This is the film model of a single catalyst pellet. Two-film transfer between a gas and a liquid with Henry's law has a
different interface condition and is not a case of it; nonisothermal pellets are also outside this result.

## Depends on

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 7.3, the internal effectiveness factor normalized at the surface concentration, Equations 7.24–7.28 (pp. 366–367); Section 7.4.5, the flux boundary condition with external mass-transfer coefficient, Equation 7.53, and the Biot number, Equation 7.55 (pp. 381–382). The lumped surface balance and its solution are derived above.
