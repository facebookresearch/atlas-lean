# Mean age system of a nonautonomous compartmental system

**Setting.** A nonautonomous compartmental system $\dot x = B(t)x + s(t)$ on $d$ pools has bounded continuous $B(t)$ with $b_{ii}(t) < 0$, $b_{ij}(t) \ge 0$ for $i \ne j$ and $\sum_i b_{ij}(t) \le 0$, and bounded continuous inputs $s(t) \ge 0$. Let $p_i(a,t)$ be the density over age $a$ (time since entry into the system) of the mass in pool $i$ at time $t$; it obeys the McKendrick–von Foerster equation

$$\frac{\partial p_i}{\partial t} + \frac{\partial p_i}{\partial a} = \sum_{j=1}^d b_{ij}(t)\, p_j, \qquad p_i(0, t) = s_i(t),$$

with $\int_0^\infty p_i(a,t)\, da = x_i(t)$.

**Theorem.** Along a solution with $x_i(t) > 0$, the mean ages $\bar a_i(t) = \int_0^\infty a\, p_i(a,t)\, da \,/\, x_i(t)$ satisfy the ordinary differential equation

$$\dot{\bar a}_i = 1 + \frac{\sum_{j=1}^d (\bar a_j - \bar a_i)\, b_{ij}(t)\, x_j(t) - \bar a_i\, s_i(t)}{x_i(t)}, \qquad i = 1, \dots, d,$$

equivalently $\dot{\bar a} = A(t, x(t))\,\bar a + \mathbf 1$ with $A = X(t)^{-1}\big(\text{off-diagonal } b_{ij}x_j;\ \text{diagonal } -s_i - \sum_{j\ne i} b_{ij}x_j\big)$ and $X = \operatorname{diag}(x)$. Together with the mass equation this is a skew-product system in $(x, \bar a)$ that is linear in $\bar a$ for given $x(\cdot)$. The transit time at time $t$, the mean age of the mass leaving the system, is $\sum_j \bar a_j(t)\, \ell_j(t) x_j(t) / \sum_j \ell_j(t) x_j(t)$ with $\ell_j = -\sum_i b_{ij}$ the loss rates.

## Expansion

Differentiate the quotient defining $\bar a_i$, substitute the PDE, and integrate by parts: $\int_0^\infty a\, \partial_a p_i\, da = -x_i$ (assuming $a\,p_i \to 0$ as $a \to \infty$), so the "ageing" term contributes $+1$; the transfer terms contribute $\sum_j b_{ij}x_j\bar a_j / x_i$, and subtracting $\bar a_i \dot x_i / x_i$ with $\dot x_i = \sum_j b_{ij} x_j + s_i$ gives the formula, in which fresh input of age zero dilutes the mean age at rate $s_i/x_i$. The mean age system needs only the solution $x(t)$, not the full age distribution. For constant $B$ and $s$ at equilibrium $x^\ast = -B^{-1}s$, setting $\dot{\bar a} = 0$ recovers the stationary mean ages, whose stock-weighted average is $M = -\mathbf 1^\top B^{-1}\eta$; under exponential stability of $\dot x = B(t)x$ (for example uniform strict column diagonal dominance) the mean age system is itself exponentially stable, so the mean ages forget their initial values.

## Sources

- M. Rasmussen, A. Hastings, M. J. Smith, F. B. Agusto, B. M. Chen-Charpentier, F. M. Hoffman, J. Jiang, K. E. O. Todd-Brown, Y. Wang, Y.-P. Wang and Y. Luo, "Transit times and mean ages for nonautonomous and autonomous compartmental systems", Journal of Mathematical Biology 73 (2016), 1379–1398, Sections 3–5 (Definition 1, Eqs. (13)–(16), Theorems 1–3, Definition 2), <https://doi.org/10.1007/s00285-016-0990-8>, PMCID: PMC5061853.
