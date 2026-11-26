# Interior equilibrium and local stability of the delayed Allee predator–prey map

**Model.** Prey $x_n \ge 0$ and predator $y_n \ge 0$ evolve with a delay $f \in \mathbb N_0$ by the exponential (Ricker-type) map

$$x_{n+1} = x_{n-f} \exp\Bigl(\frac{r x_{n-f} (1 - x_{n-f}/k)}{a + x_{n-f}} - b y_{n-f}\Bigr), \qquad y_{n+1} = y_{n-f} \exp\Bigl(b x_{n-f} - \frac{d\, y_{n-f}}{c + y_{n-f}}\Bigr),$$

where $r$ is the prey growth rate, $k$ the prey carrying capacity, $b$ the predation rate, $d$ the predator mortality, and $a, c$ Allee constants for prey and predator. Assume $r, k, b, c, d > 0$ and $a \ge 0$.

**Equilibria.** The equilibria are the origin, the predator-free state $(k, 0)$, and interior states $P = (x^*, y^*)$ with

$$y^* = \frac{b c\, x^*}{d - b x^*}, \qquad g(x^*) := r\Bigl(1 - \frac{x^*}{k}\Bigr)(d - b x^*) - b^2 c\, (a + x^*) = 0 .$$

Since $g$ is a convex quadratic with $g(0) = r d - a b^2 c$ and $g(k) = -b^2 c (a + k) < 0$, an interior equilibrium with $0 < x^* < k$ exists, and is then unique, if and only if $a b^2 c < r d$; at that root $d - b x^* > 0$, so $y^* > 0$.

**Delay reduction.** Because $(x_{n+1}, y_{n+1})$ depends only on $(x_{n-f}, y_{n-f})$, the delayed system splits into $f + 1$ independent copies of the undelayed map $F(x, y)$ on the residue classes of $n$ modulo $f + 1$. Linearizing at an equilibrium gives $\lambda^{f+1} = \mu$ for each eigenvalue $\mu$ of the Jacobian $J$ of $F$, so the equilibrium is locally asymptotically stable for the delayed system if and only if it is for $F$, independently of $f$.

**Theorem 1 (sufficient stability criterion).** Let $J = \begin{pmatrix} m_1 & m_2 \\ m_3 & m_4 \end{pmatrix}$ be the Jacobian of $F$ at the interior equilibrium $P$. If

$$|m_1 m_4 - m_2 m_3| + |m_1 + m_4| < 1,$$

then $P$ is locally asymptotically stable.

## Expansion

The criterion is a sufficient form of the Jury conditions for a $2 \times 2$ matrix, which place both eigenvalues in the open unit disk if and only if $|\operatorname{tr} J| < 1 + \det J < 2$. If $|\det J| + |\operatorname{tr} J| < 1$, then $\det J < 1$ gives $1 + \det J < 2$, and $|\operatorname{tr} J| < 1 - |\det J| \le 1 + \det J$. At the origin the Jacobian of $F$ is the identity, so linearization is inconclusive there; at $(k, 0)$ the predator direction has multiplier $e^{b k} > 1$, so the predator-free state is unstable and the prey alone cannot exclude an invading predator. The source illustrates the criterion numerically (stable nodes, unstable foci, saddles) and reports period-4 cycles and fractal-looking basins for larger delays.

## Sources

- S. Goldar, S. S. Hassan, "Fractality in a delayed-prey-predator ecological system with Allee effects", arXiv:2107.12300 (2021), Section 2.1 (model, equilibria, Jacobian and Theorem 1). <https://doi.org/10.48550/arXiv.2107.12300>
