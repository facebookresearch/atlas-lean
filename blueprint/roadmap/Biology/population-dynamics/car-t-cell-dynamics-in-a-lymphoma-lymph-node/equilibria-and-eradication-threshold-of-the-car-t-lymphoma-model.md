# Equilibria and eradication threshold of the CAR T-cell lymphoma model

**Model (dimensionless).** Let $C \ge 0$ be the CAR T-cell population and $L \ge 0$ the B-cell lymphoma load in a lymph node, after rescaling. With nonnegative parameters $m_1$ (antigen-driven CAR T expansion), $m_2$ (tumor-induced CAR T inactivation), $m_3$ (saturation of inactivation), $m_4$ (CAR T death and efflux) and $m_5$ (tumor killing by CAR T cells),

$$\frac{dC}{dt} = 1 + m_1 \frac{C L}{1 + L} - m_2 \frac{C L}{1 + m_3 C} - m_4 C, \qquad \frac{dL}{dt} = L - m_5 C L,$$

where the constant $1$ is the rescaled inflow of CAR T cells into the node. The nonnegative quadrant is positively invariant (Proposition 1).

**Tumor-free state (Proposition 2).** $E_1 = (1/m_4, 0)$ always exists, with Jacobian eigenvalues $-m_4$ and $1 - m_5/m_4$. It is asymptotically stable if $m_5 > m_4$ and unstable if $m_5 < m_4$.

**Coexistence states (Propositions 3-4).** Any other equilibrium has $C = 1/m_5$ and $L$ a root of $aL^2 + bL + c = 0$ with

$$a = -\frac{m_2}{1 + m_3/m_5}, \qquad b = m_1 + m_5 - m_4 - \frac{m_2}{1 + m_3/m_5}, \qquad c = m_5 - m_4,$$

giving a high-load state $E_2$ with $L_2 = (-b - \sqrt\Delta)/(2a)$ and a low-load state $E_3$ with $L_3 = (-b + \sqrt\Delta)/(2a)$, $\Delta = b^2 - 4ac$. Writing $k = m_2/(1 + m_3/m_5)$:
- they exist iff $m_5 \ge m_4$, or $m_5 < m_4$ and $k \le (m_1 + m_4 - m_5) - 2\sqrt{m_1(m_4 - m_5)}$ or $k \ge (m_1 + m_4 - m_5) + 2\sqrt{m_1(m_4 - m_5)}$;
- $L_2 \ge 0$ iff $m_5 \ge m_4$ or $k \le m_1 + m_5 - m_4$;
- $L_3 \ge 0$ iff $k \le m_1 + m_5 - m_4$ and $m_5 \le m_4$.

So when killing outpaces CAR T loss ($m_5 > m_4$) the tumor-free state is stable and, since $ac < 0$, exactly one positive coexistence state (the high-load $E_2$) exists; when $m_5 < m_4$ the tumor-free state is unstable and zero or two positive coexistence states exist.

**Theorem 5 (transcritical bifurcation).** At $m_4 = m_5$ the tumor-free state exchanges stability with $E_2$ if $m_2 > m_1(1 + m_3/m_5)$ and with $E_3$ if $m_2 < m_1(1 + m_3/m_5)$.

## Expansion

The $L$-equation forces $L = 0$ or $C = 1/m_5$ at equilibrium. On $L = 0$ the $C$-equation gives $C = 1/m_4$, and linearization at $E_1$ is triangular, so its eigenvalues are read off from the diagonal: $-m_4$ for $C$ and the tumor's net per-capita growth $1 - m_5 C = 1 - m_5/m_4$. Substituting $C = 1/m_5$ in the $C$-nullcline and multiplying by $m_5(1 + L)$ gives the quadratic. Since $a \le 0$, the sign analysis of $-b \pm \sqrt\Delta$ reduces to the signs of $b$ and $c$, yielding Proposition 4, and viewing $\Delta$ as a quadratic in $k$ gives the existence windows. At $m_5 = m_4$ we have $c = 0$, so one root of the quadratic is $L = 0$ and the corresponding coexistence state merges with $E_1$; which one ($E_2$ or $E_3$) is decided by the sign of $b$, that is, by comparing $m_2$ with $m_1(1 + m_3/m_5)$. Where $\Delta = 0$ the two coexistence states collide in a saddle-node.

## Sources

- S. Sabir, O. León-Triana, S. Serrano, R. Barrio, V. M. Pérez-García, "Mathematical Model of CAR T-Cell Therapy for a B-Cell Lymphoma Lymph Node", Bulletin of Mathematical Biology 87(3) (2025) 40, Equations (2)-(8), Propositions 1-4 and Theorem 5, <https://doi.org/10.1007/s11538-025-01417-1>, PMCID PMC11805830.
