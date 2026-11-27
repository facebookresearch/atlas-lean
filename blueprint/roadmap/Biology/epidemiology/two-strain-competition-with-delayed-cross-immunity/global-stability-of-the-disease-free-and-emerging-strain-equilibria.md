# Global stability of the disease-free and emerging-strain equilibria

In the [two-strain cross-immunity model](equilibria-and-harmless-delay-in-the-two-strain-cross-immunity-model.md) with reproduction numbers $R_i = a\beta_i/(d(d_i + \gamma_i))$ and any cross-immunity delay $\tau \ge 0$, consider solutions whose initial data are bounded, continuous, nonnegative histories $(S, I_1, I_2, R_l)(\theta)$, $\theta \in [-\tau, 0]$.

**Theorem (disease-free equilibrium).** If $\max\{R_1, R_2\} < 1$, then $E_0 = (a/d, 0, 0, 0)$ is globally asymptotically stable.

**Theorem (emerging strain wins).** If $R_1 < 1 < R_2$, then the strain-2-only equilibrium $E_2 = \big(\frac{\gamma_2 + d_2}{\beta_2}, 0, \frac{d}{\beta_2}(R_2 - 1), 0\big)$ is globally asymptotically stable (among solutions with $I_2(0) > 0$).

## Depends on

- [Equilibria and harmless delay in the two-strain cross-immunity model](equilibria-and-harmless-delay-in-the-two-strain-cross-immunity-model.md)

## Proof depends on

- [Forward invariance of compact sublevel sets and LaSalle's principle for differential equations](../../../Analysis/ordinary-differential-equations/forward-invariance-of-compact-sublevel-sets-and-lasalle-s-principle.md)

## Expansion

From $S' \le a - dS$, $\limsup_{t\to\infty} S(t) \le a/d$ and $[0, a/d]$ is positively invariant and attracting for $S$. If $R_1 < 1$, i.e. $\beta_1 a/d < \gamma_1 + d_1$, choose $\varepsilon > 0$ with $\beta_1(a/d + \varepsilon) < \gamma_1 + d_1$; for large $t$, $S < a/d + \varepsilon$ and so $I_1' \le \big(\beta_1(a/d + \varepsilon) - (\gamma_1 + d_1)\big)I_1$, whence $I_1 \to 0$ exponentially. Then the forcing $\gamma_1 I_1(t - \tau)$ of $R_l$ vanishes and $R_l' \le \gamma_1 I_1(t-\tau) - dR_l$ gives $R_l \to 0$. If moreover $R_2 < 1$, the same comparison with $S + R_l$ eventually below $a/d + \varepsilon$ gives $I_2 \to 0$, and then $S \to a/d$, proving global attraction to $E_0$; local stability holds by the linearization. If instead $R_2 > 1$, the limiting system on $I_1 = R_l = 0$ is the one-strain model $S' = a - dS - \beta_2 SI_2$, $I_2' = \beta_2 SI_2 - (\gamma_2 + d_2)I_2$, whose endemic equilibrium is globally asymptotically stable for $R_2 > 1$ by a Volterra-type Lyapunov function; the theory of asymptotically autonomous systems transfers this to the full delayed system. The delay plays no role in either argument, consistent with it being harmless.

## Sources

- B. Pell, S. Brozak, T. Phan, F. Wu and Y. Kuang, "The emergence of a virus variant: dynamics of a competition model with cross-immunity time-delay validated by wastewater surveillance data for COVID-19", *Journal of Mathematical Biology* 86 (2023), 63, Theorem 5 and Theorem 10 with their proofs, <https://doi.org/10.1007/s00285-023-01900-0> (PMC10054223).
