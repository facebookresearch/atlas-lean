# Time to reproductive isolation under asymmetric mating preferences

**Model.** Haploid individuals carry allele $\alpha \in \{A, a\}$ and live in patch $i \in \{1,2\}$; write $\bar\alpha$ for the other allele. $\mathbf{N}^K(t) = (N^K_{A,1}, N^K_{a,1}, N^K_{A,2}, N^K_{a,2})$ is a continuous-time Markov jump process with, in patch $i$,

- birth rate of $\alpha$-individuals $\; b\, N^K_{\alpha,i}\, \dfrac{\beta_\alpha N^K_{\alpha,i} + N^K_{\bar\alpha,i}}{N^K_{\alpha,i} + N^K_{\bar\alpha,i}}$ (assortative mating with allele-specific preference strength $\beta_\alpha$),
- death rate $\; \big(d + \tfrac{c}{K}(N^K_{\alpha,i} + N^K_{\bar\alpha,i})\big) N^K_{\alpha,i}$ (logistic competition),
- migration rate to the other patch $\; m_\alpha\, \dfrac{N^K_{\bar\alpha,i}}{N^K_{\alpha,i} + N^K_{\bar\alpha,i}}\, N^K_{\alpha,i}$ (individuals leave when mates of their type are scarce),

with $\beta_A, \beta_a > 1$, $b > d > 0$, $c > 0$, $m_A, m_a \ge 0$. As $K \to \infty$, $\mathbf{N}^K/K$ converges uniformly on compact time intervals in probability to the solution of the corresponding four-dimensional ODE. With $\zeta_\alpha = (b\beta_\alpha - d)/c$, this ODE has four stable equilibria, all reproductively isolated (migration vanishes): fixation of one allele in both patches, $(\zeta_A, 0, \zeta_A, 0)$ and $(0, \zeta_a, 0, \zeta_a)$, and **patch-wise isolation** $(\zeta_A, 0, 0, \zeta_a)$ and $(0, \zeta_a, \zeta_A, 0)$.

**Theorem.** Let $\beta_{\min} = \min(\beta_A, \beta_a)$, assume $m_A(\beta_A - 1) + m_a(\beta_a - 1) \le 2(b - d)(\beta_{\min} - 1)$, and let $\mathcal{S}$ be the compact set on which the weighted sums $\Sigma_i = (\beta_A - 1) z_{A,i} + (\beta_a - 1) z_{a,i}$ satisfy $\Sigma_i \ge (\beta_{\min}-1)(b-d)/(4c)$ and $\Sigma_1 + \Sigma_2 \le 4(\beta_{\max} - 1)(b\beta_{\max} - d)/c$.

*(1)* $\mathcal{S}$ is positively invariant and every trajectory enters it in finite time.

*(2)* Suppose $m_A = 0$ iff $m_a = 0$. There is $m_0 > 0$ such that for $m_A, m_a \le m_0$ the four equilibria have open basins of attraction in $\mathcal{S}$ whose union is dense in $\mathcal{S}$. Without migration ($m_A = m_a = 0$) the basin of the equilibrium with $\alpha$ in patch $1$ and $\alpha'$ in patch $2$ is exactly $\{(\beta_\alpha - 1) z_{\alpha,1} > (\beta_{\bar\alpha} - 1) z_{\bar\alpha,1},\ (\beta_{\alpha'} - 1) z_{\alpha',2} > (\beta_{\bar\alpha'} - 1) z_{\bar\alpha',2}\} \cap \mathcal{S}$.

*(3)* *(Time to isolation.)* If $\mathbf{N}^K(0)/K \to \mathbf{z}^0$ in probability, with $\mathbf{z}^0$ in the basin of $(\zeta_A, 0, 0, \zeta_a)$ and $(z^0_{a,1}, z^0_{A,2}) \ne (0,0)$, then there are $C_0, M, V > 0$ such that for all small $\varepsilon$ the hitting time $T^K_\varepsilon$ of the box $[(\zeta_A \pm \varepsilon)K] \times \{0\} \times \{0\} \times [(\zeta_a \pm \varepsilon)K]$ satisfies, with probability tending to $1$,

$$\Big| \frac{T^K_\varepsilon}{\log K} - \frac{1}{\omega(A,a)} \Big| \le C_0 \varepsilon, \qquad \omega(\alpha,\alpha') = \tfrac12\Big[ b(\beta_\alpha + \beta_{\alpha'} - 2) + m_\alpha + m_{\alpha'} - \sqrt{\big(b(\beta_\alpha - \beta_{\alpha'}) + m_{\alpha'} - m_\alpha\big)^2 + 4 m_\alpha m_{\alpha'}} \Big],$$

and the process then stays in the box enlarged by the factor $M$ for a time at least $e^{VK}$. Analogous statements hold for the other three equilibria.

## Depends on

- [Kurtz's law of large numbers for density-dependent chains](../../../../../Probability/markov-chains/density-dependent-markov-chains/kurtz-law-of-large-numbers-for-density-dependent.md)

## Proof depends on

- [Kendall's law of the linear birth–death process](../../../../../Probability/branching-processes/linear-birth-death-process/prob.md)

## Expansion

The law of large numbers is the Ethier–Kurtz density-dependent limit. Positive invariance of $\mathcal{S}$ follows from differential inequalities for the weighted sums $\Sigma_i$, which absorb the frequency-dependent birth terms. Without migration each patch is a planar system with two stable fixation equilibria separated by the line $(\beta_A - 1) z_A = (\beta_a - 1) z_a$; small migration is a regular perturbation that preserves hyperbolicity and basin structure. Near the target equilibrium the two minority subpopulations $(N_{a,1}, N_{A,2})$ form, to first order, a two-type subcritical branching process with migration between types, whose mean matrix has dominant eigenvalue $-\omega(A,a)$; its extinction from size $\varepsilon K$ takes time $\log K / \omega(A,a)$. The long residence time $e^{VK}$ is a Freidlin–Wentzell large-deviation estimate around a stable equilibrium.

## Sources

- Hélène Leman, *A stochastic model for reproductive isolation under asymmetrical mating preferences*, Bull. Math. Biol. 80(9) (2018), 2502–2525. <https://doi.org/10.1007/s11538-018-0479-2> Lemmas 3.1–3.3, Theorems 3.1 and 3.2, Theorem 4.1, Lemma B.1. Locators use the numbering of the preprint arXiv:1709.05987.
