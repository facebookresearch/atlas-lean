# Hidden-edge variance fraction in the three-state ion-channel chain

Consider the linear chain $1 \rightleftharpoons 2 \rightleftharpoons 3$ with per-capita rates $\alpha_{12}, \alpha_{21}, \alpha_{23}, \alpha_{32} > 0$, in which only state 3 is observable (conducting), $M = (0,0,1)^{\top}$. In the Langevin approximation of a large population, let $R_{12}$ be the contribution of the noise on the hidden edge pair $1 \leftrightarrow 2$ and $R_{23}$ that of the observable pair $2 \leftrightarrow 3$ to the stationary variance of the occupancy of state 3 (their sum is that variance), and let $\eta = R_{12}/(R_{12} + R_{23})$ be the hidden-edge fraction.

**Theorem.** With stationary distribution $\pi \propto (\alpha_{21}\alpha_{32},\ \alpha_{12}\alpha_{32},\ \alpha_{12}\alpha_{23})$,

$$\eta = \frac{\alpha_{21}}{\alpha_{12} + \alpha_{21}}\cdot\frac{\alpha_{23}}{\alpha_{12} + \alpha_{21} + \alpha_{23} + \alpha_{32}} = \frac{\pi_1}{\pi_1 + \pi_2}\cdot\frac{\alpha_{23}}{\operatorname{Tr}(-L)} .$$

Consequences:

1. $\eta \leq \dfrac{\alpha_{23}}{\alpha_{23} + \alpha_{32}} = \dfrac{\pi_3}{\pi_2 + \pi_3}$ and $\eta \leq \dfrac{\tau_{12}}{\tau_{12} + \tau_{23}}$, where $\tau_{ij} = (\alpha_{ij} + \alpha_{ji})^{-1}$ is the relaxation time of the isolated pair. An **edge importance reversal** ($\eta > 1/2$, the hidden edges dominating the observed variance) therefore requires $\pi_2 < \pi_3$ and slower equilibration on the hidden pair than on the observable pair.
2. Reversal does occur, and $\eta \to 1$, when the opening rate is much faster than all others ($\alpha_{23} \gg \max(\alpha_{12},\alpha_{21},\alpha_{32})$) and the hidden state 2 is sparsely occupied relative to state 1 ($\alpha_{12} \ll \alpha_{21}$): for any fixed rates, letting $\alpha_{23} \to \infty$ and $\alpha_{12} \to 0$ drives both factors to $1$.
3. Changing the chain with only two distinct timescales (one parameter scaling any subset of the four rates against unit rates) never produces reversal; at least three separated timescales are needed.

So stochastic shielding (dropping the hidden-edge noise) is the right reduction unless the chain has a fast opening step behind a sparsely populated bottleneck, the regime seen in the nicotinic acetylcholine receptor at low agonist concentration.

## Depends on

- [Edge decomposition of the stationary covariance of a first-order transition network](edge-decomposition-of-the-stationary-covariance-of-a-first-order-transition-network.md)

## Expansion

The chain satisfies detailed balance, so $J_{12} = J_{21}$ and $J_{23} = J_{32}$, and the variance of $X_3$ splits as $R_{12} + R_{23}$ by the edge decomposition of the stationary covariance. The $3 \times 3$ Laplacian has explicit eigenvalues and eigenvectors, and inserting them into the per-edge Lyapunov solutions gives the closed form above; solving the two per-edge Lyapunov equations numerically for random rates reproduces it to machine precision. The bounds in item 1 follow at once: the first factor is at most $1$, and $\alpha_{23}/(\alpha_{12}+\alpha_{21}+\alpha_{23}+\alpha_{32})$ is at most both $\alpha_{23}/(\alpha_{23}+\alpha_{32})$ and $(\alpha_{23}+\alpha_{32})/(\alpha_{12}+\alpha_{21}+\alpha_{23}+\alpha_{32})$. The identity $\pi_2/\pi_3 = \alpha_{32}/\alpha_{23}$ links the first bound to occupancies. Item 3 comes from checking each one-parameter family against the exact formula.

## Sources

- D. R. Schmidt, R. F. Galán, P. J. Thomas, "Stochastic shielding and edge importance for Markov chains with timescale separation", *PLoS Computational Biology* 14(6) (2018) e1006206. Results, "3-state chain with two timescales" (Eq. 8, Figs. 5–6), "Generalized 3-state model with timescale separation" (Eqs. 9–21) and "Exact expression for $\eta$" (Eq. 22 and the asymptotic inversion argument). <https://doi.org/10.1371/journal.pcbi.1006206>. PMCID: PMC6023243.
