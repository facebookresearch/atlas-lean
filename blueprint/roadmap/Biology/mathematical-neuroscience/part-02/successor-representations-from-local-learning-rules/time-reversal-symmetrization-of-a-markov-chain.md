# Time-reversal symmetrization of a Markov chain

Let $P$ be the transition matrix of an irreducible Markov chain on a finite state space $\mathcal S$ with stationary distribution $\pi > 0$, and let $\Pi = \operatorname{diag}(\pi)$. The **backward** (time-reversed) chain has transition probabilities

$$P^{\mathrm{backward}}_{s,s'} = \Pr(S_t = s' \mid S_{t+1} = s) = \frac{\pi(s')P_{s',s}}{\pi(s)},$$

i.e. $P^{\mathrm{backward}} = \Pi^{-1}P^\top\Pi$. It is a stochastic matrix with the same stationary distribution $\pi$, and it is the adjoint $P^*$ of $P$ for the inner product $\langle x, y\rangle_\pi = x^\top \Pi y$. Consequently:

1. $P^{\mathrm{backward}} = P$ iff the chain satisfies detailed balance $\pi(s)P_{s,s'} = \pi(s')P_{s',s}$ (is reversible).
2. For every $\alpha, \beta \ge 0$ with $\alpha + \beta > 0$, the mixture $P_{\alpha,\beta} = \frac{\alpha}{\alpha+\beta}P + \frac{\beta}{\alpha+\beta}P^{\mathrm{backward}}$ is a stochastic matrix with stationary distribution $\pi$, and the **symmetrized chain** $P^{\mathrm{sym}} = \tfrac12(P + P^{\mathrm{backward}})$ is always reversible, being self-adjoint in $\langle\cdot,\cdot\rangle_\pi$

(Keck et al. 2025, Eqs. 19 and 44–48).

## Expansion

Row sums of $\Pi^{-1}P^\top\Pi$ equal $\pi(s)^{-1}\sum_{s'}\pi(s')P_{s',s} = 1$ by stationarity, and $\pi^\top \Pi^{-1}P^\top\Pi = (P\mathbf 1)^\top \Pi = \pi^\top$. The identity $x^\top\Pi P y = (\Pi^{-1}P^\top\Pi x)^\top \Pi y$ shows $P^* = P^{\mathrm{backward}}$. Since $(P^*)^* = P$, $(P^{\mathrm{sym}})^* = P^{\mathrm{sym}}$, and self-adjointness in $\langle\cdot,\cdot\rangle_\pi$ is exactly detailed balance. With $\pi$ uniform this is the ordinary symmetric part $\tfrac12(P + P^\top)$.

## Sources

- J. Keck, C. Barry, C. F. Doeller and J. Jost, *Impact of symmetry in local learning rules on predictive neural representations and generalization in spatial navigation*, PLoS Computational Biology (2025), e1013056, Eqs. (19), (44)–(48). <https://doi.org/10.1371/journal.pcbi.1013056> (PMCID: PMC12184951)
