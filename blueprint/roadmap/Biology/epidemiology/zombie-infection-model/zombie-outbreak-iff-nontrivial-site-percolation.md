# Zombie outbreak at high bite rates iff site percolation is non-trivial

**Setting.** The zombie infection model with relative bite rate $\lambda$ on a connected, locally finite graph $G$ of bounded degree, outbreak meaning $\mathcal{Z}_t \to \infty$ with positive probability; the comparison process is the SIR model on $G$ with infected count $\mathcal{I}_t$.

**Theorem.** The following are equivalent:
1. there is $\lambda_*^{\mathrm{ZIM}} \in [1,\infty)$ such that the ZIM has an outbreak with positive probability for every $\lambda > \lambda_*^{\mathrm{ZIM}}$ and every finite initial set $\Delta$;
2. there is $\lambda_c^{\mathrm{SIR}} \in (0,\infty)$ such that the SIR model has $\mathcal{I}_t \to \infty$ with positive probability for every $\lambda > \lambda_c^{\mathrm{SIR}}$ and every finite $\Delta$;
3. the critical probability for site percolation satisfies $p_c^{\mathrm{site}}(G) < 1$.

If $p_c = p_c^{\mathrm{site}}(G) < 1$ one may take

$$\lambda_*^{\mathrm{ZIM}} = \frac{p_c^{1/d}}{1 - p_c^{1/d}}, \qquad d = \deg(G) - 1.$$

**Non-monotonicity.** Unlike SIR, the ZIM is not monotone in the graph: there are bounded-degree graphs $G_1 \subset G_2$ for which the ZIM has an outbreak on $G_1$ but not on $G_2$. On trees with at most two infected clusters it is monotone in $\lambda$ and in the initial configuration.

## Depends on

- [Zombie infection model: extinction threshold and complete-graph limit](zombie-infection-model-extinction-and-complete-graph-limit.md)

## Expansion

A node is "open" if its zombie, once created, bites each of its at most $d$ forward susceptible neighbours before being destroyed; with independent exponential clocks this has probability at least $(\lambda/(\lambda+1))^d$. When this exceeds $p_c$, an infinite open cluster of sites exists and the infection follows it, which gives the explicit $\lambda_*$. Conversely, if $p_c = 1$ even arbitrarily infectious SIR or ZIM dynamics cannot reach infinitely many nodes. Adding edges can hurt zombies because extra susceptible neighbours add extra kill clocks.

## Sources

- S. A. Bethuelsen, E. Broman, S. Modée, "The Zombie Infection Model" (2026), Theorems 1-4 and Theorem 6, <https://doi.org/10.48550/arXiv.2607.29409>.
