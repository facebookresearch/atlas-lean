# Phase transition of neuropercolation with long-range axons

**Model.** The cortical neuropil is modelled as a random graph $G$ on the discrete torus $\mathbb Z_N^2$, an $(N+1)\times(N+1)$ grid with periodic boundary. It has two kinds of edges. Short edges join lattice neighbours. Long edges, which stand for long axons, are added independently: a pair of vertices at distance $d$ is joined with probability
$$p_d=\frac{c}{N\,d^{\alpha}},$$
for constants $c>0$ and $\alpha$ (for example $\alpha=1$). Each vertex $v$ carries a state $\chi_v(t)\in\{0,1\}$. Initially each vertex is active independently with probability $p_0$, and states then update synchronously by the threshold rule
$$\chi_v(t+1)=\mathbf 1\Big(\sum_{u\in N(v)}\chi_u(t)\ge k\Big),$$
where $N(v)$ is the neighbourhood of $v$ in $G$ and $k$ is the activation threshold. Let $\rho_t=|A(t)|/N^2$ be the active fraction.

**Theorem (mean-field phase transition).** In the mean-field approximation for $\rho_t$ there is a critical initial activation probability $p_c=p_c(k,\lambda)$, where $\lambda$ scales linearly with the density of long edges. With high probability as $N\to\infty$, every vertex is eventually active if $p_0>p_c$, and every vertex is eventually inactive if $p_0<p_c$. The value $p_c$ is given implicitly through the solution of transcendental equations in $k$ and $\lambda$.

## Expansion

This is a bootstrap-type percolation (threshold activation) process on a lattice coupled to a sparse random graph, so local clusters can trigger distant ones. For small $\lambda$ the critical probability stays close to that of the purely local system. As $\lambda$ grows it decreases: long axons lower the initial activity needed for system-wide ignition. That is the mechanism the source offers for brain dynamics poised near criticality and for abrupt, roughly 100 ms recurrent phase transitions in cortical EEG. The source writes the critical value as $p_c$ in the same symbol as the long-edge probability. Its figure plots $p_c$ against $\lambda$, which fixes the long-edge density, so the threshold is in the initial activation density.

## Sources

- R. Kozma, B. J. Baars, N. Geld, "Evolutionary advantages of stimulus-driven EEG phase transitions in the upper cortical layers", *Frontiers in Systems Neuroscience* 15 (2021) 784404, Section 3.1, Eqs. (1)–(2), Proposition 6 and Figure 1, <https://doi.org/10.3389/fnsys.2021.784404>, PMCID PMC8692947.
- The theorem restated there is due to S. Janson, R. Kozma, M. Ruszinkó and Y. Sokolov (2019).
