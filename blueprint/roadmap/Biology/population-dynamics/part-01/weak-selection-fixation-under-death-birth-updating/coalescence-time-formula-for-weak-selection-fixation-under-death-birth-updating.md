# Coalescence-time formula for weak-selection fixation under death-Birth updating

**Setting.** Let $G$ be a connected, weighted, undirected graph on $N \ge 2$ vertices with weights $w_{ij} = w_{ji} \ge 0$ and no self-loops ($w_{ii} = 0$). Each vertex holds one haploid individual, mutant (fitness $r > 0$) or resident (fitness $1$). Under **death-Birth (dB) updating**, a uniformly random individual dies and a neighbour $j$ of the vacated vertex $i$ reproduces into it with probability proportional to (fitness) $\times\, w_{ij}$. A single mutant is placed at a uniformly random vertex, and $\rho_G(r)$ denotes the probability that mutants take over. For the complete graph,

$$\rho_{K_N}(r) = \frac{N-1}{N}\,\frac{1-r^{-1}}{1-r^{-(N-1)}}, \qquad \rho_{K_N}(1+\delta) = \frac1N + \delta\,\frac{N-2}{2N} + O(\delta^2).$$

**Random walks.** Let $w_i = \sum_j w_{ij}$, $p_{ij} = w_{ij}/w_i$ and $\pi_i = w_i/\sum_j w_j$ (the stationary distribution). The expected coalescence times $\tau_{ij}$ of two walkers, of which one chosen at random steps at each time, solve

$$\tau_{ij} = \begin{cases} 0, & i = j,\\ 1 + \tfrac12\sum_k \big(p_{ik}\tau_{jk} + p_{jk}\tau_{ik}\big), & i \ne j,\end{cases}$$

the remeeting times are $\tau_i = 1 + \sum_j p_{ij}\tau_{ij}$, and Kac's return-time formula gives $\sum_i \pi_i^2\tau_i = 1$.

**Theorem.** With $r = 1 + \delta$,

$$\rho_G(1+\delta) = \frac1N + \delta\,\frac{N_{\mathrm{eff}} - 2}{2N} + O(\delta^2), \qquad N_{\mathrm{eff}} := \sum_{i} \pi_i\tau_i .$$

Hence $G$ amplifies weak selection (beats $K_N$ for all $r$ in some interval $(a,1)\cup(1,b)$ in the appropriate directions) if $N_{\mathrm{eff}} > N$, and suppresses it if $N_{\mathrm{eff}} < N$.

**Example.** For the star with $n$ leaves ($N = n+1$), $\tau_{\mathrm{hub}} = \tau_{\mathrm{leaf}} = N_{\mathrm{eff}} = 4n/(n+1) < N$ for $n \ge 2$, so the star suppresses weak selection and $\rho(1+\delta) = 1/N + \delta(N-2)/N^2 + O(\delta^2)$.

## Depends on

- [Average fixation equals Moran fixation on isothermal graphs (Birth-death updating)](../../isothermal-theorem-for-evolutionary-graph-dynami/average-fixation-eq-moran-fixation.md)

## Expansion

Under neutral drift $p_{ij}$ is the probability that $j$ reproduces given that $i$ dies, so ancestral lineages are random walks on $G$ and the neutral identity-by-descent structure is encoded by the $\tau_{ij}$. Differentiating the fixation probability at $\delta = 0$ reduces to a neutral expectation of the change in a reproductive-value-weighted mutant frequency, where vertex $i$ has reproductive value proportional to $\pi_i$; evaluating that expectation with the coalescence-time recursion, Eq. for $\tau_i$ and Kac's identity yields the first-order coefficient $(N_{\mathrm{eff}}-2)/(2N)$. Comparing with the expansion for $K_N$ gives the amplifier/suppressor criterion. The computation needs only an $O(N^2)$ linear system instead of the $O(2^N)$ Markov chain.

## Sources

- B. Allen, C. Sample, R. Jencks, J. Withers, P. Steinhagen, L. Brizuela, J. Kolodny, D. Parke, G. Lippner, Y. A. Dementieva, "Transient amplifiers of selection and reducers of fixation for death-Birth updating on graphs", PLoS Computational Biology 16 (2020) e1007529, Eqs. (1), (4)–(10) and S1 Appendix, <https://doi.org/10.1371/journal.pcbi.1007529>, PMCID PMC6968840.
