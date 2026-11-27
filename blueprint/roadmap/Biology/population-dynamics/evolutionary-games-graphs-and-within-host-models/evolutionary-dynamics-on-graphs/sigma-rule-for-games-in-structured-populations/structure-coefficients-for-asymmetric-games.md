# Structure coefficients for asymmetric games

Consider a finite population of fixed size $N$ and arbitrary fixed structure, with two traits $S$ and $NS$, symmetric mutation with probability $u > 0$ per offspring (a mutant offspring takes a uniformly random trait), and replacement rules that depend smoothly on fecundities $F_i = 1 + \delta U_i + O(\delta^2)$ (or $e^{\delta U_i}$), where $U_i$ is the payoff of the individual at $i$ and $\delta \ge 0$ is the selection intensity. Payoffs may depend on location: an individual of trait $x$ at $k$ playing an individual of trait $y$ at $\ell$ receives $a^{k\ell}_{xy}$ (indices $1 = S$, $2 = NS$). Assume at least one site can propagate its offspring throughout the population, so the chain has a unique stationary distribution; let $\langle x_S \rangle$ be the stationary mean frequency of $S$.

Then

$$\langle x_S \rangle = \frac12 + \frac{\delta}{2}\sum_{k,\ell=1}^N \Big( K^{k\ell}_1\big(a^{k\ell}_{11} - a^{k\ell}_{22}\big) + K^{k\ell}_2\big(a^{k\ell}_{12} - a^{k\ell}_{21}\big)\Big) + O(\delta^2),$$

with structure coefficients

$$K^{k\ell}_1 = \frac{1}{2u}\sum_{i,j=1}^N \pi^{\mathrm{mut}}_i\, m^k_{ji}\Big( -(\phi_{ik} + \phi_{i\ell}) + (1-u)(\phi_{jk} + \phi_{j\ell}) + u \Big),$$

$$K^{k\ell}_2 = \frac{1}{2u}\sum_{i,j=1}^N \pi^{\mathrm{mut}}_i\, m^k_{ji}\Big( -(\phi_{ik} - \phi_{i\ell}) + (1-u)(\phi_{jk} - \phi_{j\ell}) \Big),$$

where $\pi^{\mathrm{mut}}$ is the mutation-weighted reproductive value, $\phi_{ij}$ is the neutral stationary probability that $i$ and $j$ are identical by state ($\phi_{ii} = 1$), and $m^k_{ji} = \partial e_{ji}/\partial F_k$ at neutrality is the marginal effect of $k$'s fecundity on the probability that $j$ replaces $i$. $S$ is favoured by weak selection iff the first-order term is positive.

For a symmetric game ($a^{k\ell}_{xy} = a_{xy}$ for every interacting pair $(k,\ell)$ and $0$ otherwise), let $K_1$ and $K_2$ be the sums of $K^{k\ell}_1$ and $K^{k\ell}_2$ over interacting pairs; when $K_2 > 0$ the condition becomes the sigma rule $\sigma a_{11} + a_{12} > a_{21} + \sigma a_{22}$ with $\sigma = K_1/K_2$; this gives an explicit recipe for $\sigma$ in terms of demographic quantities. Location-dependent payoffs arise for example from "ff-goods": a producer at $i$ with $w_i$ neighbours splits a benefit $b$ and cost $c$ among them, so $a^{ij}_{11} = b/w_j - c/w_i$, $a^{ij}_{12} = -c/w_i$, $a^{ij}_{21} = b/w_j$, $a^{ij}_{22} = 0$, which is asymmetric unless the graph is regular.

## Depends on

- [Mutation-weighted reproductive value](mutation-weighted-reproductive-value.md)

## Proof sketch

The proof writes $d\langle x_S\rangle/d\delta = (d\langle x_S\rangle/dF)(dF/d\delta)$. Expanding $e_{ij} = e^\circ_{ij} + \delta\sum_k m^k_{ij}U_k + O(\delta^2)$ shows that the first-order change in the mean frequency is a sum over replacement events ($j$ replaces $i$), weighted by $\pi^{\mathrm{mut}}_i$, of expected payoffs to $k$ conditioned on $j$ or $i$ carrying $S$; these neutral expectations are linear in pair and triple trait probabilities, which reduce for two traits to identity-by-state probabilities $\phi$. The terms divided by $u$ have finite limits as $u \to 0$, because without mutation all individuals eventually become identical by state. Computing the $N(N-1)/2$ values $\phi_{ij}$ from a linear recursion over one time step is the main cost, so the coefficients are computable in time polynomial in $N$ (Eqs. (4)–(5) of the source; the source also treats any finite number of traits).

## Sources

- A. McAvoy, J. Wakeley, "Evaluating the structure-coefficient theorem of evolutionary game theory", Proceedings of the National Academy of Sciences of the USA (2022), <https://doi.org/10.1073/pnas.2119656119> (PMC9282417).
