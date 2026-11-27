# Poaching model with self-employment and its grapheme Wright–Fisher limit

**Finite model.** On graphs with vertex set of size $N$, the *poaching model with self-employment* is the continuous-time Markov chain in which
- for each ordered pair $(v,v')$ of distinct vertices, at rate $1$, $v'$ drops all its edges and connects to $v$ and to every neighbour of $v$ (poaching, i.e. resampling: $v'$ adopts the "type" of $v$);
- for each vertex $v$, at rate $\mu\ge 0$, $v$ deletes all its edges (self-employment, i.e. mutation to a new type).

Started from a graph whose components are complete, components stay complete and correspond exactly to the allelic classes of a Moran model with infinitely-many-alleles mutation at rate $\mu$. The chain is ergodic and its stationary law is the *multivariate Ewens distribution* (MED) $N$-graph: the partition of $[N]$ into complete components with $\nu(j)$ components of size $j$ has probability

$$\pi^N_{\mathrm{MED}}(\nu)=\frac{N!}{\mu(\mu+1)\cdots(\mu+N-1)}\prod_{j=1}^N\frac{\mu^{\nu(j)}}{j^{\nu(j)}\,\nu(j)!}.$$

**Limit object.** A grapheme is an equivalence class of $(\Omega,\tau,\mu,W)$ with a Polish space, a sampling probability measure and a symmetric adjacency map $W:\Omega^2\to\{0,1\}$; convergence means convergence of all sampled subgraph densities $\Phi^{k,A}(\mathfrak{g})=\int\mu^{\otimes k}(dx)\mathbf{1}_A\big((W(x_i,x_j))_{i,j\le k}\big)$. The *GEM-grapheme* is $\Omega=[0,1]$ with Lebesgue measure and a random $W$ whose components are complete and whose component masses have the law of the GEM($\mu$) (equivalently, ranked, Poisson-Dirichlet($\mu$)) frequencies.

**Statements.**
1. *(Martingale problem.)* For an initial grapheme with complete components, the martingale problem for the operator $\Omega_{\mathrm{grapheme}}\Phi^{k,A}(\mathfrak{g})=\int\mu^{\otimes k}(dx)\,(\Omega^k_{\mathrm{adj}}\mathbf{1}_A)\big((W(x_i,x_j))\big)$, where $\Omega^k_{\mathrm{adj}}$ is the generator of poaching and self-employment on $k$ sampled vertices, has a unique solution with continuous paths: the *grapheme-valued Wright-Fisher diffusion with mutation*.
2. *(Convergence.)* If the encoded $N$-graph chains start from graphemes converging to $\mathfrak{g}$, they converge weakly in Skorokhod space to this diffusion started at $\mathfrak{g}$.
3. *(Duality and stationarity.)* Sampled subgraph densities satisfy a Feynman-Kac duality with an adjacency-matrix-valued chain run backward in time, and the GEM-grapheme is the unique stationary distribution of the diffusion; the MED $N$-graphs converge to it.

## Depends on

- [Dirichlet-process stationary law of the Fleming–Viot process](../dirichlet-process-stationary-law.md)

## Expansion

The generator of the finite chain acts on a subgraph density by poaching or isolating one of the $k$ sampled vertices, and the difference between sampling with and without replacement vanishes as $N\to\infty$, giving convergence of generators uniformly in the state. The space of graphemes with complete components is compact, so tightness follows, and uniqueness follows from the duality, which turns subgraph densities at time $t$ into expectations over a finite backward chain that duplicates rows (poaching) and grounds them (mutation). Because the dynamics on component frequencies is exactly the infinitely-many-alleles Moran model and its diffusion limit, the stationary component sizes are GEM/Poisson-Dirichlet distributed, mirroring the stationary law of the neutral Fleming-Viot process.

## Sources

- Andreas Greven, Frank den Hollander, Anton Klimovsky and Anita Winter, "The grapheme-valued Wright–Fisher diffusion with mutation", Theor. Popul. Biol. 158 (2024), 76–88, <https://doi.org/10.1016/j.tpb.2024.04.007>. Numbering follows the arXiv version, arXiv:2308.11598 (2023): Section 2 (poaching model with self-employment, MED $N$-graph, stationary distribution and ergodicity, link to the Moran model), Section 3 (GEM-grapheme definition and convergence of the MED $N$-graph) and Section 4 (well-posed martingale problem theorem, Feynman-Kac duality, stationary distribution), <https://doi.org/10.48550/arXiv.2308.11598>.
