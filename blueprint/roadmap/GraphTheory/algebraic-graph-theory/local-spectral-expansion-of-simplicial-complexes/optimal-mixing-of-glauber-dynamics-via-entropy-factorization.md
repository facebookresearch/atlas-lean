# Chen-Liu-Vigoda: optimal mixing of Glauber dynamics in the uniqueness regime

Let $\Delta \ge 3$ be an integer and $b, \eta > 0$ reals. Let $G = (V, E)$ be an $n$-vertex graph of maximum degree at most $\Delta$ and $\mu$ the Gibbs distribution of a spin system on $G$ with spins in $[q]$. Assume that:

- **total connectivity**: for every nonempty $S \subseteq V$ and every feasible boundary condition $\tau$ on $V \setminus S$, the feasible configurations on $S$ under $\tau$ are connected by moves that change one vertex at a time;
- **bounded marginals**: for every $\Lambda \subsetneq V$, every feasible $\tau$ on $\Lambda$, every $v \notin \Lambda$ and every spin $i$ feasible at $v$ under $\tau$, $\mu(\sigma_v = i \mid \sigma_\Lambda = \tau) \ge b$;
- **spectral independence**: $\mu$ is $\eta$-spectrally independent, that is, under every such pinning the largest eigenvalue of the pairwise influence matrix is at most $\eta$.

Then the Glauber dynamics for $\mu$ satisfies the modified log-Sobolev inequality with constant $1/(C_1 n)$, where $C_1 = (\Delta/b)^{O(\eta/b^2 + 1)}$, and its mixing time is $T_{\mathrm{mix}}(\varepsilon) = (\Delta/b)^{O(\eta/b^2 + 1)} \cdot O(n \log(n/\varepsilon))$; for $n$ large enough $\mu$ satisfies approximate tensorization of entropy with constant $C_1$. Total connectivity cannot be dropped: if the spins at the two endpoints of each edge of a perfect matching are constrained to agree, influences stay bounded and feasible marginals are at least $1/2$, yet single-site updates cannot move at all. The hypotheses hold for the hard-core model with fugacity $\lambda \le (1 - \delta) \lambda_c(\Delta)$ and for antiferromagnetic two-spin systems that are up-to-$\Delta$ unique with gap $\delta$, giving mixing time $C(\Delta, \delta)\, n \log n$.

## Proof sketch

Upgrade spectral independence to entropy decay: by local-to-global arguments for entropy (rather than variance) on the simplicial complex of partial assignments, prove uniform block factorization of entropy for heat-bath block dynamics that update a uniformly random set of $\Theta(n)$ vertices. Bounded degree and bounded marginals then compare block factorization with single-site factorization at a constant loss, giving approximate tensorization of entropy, hence the modified log-Sobolev constant $\Omega(1/n)$ and the $O(n \log n)$ mixing time.

## Depends on

- [Spectral independence of a distribution on the hypercube](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/spectral-independence.md)

## Proof depends on

- [Spectral independence implies polynomial mixing of Glauber dynamics](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/spectral-independence-glauber.md)

## Sources

- Zongchen Chen, Kuikui Liu, Eric Vigoda, "Optimal mixing of Glauber dynamics: entropy factorization via high-dimensional expansion", STOC (2021); arXiv:2011.02075 (Assumption 1.8, Definitions 1.9 and 1.11, Theorems 1.1, 1.2, 1.12 and 2.9).
