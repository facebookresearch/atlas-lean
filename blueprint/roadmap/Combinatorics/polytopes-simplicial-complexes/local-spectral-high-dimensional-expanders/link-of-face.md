# Link of a face in a weighted complex

Let $X$ be a pure $d$-dimensional complex weighted by $\Pi_d$, and let $\tau \in X(i)$ with $-1 \le i \le d-2$. The **link** of $\tau$ is the pure $(d-i-1)$-dimensional complex

$$
X_\tau = \{\, \sigma \setminus \tau \;:\; \sigma \in X,\ \sigma \supseteq \tau \,\},
$$

weighted by the conditional distribution $\Pi^{\tau}_{d-i-1}(\sigma \setminus \tau) \propto \Pi_d(\sigma)$ over top faces $\sigma \supseteq \tau$. The **underlying graph** of $X_\tau$ is its $1$-skeleton $(X_\tau(0), X_\tau(1))$ with edge weights $\Pi^{\tau}_1$; its random-walk operator $M_\tau$ moves from a vertex $u$ to a neighbour $v$ with probability proportional to the weight of the edge $\{u, v\}$. The link of the empty face $\emptyset \in X(-1)$ is $X$ itself.

## Depends on

- [Pure weighted simplicial complexes and their face distributions](pure-weighted-complex.md)

## Sources

- H. Garland, "p-adic curvature and the cohomology of discrete subgroups of p-adic groups", Annals of Mathematics 97 (1973) 375-423.
- I. Oppenheim, "Local spectral expansion approach to high dimensional expanders Part I: Descent of spectral gaps", Discrete & Computational Geometry 59 (2018) 293-330, arXiv:1709.04431.
- I. Dinur, T. Kaufman, "High dimensional expanders imply agreement expanders", FOCS (2017), ECCC TR17-089.
