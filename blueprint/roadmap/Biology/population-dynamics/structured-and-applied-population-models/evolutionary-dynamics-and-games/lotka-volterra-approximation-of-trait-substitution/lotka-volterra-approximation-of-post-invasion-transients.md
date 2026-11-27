# Lotka–Volterra approximation of post-invasion transients

**Setting.** A community contains phenotypes $s' = (s_1, \dots, s_{N+1})$ (residents $s_1, \dots, s_N$ and a mutant $s_{N+1}$ that arose from $s_N$ with $|s_{N+1} - s_N| = \varepsilon_\mu$) with densities $n' = (n_1, \dots, n_{N+1})$ obeying

$$\frac{dn_i}{dt} = n_i\,F(s_i; s'; n'),$$

where the fitness-generating function $F$ is smooth in all arguments and invariant under exchanging phenotypes together with their densities, so that nearly identical phenotypes act almost as one. Phenotypes closer than a threshold distance $\varepsilon = \varepsilon_\mu/\rho_\mu$ are grouped into clusters, each represented by an **approximate phenotype** $s_a$ carrying the cluster's total density $m_a$; clusters are assumed well separated, and before the invasion the approximate phenotypes sit at a stable equilibrium $\breve m$.

**Theorem.**
1. (Lotka–Volterra approximation) If during the transient after the invasion the approximate-phenotype densities stay close to their pre-invasion values, $\|m - \breve m\| \le \varepsilon C_m$, then

$$F(s_i; s'; n') = \breve F_i + \sum_{j=1}^{N+1} a_{ij}(n_j - \breve n_j) + R_i, \qquad |R_i| \le \varepsilon^2 C,$$

with $a_{ij} = \partial F(s_i; s'; n')/\partial n_j$ at the pre-invasion state, so that

$$\frac{dn_i}{dt} = n_i\Big(\gamma_i + \sum_{j=1}^{N+1}a_{ij}n_j + R_i\Big), \qquad \gamma_i = \breve F_i - \sum_j a_{ij}\breve n_j,$$

a Lotka–Volterra system up to a remainder of order $\varepsilon^2$.
2. (Approximability) The closeness condition holds when within-cluster differences are small relative to the leading eigenvalue of the community Jacobian at $\breve m$, both when all approximate densities are large and, with a refined analysis, when some are small.
3. (Invasion implies substitution) For a monomorphic resident (and, by extension, for several residents) and a mutant with positive invasion fitness away from evolutionary singular points, the approximating Lotka–Volterra system has the mutant replacing its parent while the rest of the community stays near its equilibrium.

## Depends on

- [Classification of adaptive dynamics singular strategies](../../../classification-of-adaptive-dynamics-singular-str/README.md)
- [Replicator and Lotka–Volterra equivalence](../../../replicator-and-lotka-volterra-equivalence/README.md)

## Expansion

Rewrite the fitness of each phenotype as a function of the approximate densities $m'$; by exchangeability and smoothness the result is again smooth, so a first-order Taylor expansion around $\breve m$ with remainder bounded by the second derivative times $\|m' - \breve m'\|^2$ gives part 1 once the densities move only $O(\varepsilon)$. Part 2 controls that movement: a stable hyperbolic equilibrium with leading eigenvalue bounded away from $0$ absorbs perturbations of size $O(\varepsilon)$ from the within-cluster heterogeneity, while small populations need higher-order terms because their eigenvalues approach zero. In the Lotka–Volterra approximation, a mutant and its parent are nearly equivalent competitors, and the sign of the invasion fitness, of order $\varepsilon$, decides the competitive outcome on a slow time scale of order $1/\varepsilon$, giving substitution. This is the rigorous underpinning of the trait-substitution sequence used to derive the canonical equation of adaptive dynamics.

## Sources

- H. C. Ito, U. Dieckmann, J. A. J. Metz, "Lotka–Volterra approximations for evolutionary trait-substitution processes", Journal of Mathematical Biology 80(7) (2020) 2141–2226, axioms and Eq. (2.3), Proposition 1, Lemmas 1–2, Theorem 1 (Eqs. (3.4a), (3.6a)–(3.6b)) and the invasion-implies-substitution application, <https://doi.org/10.1007/s00285-020-01493-y>, PMCID PMC7250815.
