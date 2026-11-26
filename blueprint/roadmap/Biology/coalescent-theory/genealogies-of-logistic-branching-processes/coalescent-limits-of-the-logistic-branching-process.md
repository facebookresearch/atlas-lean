# Coalescent limits of the logistic branching process

**Model.** Fix a carrying-capacity parameter $K$. Individuals carry neutral types in a compact Polish space $E$ that mutate according to a Markov process with generator $\mathcal{Q}_K$. Each individual gives birth at rate $b$ to a random number $\ell \ge 1$ of children with law $(p_\ell)_{\ell\ge1}$, children inheriting the parent's type, and dies at the density-dependent rate $d + \frac{c}{K}N^K(t)$, where $N^K(t)$ is the population size and $b, c, d > 0$. Write $m = \sum_\ell \ell p_\ell$, $m^{(2)} = \sum_\ell \ell^2 p_\ell$, assume $bm - d > 0$, and set $n_* = (bm - d)/c$, so the population fluctuates around $Kn_*$.

**Ancestral partition process.** Sample $k$ individuals at time $r_K T$, where $r_K = K$, $K^{\alpha-1}$ or $1$ according to the regime below, and let $\Pi^K(t)$ be the partition of $\{1,\dots,k\}$ in which $i \sim j$ when samples $i$ and $j$ share an ancestor at time $r_K T - t$.

**Theorem.** In each regime, with the population started near its quasi-equilibrium as required for the corresponding forward-in-time limit:
1. **Finite variance**, $\sum_\ell p_\ell\,\ell^{2+\delta} < \infty$ for some $\delta > 0$: $(\Pi^K(Kt))_{t\in[0,T]}$ converges in distribution to Kingman's coalescent with effective population size
$$N_e = \frac{n_*}{b\,(m + m^{(2)})}.$$
2. **$\alpha$-stable offspring**, $p_\ell \sim p_0\,\ell^{-1-\alpha}$ with $\alpha \in (1,2)$: $(\Pi^K(K^{\alpha-1}t))_{t\in[0,T]}$ converges to the Beta$(2-\alpha,\alpha)$-coalescent, the $\Lambda$-coalescent with
$$\Lambda(du) = \frac{b\,p_0}{n_*^{\alpha-1}}(1-u)^{\alpha-1}u^{1-\alpha}\,du.$$
3. **Neveu-type offspring**, $p_\ell\,\ell^2 \to p_0$: with no time rescaling, $(\Pi^K(t))_{t\in[0,T]}$ converges to the Bolthausen–Sznitman coalescent, $\Lambda(du) = b\,p_0\,du$.

**Spatial version.** If $E$ is the flat torus, the rescaled motions $r_K\mathcal{Q}_K$ converge to Brownian motion and the initial type distribution is the stationary law of the limiting $(\Lambda, \Delta)$-Fleming–Viot process, then in each regime the spatial ancestral partition process (lineages with their locations) converges to the corresponding Brownian spatial $\Lambda$-coalescent.

## Depends on

- [Lookdown construction of the logistic branching process](lookdown-construction-of-the-logistic-branching-process.md)

## Expansion

Competition holds the total size near $Kn_*$, so on the genealogical time scale the population behaves like a fixed-size Cannings-type population whose reproduction law is inherited from the branching mechanism. With finite offspring variance pairwise mergers dominate, at a rate set by the offspring second moment over the equilibrium size, giving Kingman's coalescent. Heavy-tailed offspring numbers produce single births that replace a positive fraction of the population, which is the Beta-coalescent mechanism; the borderline tail $\ell^{-2}$ gives Bolthausen–Sznitman on the original time scale, because the population size is then of order $K\log K$. The genealogy is read off a lookdown representation of the population, whose forward limits are the lookdown representations of the corresponding Fleming–Viot processes, and the sample genealogy converges with them.

## Sources

- Ruairi Garrett and Julio Ernesto Nava Trejo, "Genealogies under logistic growth", arXiv:2509.05217 (2025), Definitions 1.1 and 1.6, Theorems 1.7 and 1.8 and Lemma 2.2 (the forward-in-time limits it uses are recalled as Theorem 1.3 from earlier work), <https://doi.org/10.48550/arXiv.2509.05217>.
