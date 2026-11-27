# Fixation time of a strongly beneficial allele across colonies

Let $\underline X(t) = (X_1,\dots,X_d) \in [0,1]^d$ be the frequencies of a beneficial allele in $d$ colonies, solving the interacting Wright–Fisher diffusions

$$dX_i = \Big(\alpha X_i(1-X_i) + \mu\sum_{j} b(i,j)(X_j - X_i)\Big)dt + \sqrt{\rho_i^{-1}X_i(1-X_i)}\,dW_i,$$

with selection coefficient $\alpha > 0$, migration coefficient $\mu > 0$, an irreducible backward migration matrix $b$ with equilibrium weights $\rho_1,\dots,\rho_d$ (relative colony sizes), and forward rates $a(i,j) = \rho_j b(j,i)/\rho_i$. The fixation probability from $\underline x$ is $\big(1 - e^{-2\alpha\sum_i x_i\rho_i}\big)/\big(1 - e^{-2\alpha}\big)$. Conditioning on fixation gives the $h$-transformed system $\underline X^*$ with drift $\alpha X_i^*(1-X_i^*)\coth\big(\alpha\sum_j X_j^*\rho_j\big)$ in place of $\alpha X_i(1-X_i)$; its entrance laws from $\underline 0$ are mixtures of $d$ extremal ones, the solution *with founder in colony* $\iota$. Let $T_{\mathrm{fix}} = \inf\{t : \underline X^*(t) = \underline 1\}$.

Let $G$ be the graph on colonies with edges $\{(i,j) : a(i,j) > 0\}$ and $\Delta_\iota$ the number of steps a stepwise percolation started at $\iota$ needs to reach all colonies. Let $S_{\mathcal J^\iota}$ be the time at which all colonies are infectious in the random epidemic on $\{0,1,2\}^d$ started with colony $\iota$ infected, in which an infected colony becomes infectious exactly one time unit after infection and an uninfected colony $j$ is infected at rate $2\sum_k\rho_k a(k,j)\mathbf 1\{\text{colony } k \text{ infectious}\}$.

**Theorem.** For the solution with founder in colony $\iota$, as $\alpha \to \infty$:

1. if $\mu \in \Theta(\alpha)$, then $\dfrac{\alpha}{\log\alpha}T_{\mathrm{fix}} \to 2$ in probability;
2. if $\mu \in \Theta(\alpha^\gamma)$ with $\gamma \in [0,1]$, then $\dfrac{\alpha}{\log\alpha}T_{\mathrm{fix}} \to 2 + (1-\gamma)\Delta_\iota$ in probability;
3. if $\mu = 1/\log\alpha$, then $\dfrac{\alpha}{\log\alpha}T_{\mathrm{fix}} \Rightarrow 1 + S_{\mathcal J^\iota}$ in distribution.

So a sweep that takes $2\log\alpha/\alpha$ in an unstructured population is slowed by an extra $(1-\gamma)\log\alpha/\alpha$ per migration step when migration is weaker than selection, and by a random epidemic time when migration is of order $1/\log\alpha$.

## Expansion

In one colony the conditioned frequency spends $\sim\log\alpha/\alpha$ rising to a small level $\varepsilon$, time $O(1/\alpha)$ crossing to $1-\varepsilon$, and $\sim\log\alpha/\alpha$ completing fixation. With migration $\mu \approx \alpha^\gamma$, a colony near fixation sends migrants at rate $\approx\alpha^\gamma$, and a new colony needs about $(1-\gamma)\log\alpha/\alpha$ to grow its first established beneficial lineage; colonies are therefore conquered in successive waves along $G$, giving the deterministic epidemic. When $\mu = 1/\log\alpha$, migrant arrival is itself random on the $\log\alpha/\alpha$ time scale. The proof combines a moment dual of the conditioned process (a structured ancestral selection graph) with time reversal of a structured coalescent in equilibrium.

## Sources

- Andreas Greven, Peter Pfaffelhuber, Cornelia Pokalyuk, Anton Wakolbinger, "The fixation time of a strongly beneficial allele in a structured population", *Electronic Journal of Probability* 21 (2016), <https://doi.org/10.1214/16-EJP3355>; preprint arXiv:1402.1769, <https://doi.org/10.48550/arXiv.1402.1769>. Numbering of the arXiv version: Section 2 (model, fixation probability, conditioned system, Theorem 1, Definition of the auxiliary epidemic processes, Theorem 2), Section 3 (ancestral selection graph, Proposition 3.1).
