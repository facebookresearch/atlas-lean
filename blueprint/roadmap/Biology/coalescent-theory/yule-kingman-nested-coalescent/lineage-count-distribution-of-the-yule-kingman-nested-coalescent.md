# Lineage-count distribution of the Yule–Kingman nested coalescent

**Model.** A sample consists of individuals from $s$ species. Backward in time, species merge in pairs as a Kingman-type process on species in which each species merges with another uniformly chosen species at constant rate $c > 0$ (the reversed Yule tree), and, within each species, every pair of individual lineages coalesces independently at rate $1$ (Kingman's coalescent). When two species merge, their individual lineages are pooled. Let $K_n(t)$ be the number of blocks at time $t$ of Kingman's coalescent started from $n$ lineages, and $N_k(t)$ the number of lineages in species $k$.

**Theorem (recursive distributional equation).** For every $c > 0$ there is a unique distribution $\mu_c^*$ on $\{1, 2, \dots\}$ such that, for independent $W, W_1, W_2 \sim \mu_c^*$ and $Y \sim \mathrm{Exp}(c)$ independent of them,

$$W \overset{d}{=} K_{W_1+W_2}(Y),$$

where $K_{W_1+W_2}$ is an independent Kingman coalescent started from $W_1 + W_2$ lineages and run for time $Y$.

**Theorem (convergence).** Start from $s$ species with arbitrary positive (possibly infinite) initial lineage counts. For fixed $m$, let $\tau_m^s$ be the time at which the number of species drops from $m$ to $m-1$. As $s \to \infty$, the numbers of lineages $N_{k_1}, \dots, N_{k_m}$ in the $m$ surviving species just before $\tau_m^s$ are asymptotically independent and each converges in law to $\mu_c^*$. Moreover, if $1 \ll m_j \ll s_j$, the average number of lineages per surviving species converges in probability to the mean $\sum_i i\,\mu_c^*(\{i\})$.

**Theorem (explicit solution at $c = 1$).**

$$\mu_1^*(\{i\}) = \frac{2i-1}{3^i}, \qquad i = 1, 2, \dots,$$

so that at $c = 1$ the mean number of lineages per species is $\sum_i i(2i-1)/3^i = 9/4$.

## Expansion

Just before two species merge, each carries a lineage count that is the outcome of its own subtree's history; after the merger the pooled $W_1 + W_2$ lineages coalesce under Kingman's coalescent for an exponential waiting time until the next species merger involving this species, which is exactly the RDE. Existence and uniqueness use monotonicity of the induced map $F_c$ on distributions, invariance of a suitable class $\mathcal S_1$ of distributions, and analysis of the associated generating-function ODE near $x = 1$ (where the Kingman coming-down-from-infinity behaviour produces the boundary layer). For $c = 1$ the generating function of $(2i-1)/3^i$ is checked to satisfy the transformed equation. The Yule–Kingman model is the $\Lambda = \delta_0$ case of the more general Yule–$\Lambda$ nested coalescent.

## Sources

- T. Gui, "The Yule–Kingman nested coalescent: distribution of the number of lineages", arXiv:2312.12179 (2023), Theorems 1–3 (Section 1), Lemmas 4–10 (Section 2), Lemma 11 and Theorem 12 (Section 3), <https://doi.org/10.48550/arXiv.2312.12179>.
