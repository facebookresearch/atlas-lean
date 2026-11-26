# Time-dependent isolation–migration model fitted to coalescence rates

Consider two populations with time-dependent diploid sizes $N_1(t), N_2(t)$ and a symmetric, time-dependent per-lineage migration rate $m(t)$, time $t$ measured backward in generations. The ancestry of two sampled lineages is a time-inhomogeneous Markov chain on the states $S_{11}$ (both in population 1), $S_{12}$ (one in each), $S_{22}$ (both in population 2) and the absorbing state "coalesced", with generator

$$Q(t) = \begin{pmatrix} -2m - c_1 & 2m & 0 & c_1 \\ m & -2m & m & 0 \\ 0 & 2m & -2m - c_2 & c_2 \\ 0 & 0 & 0 & 0 \end{pmatrix}, \qquad c_i(t) = \frac{1}{2N_i(t)},$$

with $m = m(t)$. Let $P_{\mathrm{IM}}(t \mid s_0)$ be the density of the coalescence time from start $s_0 \in \{S_{11}, S_{12}, S_{22}\}$, obtained from the transition matrices of $Q$ (products of matrix exponentials when $N_1, N_2, m$ are piecewise constant).

**MSMC-IM.** Given within- and cross-population coalescence-rate functions $\lambda_{11}(t), \lambda_{22}(t), \lambda_{12}(t)$ estimated by a sequentially Markovian coalescent method, form the empirical densities $P_{\mathrm{MSMC}}(t \mid S_{ab}) = \lambda_{ab}(t)\exp(-\int_0^t \lambda_{ab}(t')\,dt')$. Choose piecewise-constant $(N_1, N_2, m)$ on time segments $t_1 < \dots < t_{n_T}$ to minimize

$$\chi^2 = \sum_{i=1}^{n_T}\Bigl[\sum_{s_0}\frac{\bigl(P_{\mathrm{IM}}(t_i \mid s_0) - P_{\mathrm{MSMC}}(t_i \mid s_0)\bigr)^2}{P_{\mathrm{MSMC}}(t_i \mid s_0)} + \beta_1\int_0^\infty m + \beta_2\Bigl(\frac{N_1(t_i) - N_2(t_i)}{N_1(t_i) + N_2(t_i)}\Bigr)^2\Bigr].$$

This re-parametrizes the triple $(\lambda_{11}, \lambda_{12}, \lambda_{22})$ as $(N_1, N_2, m)$. The **cumulative migration probability**

$$M(t) = 1 - \exp\Bigl(-\int_0^t m(t')\,dt'\Bigr)$$

is nondecreasing from $0$ to at most $1$, constant on intervals of isolation ($m = 0$). It is read as the fraction of ancestry already merged by time $t$. A clean split at time $T$ appears as a single pulse of $m$ near $T$. Admixture of a fraction $\alpha$ from a lineage that diverged at $T_a > T$ gives a plateau of $M$ at about $1 - \alpha$ between $T$ and $T_a$.

## Remarks

From $S_{11}$ either lineage may migrate (rate $m$ each, total $2m$) or the pair may coalesce at rate $c_1$. From $S_{12}$ either lineage may move into the other's population, and no coalescence is possible. Solving the Kolmogorov forward equations along the segments gives $P_{\mathrm{IM}}$. The re-parametrization is over-specified once the populations are fully mixed: any large $m$ then gives the same rates, which is why the $\beta_1$ and $\beta_2$ penalties are needed and why $m$ is reported only while $M(t) < 0.999$. A population split corresponds in this parametrization to an instantaneous transfer of lineages, hence a migration pulse. A deep archaic branch merges into the extant trunk only at its own divergence, which leaves $M$ flat at $1 - \alpha$ in between. Numerically $M(t)$ tracks the relative cross-coalescence rate $2\lambda_{12}/(\lambda_{11} + \lambda_{22})$, while giving it a migration-based interpretation.

## Depends on

- [MSMC2: pairwise composite likelihood under the sequentially Markovian coalescent](../two-locus-coalescent/multiple-sequentially-markovian-coalescent/msmc2-pairwise-composite-likelihood.md)

## Sources

- K. Wang, I. Mathieson, J. O'Connell and S. Schiffels, "Tracking human population structure through time from whole genome sequences", PLoS Genetics 16 (2020), e1008552, Results ("Estimating pairwise coalescence rates with MSMC2 and fitting an IM model", "Evaluating MSMC-IM with simulated data") and Materials and methods ("MSMC2", "MSMC-IM model"), <https://doi.org/10.1371/journal.pgen.1008552>, PMCID PMC7082067.
