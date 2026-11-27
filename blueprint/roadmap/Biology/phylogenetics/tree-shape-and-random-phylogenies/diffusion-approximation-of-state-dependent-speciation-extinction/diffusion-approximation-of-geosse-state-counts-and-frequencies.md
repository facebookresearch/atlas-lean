# Diffusion approximation of GeoSSE state counts and frequencies

**Setting.** In a cladogenetic state-dependent speciation–extinction (ClaSSE) model, and in particular the geographic GeoSSE model with ranges $S$ (non-empty subsets of regions) and within-region speciation $w_i$, local extinction $e_i$, dispersal $d_{ij}$ and between-region speciation $b^s_t$ rates, let $N_i(t)$ be the number of lineages in state $i \in S$ and $N = \sum_i N_i$. Let $\mathbb P_i^+$ and $\mathbb P_i^-$ be the total rates at which $N_i$ increases or decreases by one (summing all anagenetic and cladogenetic events that create or remove a lineage in state $i$).

**Lemma (counts).** Treating the $N_i$ as a diffusion, the infinitesimal mean and variance of $N_i$ are

$$\mu_i = \mathbb P_i^+ - \mathbb P_i^-, \qquad \sigma_i^2 = \mathbb P_i^+ + \mathbb P_i^-.$$

**Lemma (frequencies).** For the state frequency $\Pi_i = N_i/N$, Itô's transformation formula gives

$$\mu_{\Pi_i} = \frac1N\Big(\mu_i - \frac{\sigma_i^2}{N}\Big) + \frac{\Pi_i}{N}\sum_{j\in S}\Big(-\mu_j + \frac{\sigma_j^2}{N}\Big), \qquad \sigma^2_{\Pi_i} = \Big(\frac{\sigma_i}{N}\Big)^2(1 - 2\Pi_i) + \Big(\frac{\Pi_i}{N}\Big)^2\sum_{j\in S}\sigma_j^2,$$

which is undefined at total extinction ($N = 0$).

**Lemma (inverse problem for stationary frequencies).** Rate parameters compatible with prescribed stationary frequencies $\hat\Pi_i$ must satisfy the balance conditions $\hat{\mathbb P}_i^+ = \hat{\mathbb P}_i^-$ at the stationary state, together with an ordering of the total per-state event rates consistent with the ordering of the $\hat\Pi_i$, positivity of all rates and $\sum_i\Pi_i(0) = 1$; for two-region GeoSSE this system can be solved for the stationary frequencies analytically.

## Proof sketch

Each event changes a state count by $\pm 1$, so a Gaussian (diffusion) approximation of the jump process matches drift and variance to the up- and down-rates, as for birth–death processes. Frequencies are a smooth function of counts, so their drift and diffusion coefficients follow from Itô's formula for $g(N_i, N) = N_i/N$. Simulating these diffusions forward in time reproduces state-frequency trajectories of tree-based ClaSSE simulations at a fraction of the cost and links rate parameters directly to observed stationary range frequencies. The BiSSE and MuSSE models are special cases.

## Sources

- Albert C. Soewongsono and Michael J. Landis, "A Diffusion-Based Approach for Simulating Forward-in-Time State-Dependent Speciation and Extinction Dynamics", *Bulletin of Mathematical Biology* 86 (2024), 101, <https://doi.org/10.1007/s11538-024-01337-6>. Preprint version: arXiv:2402.00246 (2024), Theorem 1 and Lemmas 1–5 (Section 2), <https://doi.org/10.48550/arXiv.2402.00246>.
