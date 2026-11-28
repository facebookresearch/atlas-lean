# Finite Dirichlet-mixture filtering of the Fleming–Viot diffusion

**Model.** The population type distribution $X_t$ on a type space $\mathbb Y$ is a neutral Fleming–Viot diffusion with parent-independent mutation $Af(x) = \frac{\theta}{2}\int [f(z) - f(x)]\,\nu_0(dz)$, parameter $\alpha = \theta\nu_0$, reversible with respect to the Dirichlet process law $\Pi_\alpha$, started from $X_0 \sim \Pi_\alpha$. At times $t_0 < t_1 < \dots < t_p$ one observes samples $\mathbf Y_j = (Y_{t_j,i})_i$ that are i.i.d. from $X_{t_j}$ given $X_{t_j}$; let $y^*_1, \dots, y^*_K$ be the distinct observed types and $\mathbf n_j \in \mathbb Z_+^K$ the multiplicities at time $t_j$.

**Theorem.**
1. *(Update.)* $\mathcal L(X_{t_0} \mid \mathbf Y_0) = \Pi_{\alpha + \sum_k n_{0,k}\delta_{y^*_k}}$; more generally, if the predictive law is $\sum_{\mathbf m \in \mathbf M} w_{\mathbf m}\Pi_{\alpha + \sum_k m_k \delta_{y^*_k}}$, then after observing $\mathbf Y_j$ it is a mixture over $\mathbf M + \mathbf n_j$ with weights proportional to $w_{\mathbf m}$ times the Dirichlet-process marginal likelihood of $\mathbf n_j$ given $\mathbf m$.
2. *(Propagation.)* If $\mathcal L(X_{t_{j-1}} \mid \mathbf Y_{0:j-1}) = \sum_{\mathbf m \in \mathbf M} w_{\mathbf m}\Pi_{\alpha + \sum_k m_k\delta_{y^*_k}}$ with $\mathbf M$ finite, then

$$\mathcal L(X_{t_j} \mid \mathbf Y_{0:j-1}) = \sum_{\mathbf n \in L(\mathbf M)} \tilde w_{\mathbf n}\, \Pi_{\alpha + \sum_k n_k \delta_{y^*_k}}, \qquad \tilde w_{\mathbf n} = \sum_{\mathbf m \in \mathbf M,\ \mathbf n \le \mathbf m} w_{\mathbf m}\, p_{\mathbf m, \mathbf n}(t_j - t_{j-1}),$$

where $L(\mathbf M) = \{\mathbf n : \mathbf n \le \mathbf m \text{ for some } \mathbf m \in \mathbf M\}$ and $p_{\mathbf m,\mathbf n}(s)$ are transition probabilities of a pure-death process on multiplicity vectors.
3. *(Filtering and smoothing.)* For every $t$, $\mathcal L(X_t \mid \mathbf Y_{0:T})$ is a finite mixture $\sum_{\mathbf m \in \mathbf M} w_{\mathbf m}\Pi_{\alpha + \sum_k m_k \delta_{y^*_k}}$; the smoothing law combines the past filter and the future (backward) information through explicit double sums over past and future mixture indices.

## Depends on

- [Fleming–Viot diffusion with parent-independent mutation](../../fleming-viot-processes/fleming-viot-diffusion-with-parent-independent-m.md)
- [Dirichlet-process stationary law of the Fleming–Viot process](../../fleming-viot-processes/dirichlet-process-stationary-law.md)

## Proof idea

Dirichlet processes are conjugate to i.i.d. sampling, giving the update step. The Fleming–Viot diffusion is dual to a Kingman-type death process on the counts of observed types (lineages are lost by coalescence and by mutation to fresh types drawn from $\nu_0$), so propagating a Dirichlet process with atoms of masses $\mathbf m$ over time $s$ yields a mixture of Dirichlet processes whose atom masses $\mathbf n \le \mathbf m$ are distributed as the dual death process. Iterating keeps the mixture finite, so filtering is exact with finitely many components, which supports nonparametric inference on populations with infinitely many types (e.g. allele or strain frequencies).

## Sources

- F. Ascolani, S. Damato and M. Ruggiero, "An R package for nonparametric inference on dynamic populations with infinitely many types", Journal of Computational Biology 31 (2024), 1305–1311, <https://doi.org/10.1089/cmb.2024.0600>. Numbering as in the supplementary material of the preprint arXiv:2409.15539v1, <https://arxiv.org/abs/2409.15539v1>: Theorem 1.1 (finite mixture), Propositions 2.1–2.3 (update, propagation, update) and Proposition 3.1 (smoothing).
- O. Papaspiliopoulos, M. Ruggiero and D. Spanò, "Conjugacy properties of time-evolving Dirichlet and gamma random measures", Electronic Journal of Statistics 10 (2016), 3452–3489, <https://doi.org/10.1214/16-EJS1194>, Proposition 3.1 (propagation).
- F. Ascolani, A. Lijoi and M. Ruggiero, "Smoothing distributions for conditional Fleming–Viot and Dawson–Watanabe diffusions", Bernoulli 29 (2023), 1410–1434, <https://doi.org/10.3150/22-BEJ1504>, Theorem 1.1 (finite-mixture smoothing).
