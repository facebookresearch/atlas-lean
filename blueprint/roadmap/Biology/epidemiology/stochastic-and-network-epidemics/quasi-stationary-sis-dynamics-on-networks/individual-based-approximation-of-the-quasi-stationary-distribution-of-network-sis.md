# Individual-based approximation of the quasi-stationary distribution of network SIS

**Setting.** In the Markovian SIS model on a strongly connected network with $N$ nodes, node $j$ infects a susceptible neighbour $i$ at rate $T_{ij}$, and node $i$ recovers at rate $\gamma_i$. The disease-free state is absorbing, so there is no endemic steady state. Long-lived endemic behaviour is described by the *quasi-stationary distribution* (QSD), the limiting law conditioned on non-extinction. Closing the QSD equations under the assumption that node states are independent gives the following problem. Find feasible $\langle Y\rangle^*\in[0,1]^N$, with $\langle X_i\rangle^*=1-\langle Y_i\rangle^*$, solving

$$0=\sum_jT_{ij}\langle X_i\rangle\langle Y_j\rangle-\gamma_i\langle Y_i\rangle+\frac{\langle Y_i\rangle\sum_j\gamma_j\langle Y_j\rangle\prod_{k\neq j}\langle X_k\rangle}{1-\prod_k\langle X_k\rangle},$$

and set $\langle I_i\rangle^{\mathrm{QSD}}_{\mathrm{approx}}=\langle Y_i\rangle^*/\big(1-\prod_k\langle X_k\rangle^*\big)$ and $[I]^{\mathrm{QSD}}_{\mathrm{approx}}=\sum_i\langle I_i\rangle^{\mathrm{QSD}}_{\mathrm{approx}}$. The last term of the equation is the *conditioning correction*: it re-injects the probability mass lost to extinction, in proportion to current infection.

**Theorem.**

1. The associated ODE system, whose right-hand side is the expression above, is positively invariant in $[0,1]^N$, so integrating it to equilibrium gives a feasible solution.
2. On a strongly connected $K$-regular graph with homogeneous rates, the approximation is feasible with $\langle I_i\rangle^{\mathrm{QSD}}_{\mathrm{approx}}\in(0,1)$, the same for every node, and $[I]^{\mathrm{QSD}}_{\mathrm{approx}}\in(1,N)$.
3. On any strongly connected network, if a solution with $\langle I_i\rangle^{\mathrm{QSD}}_{\mathrm{approx}}\in(0,1)$ exists, then $[I]^{\mathrm{QSD}}_{\mathrm{approx}}\in(1,N)$. So the expected number infected is bounded below by $1$, as for the true QSD. This holds both above and below the epidemic threshold, unlike standard mean-field models, which predict zero prevalence below threshold.

## Proof sketch

The exact QSD satisfies a linear eigen-equation on the $2^N-1$ transient states. Rescaling by the mass remaining in the transient states turns it into stationarity equations for node marginals, with an extra term proportional to the total recovery flux out of states with exactly one infective. This extra term comes from the extinction events that conditioning removes. The independence closure keeps the network structure, scales linearly in $N$, and gives at least one infective on average because conditioning on survival requires one. A pair-based closure adds correlations between neighbours and improves accuracy, particularly near threshold and on heterogeneous networks.

## Sources

- Christopher E. Overton, Robert R. Wilkinson, Adedapo Loyinmi, Joel C. Miller and Kieran J. Sharkey, "Approximating Quasi-Stationary Behaviour in Network-Based SIS Dynamics", *Bulletin of Mathematical Biology* 84 (2022), 4, <https://doi.org/10.1007/s11538-021-00964-7>. Preprint version: arXiv:2208.05901 (2022), Section 3 (QSD), Section 4 (individual-based and pair-based approximations), Theorem 1 (feasibility and lower bound), appendices (invariance and existence of the endemic steady state), <https://doi.org/10.48550/arXiv.2208.05901>.
