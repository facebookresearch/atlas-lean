# Invariance of the target distribution under absolutely refractory spiking dynamics

Let $p$ satisfy the neural computability condition with membrane potentials $u_k$, and give each neuron an internal state $\zeta_k \in \{0, 1, \dots, \tau\}$ with $z_k = 1$ iff $\zeta_k \ge 1$ (the neuron spiked within the last $\tau$ steps). The single-neuron transition operator $T^k$ changes only $\zeta_k$:

- if $\zeta_k \in \{0, 1\}$, the neuron spikes, $\zeta_k \to \tau$, with probability $\sigma(u_k - \log \tau)$, and otherwise $\zeta_k \to 0$;
- if $\zeta_k \ge 2$, then $\zeta_k \to \zeta_k - 1$ with probability one (absolute refractoriness),

where $\sigma(x) = 1/(1 + e^{-x})$. If $p(z) > 0$ for all $z$, each $T^k$ leaves invariant the joint distribution $p(\zeta)$ of the internal states, the composition $T = T^K \circ \cdots \circ T^1$ is irreducible and aperiodic, and $p(\zeta)$ is its unique invariant distribution, with marginal $p(z)$ on the spike variables. Hence, from any initial state, the spiking network produces samples from $p$ after burn-in.

## Depends on

- [Neural computability condition and Boltzmann membrane potentials](neural-computability-condition-and-boltzmann-membrane-potentials.md)

## Expansion

Fix all other neurons, so $u = u_k$ is constant, and write $s = \sigma(u - \log \tau) = e^{u}/(\tau + e^{u})$. A stationary law $\pi$ of the single-neuron chain satisfies $\pi_\tau = s(\pi_0 + \pi_1)$ and $\pi_{j} = \pi_{j+1}$ for $1 \le j < \tau$, so all refractory states share one mass $x$ with $x(1 - s) = s \pi_0$. The odds of being active are then $\tau x / \pi_0 = \tau s / (1 - s) = e^{u}$, which by the NCC are exactly the conditional odds $p(z_k = 1 \mid z_{\setminus k}) / p(z_k = 0 \mid z_{\setminus k})$; consequently $p(\zeta) = p(z(\zeta))\, \tau^{-\sum_k z_k}$, uniform over the refractory phase of active neurons, is invariant under each $T^k$, and compositions of invariant operators are invariant. Irreducibility uses $p(z) > 0$, which keeps every spike probability strictly between $0$ and $1$. Unlike Gibbs sampling, the chain is not reversible: refractory states are traversed in one direction only, which matches the stereotyped time course of real spikes and postsynaptic potentials.

## Sources

- Buesing L, Bill J, Nessler B, Maass W. Neural dynamics as sampling: a model for stochastic computation in recurrent networks of spiking neurons. *PLoS Computational Biology* 7:e1002211 (2011), Results, "Neural sampling" and "Neural sampling in discrete time", Theorem 1, equations (4)–(10). DOI <https://doi.org/10.1371/journal.pcbi.1002211>. PMCID PMC3207943.
