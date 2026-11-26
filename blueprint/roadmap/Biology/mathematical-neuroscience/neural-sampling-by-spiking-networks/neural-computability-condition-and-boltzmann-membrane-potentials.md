# Neural computability condition and Boltzmann membrane potentials

Let $p$ be a probability distribution on $\{0, 1\}^K$ with $p(z) > 0$ for every $z$, where $z_k = 1$ means that neuron $k$ has spiked within the last $\tau$ time steps. A network satisfies the neural computability condition (NCC) for $p$ if the membrane potential of each neuron equals the log-odds of its variable given all others,

$$u_k(t) = \log \frac{p(z_k = 1 \mid z_{\setminus k})}{p(z_k = 0 \mid z_{\setminus k})}.$$

For a Boltzmann distribution

$$p(z) = \frac{1}{Z} \exp\Bigl( \sum_{i,j} \tfrac12 W_{ij} z_i z_j + \sum_i b_i z_i \Bigr)$$

with real weights satisfying $W_{ij} = W_{ji}$ and $W_{ii} = 0$, the NCC holds exactly for point neurons with the linear membrane potential

$$u_k(t) = b_k + \sum_{i=1}^{K} W_{ki} z_i(t),$$

so $b_k$ acts as an intrinsic excitability and $W_{ki}$ as the amplitude of a rectangular postsynaptic potential of duration $\tau$ from neuron $i$.

## Expansion

The conditional odds equal $p(z^{k \to 1}) / p(z^{k \to 0})$, the ratio of the joint probabilities of the two states that differ only in coordinate $k$, so the normalizing constant cancels. In the exponent, the terms that change with $z_k$ are $b_k z_k$ and the two copies $\tfrac12 W_{ki} z_k z_i + \tfrac12 W_{ik} z_i z_k$ for each $i \ne k$; symmetry merges them into $W_{ki} z_k z_i$ and the zero diagonal removes $z_k^2$, which leaves the log-odds $b_k + \sum_i W_{ki} z_i$. Distributions with higher-order interactions satisfy the NCC only with neurons whose potentials are nonlinear in their inputs, for example through dendritic nonlinearities.

## Sources

- Buesing L, Bill J, Nessler B, Maass W. Neural dynamics as sampling: a model for stochastic computation in recurrent networks of spiking neurons. *PLoS Computational Biology* 7:e1002211 (2011), Results, "Neural sampling" and "Neural sampling in discrete time", Theorem 1, equations (4)–(10). DOI <https://doi.org/10.1371/journal.pcbi.1002211>. PMCID PMC3207943.
