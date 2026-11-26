# Acyclic threshold-linear networks have a globally stable fixed point

**Threshold-linear network.** $\mathrm{TLN}(W,b)$ on nodes $[n]=\{1,\dots,n\}$ evolves by

$$\dot x_i=-x_i+\Big[\sum_{j=1}^nW_{ij}x_j+b_i\Big]_+,\qquad i\in[n],$$

with $[\cdot]_+=\max\{\cdot,0\}$ and constant inputs $b_i$. Each node is excitatory or inhibitory; $\delta_{j,I}=1$ if $j$ is inhibitory and $0$ otherwise, and an edge $i\leftarrow j$ of a directed graph $G$ carries weight $W_{ij}=w_{ij}(-1)^{\delta_{j,I}}$ with $w_{ij}>0$ ($W_{ij}=0$ off $G$).

**Theorem 1.** If $G$ contains no directed cycle, then for any positive weights and any inputs $b$, $\mathrm{TLN}(W,b)$ has a unique globally asymptotically stable fixed point. In particular, no acyclic network of excitatory and inhibitory threshold-linear populations can oscillate, whatever the signs and strengths of its connections.

## Expansion

An acyclic digraph admits a topological layering: a partition $\sigma_1,\dots,\sigma_k$ of $[n]$ with no edges inside a layer and every edge into $\sigma_i$ coming from $\sigma_1\cup\dots\cup\sigma_{i-1}$. Nodes of $\sigma_1$ receive no network input, so $\dot x_i=-x_i+[b_i]_+$ and they converge exponentially to $[b_i]_+$. Once the earlier layers have (asymptotically) settled, each node of the next layer is driven by an asymptotically constant input through the Lipschitz map $[\cdot]_+$, so it converges to a unique limit as well; induction over layers gives global convergence to a unique fixed point. The result isolates connectivity as the source of oscillation by excluding intrinsic node dynamics, plasticity and delays.

## Sources

- Zang J, Liu S, Helson P, Kumar A, "Structural constraints on the emergence of oscillations in multi-population neural networks" (2024), equation (1) and Theorem 1 with its proof, <https://doi.org/10.7554/elife.88777>, PMCID PMC10937037.
