# Equitable-partition reduction of the mean-field network SIRS model with vaccination

**Model.** On an undirected graph $G=(V,E)$ with adjacency matrix $A$, the first-order (independence) closure of the Markovian network SIRS epidemic with infection rate $\beta$ per edge, recovery rate $\delta$, immunity-loss rate $\gamma$ and vaccination rate $\sigma\ge 0$ gives the node-level mean-field equations

$$\dot S_i=-\beta S_i\sum_ja_{ij}I_j+\gamma R_i-\sigma S_i,\qquad \dot I_i=\beta S_i\sum_ja_{ij}I_j-\delta I_i,\qquad \dot R_i=\delta I_i-\gamma R_i+\sigma S_i ,$$

with $S_i+I_i+R_i=1$ forward invariant. The disease-free equilibrium is $I_i=0$, $R_i=\sigma/(\gamma+\sigma)$, and the epidemic threshold for $\tau=\beta/\delta$ is

$$\tau_c=\frac{\gamma+\sigma}{\gamma}\cdot\frac{1}{\lambda_1(A)} .$$

For $\tau\le\tau_c$ the disease-free equilibrium is globally asymptotically stable; for $\tau>\tau_c$ the system is uniformly persistent with a unique endemic equilibrium, which is asymptotically stable if $\delta\ge\sigma$.

**Equitable partitions.** A partition $\pi=\{V_1,\dots,V_n\}$ of $V$ is *equitable* if for all $h,k$ there is an integer $d_{hk}$ such that every $v\in V_h$ has exactly $d_{hk}$ neighbours in $V_k$. Let $\bar S_h,\bar I_h,\bar R_h$ denote cell averages.

**Theorem (invariant reduction).** If $\pi$ is equitable, the set

$$\tilde\Omega=\{S_i=\bar S_h,\ I_i=\bar I_h,\ R_i=\bar R_h\ \text{for all } i\in V_h,\ h=1,\dots,n\}$$

is positively invariant, and on it the $3N$ equations reduce to $3n$ equations driven by the quotient matrix $(d_{hk})$, whose spectral radius equals $\lambda_1(A)$.

**Theorem (regular graphs).** Let $G$ be $d$-regular, $\tau>\tau_c$ and $\delta>\sigma$. Then the endemic equilibrium is asymptotically stable and $\tilde\Omega$ intersected with the interior of the state space (all node states equal, with every probability positive) lies in its domain of attraction.

## Expansion

When all nodes of a cell start with equal probabilities, each node of $V_h$ sees the same weighted infected mass $\sum_kd_{hk}\bar I_k$, so the vector field preserves equality within cells; the endemic equilibrium inherits this symmetry and can be computed from the quotient system. For a regular graph the trivial one-cell partition is equitable, and the reduced system is a single planar SIRS model with contact number $\beta d$, whose phase-plane analysis gives convergence to the endemic point when $\delta>\sigma$. A sufficient eigenvalue condition for global stability imported from the heterogeneous mean-field literature is never met on regular graphs, which motivates this invariant-set route.

## Sources

- Stefania Ottaviano and Stefano Bonaccorsi, "Some aspects of the Markovian SIRS epidemic on networks and its mean-field approximation", arXiv:1912.11287 (2019), Section 3 (Mean-field approximation) and Section 4 (Stability analysis), including the definition of equitable partition, the invariance theorem for cell-homogeneous states and the attractivity theorem for regular graphs, <https://doi.org/10.48550/arXiv.1912.11287>.
