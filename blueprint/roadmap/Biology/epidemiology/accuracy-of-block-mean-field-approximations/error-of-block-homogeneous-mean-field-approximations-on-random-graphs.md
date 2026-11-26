# Error of block-homogeneous mean-field approximations on stochastic block model graphs

**Graphs.** Vertices $\{1,\dots,N\}$ are partitioned into $K$ blocks $I_k$ of sizes $N_k = \pi_k N \ge c_{\mathrm{block}}N$. Each edge $ij$ ($i \in I_k$, $j \in I_l$) is present independently with probability $\rho w_{kl}$, with bounded weights and $m \le \sum_{k,l} w_{kl}\pi_k\pi_l \le M$; the expected average degree is $d = \Theta(N\rho)$, assumed $\ge N^{\alpha}$ for some $\alpha \in (0,1]$.

**Dynamics.** Each vertex has a state in a finite set $\mathcal{S}$. A vertex in state $s$ jumps to $s'$ spontaneously at rate $q_{s\to s'}$, and a neighbor $j$ in state $\tilde s$ moves it from $s$ to $s'$ at rate $q_{\tilde s;s\to s'}\,a_{ij}/(N\rho)$. This covers SIS and SIR (e.g. $q_{I;S\to I} = \beta$, $q_{I\to R} = \gamma$). Initial states are conditionally independent given the graph. Let $\bar\xi_{k,s}(t) = N_k^{-1}\sum_{i\in I_k}\mathbf{1}\{\text{vertex } i \text{ in state } s \text{ at } t\}$.

**Approximations.** NIMFA (the N-intertwined mean-field approximation) closes the vertex-level equations by independence:
$$\dot z_{i,s} = \sum_{s'} q_{s'\to s}z_{i,s'} + \sum_{s',\tilde s} q_{\tilde s;s'\to s}\, z_{i,s'}\,\frac{1}{N\rho}\sum_j a_{ij} z_{j,\tilde s}.$$
Replacing $a_{ij}$ by its mean and assuming block homogeneity gives the block-homogeneous mean-field approximation (BHMFA)
$$\dot x_{k,s} = \sum_{s'} q_{s'\to s}x_{k,s'} + \sum_{s',\tilde s} q_{\tilde s;s'\to s}\sum_l w_{kl}\pi_l\, x_{k,s'}x_{l,\tilde s}, \qquad x_{k,s}(0) = \frac{1}{N_k}\sum_{i\in I_k}\Pr(\text{vertex } i \text{ starts in } s).$$

**Theorem.** Fix a time horizon $t$, and write $\|X\| = \mathbb{E}[X^2]^{1/2}$.
1. (General initial conditions.) For every process in the class,
$$\sup_{0\le\tau\le t}\ \max_{k,s}\ \big\|\bar\xi_{k,s}(\tau) - x_{k,s}(\tau)\big\| = O\!\left(\frac{1}{\sqrt d}\right).$$
2. (Tightness.) For the catalyst process ($q_{c;a\to b} = 1$) on an Erdős–Rényi graph with density $\rho < 1 - c$, graph-dependent conditionally independent initial conditions can be chosen so that the error at time $1$ is $\Theta(1/\sqrt d)$.
3. (Near-homogeneous initial conditions.) If, outside an event of superpolynomially small probability, $N^{-1}\sum_k\sum_{i\in I_k}(z_{i,s}(0) - \bar z_{k,s}(0))^2 \le c_0/d$ for all $s$, then the error is $O\big(\max\{1/d,\ 1/\sqrt N\}\big)$.
4. (Tightness.) For the degree process on an Erdős–Rényi graph with all vertices starting in state $a$, the error at time $1$ is $\Theta\big(\max\{1/d, 1/\sqrt N\}\big)$.

## Expansion

Kurtz's law of large numbers on the complete graph gives $O(1/\sqrt N)$ errors; on random graphs the topology adds an extra error that depends on how initial conditions correlate with the realized graph. The proof compares the stochastic process to quenched NIMFA (conditional variance $O(1/d)$ by degree concentration) and quenched NIMFA to BHMFA using spectral concentration $\|B - \hat B\|_2 = O(1/\sqrt d)$ of the normalized adjacency matrix $B = A/(N\rho)$ around its block mean. When initial conditions are arbitrary functions of the graph, they can align with the fluctuation $B - \hat B$ and realize the full $1/\sqrt d$; when they are nearly constant on blocks, first-order fluctuations cancel and only second-order terms $1/d$ and sampling noise $1/\sqrt N$ remain.

## Sources

- P. Dionigi, D. Keliger, "The effects of initial conditions on the accuracy of mean-field approximations of Markov processes on large random graphs", arXiv:2506.12872 (2025), Section 2 (graph model, NIMFA and BHMFA equations, Corollary 1), Theorems 1–4 (Section 3), <https://doi.org/10.48550/arXiv.2506.12872>.
