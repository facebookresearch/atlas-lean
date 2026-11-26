# Dice processes characterise partially exchangeable consistent Markov chains

**Setting.** Let $[d] = \{1, \dots, d\}$ be a set of types (colonies, islands, active/dormant states) and $\Delta_{d-1}^d$ the set of $d \times d$ stochastic matrices $U = (u_{ij})$. A $[d]^\infty$-valued process $Y$ is *partially exchangeable* if its law is invariant under finite permutations that preserve the initial type partition $\{l : Y_l(0) = i\}_{i \in [d]}$.

**Definition (dice process).** Given nonnegative rates $(a_{ij})_{i \ne j}$ and a measure $\nu$ on $\Delta_{d-1}^d$ with $\int \sum_i (1 - u_{ii})\,\nu(dU) < \infty$, the $n$-dice process is the Markov chain on $[d]^n$ with rates
$$\tilde\gamma^{(n)}_{x,y} = a_{ij} + \int u_{ij}\prod_{m \ne l} u_{x_m x_m}\,\nu(dU) \quad \text{if } y = x + (j-i)e_l,\ x_l = i,$$
$$\tilde\gamma^{(n)}_{x,y} = \int \prod_{m=1}^n u_{x_m y_m}\,\nu(dU) \quad \text{for all other } y \ne x.$$
Particles move one at a time from $i$ to $j$ at rate $a_{ij}$, and in coordinated events a random matrix $U \sim \nu$ is drawn and every particle at $i$ independently jumps to $j$ with probability $u_{ij}$. The $n$-dice processes are consistent and extend to a $[d]^\infty$-valued process.

**Theorem.** Let $Y$ be a $[d]^\infty$-valued process whose restriction to the first $n$ coordinates is a Markov chain for each $n$. Then $Y$ is partially exchangeable if and only if it is a dice process; it is exchangeable iff in addition $Y(0)$ is exchangeable. Equivalently, an array of block-transition rates $\gamma_{b,K}$ (rate at which, out of $b_i$ particles of type $i$, $k_{ij}$ move to $j$) is consistent iff
$$\gamma_{b,K} = \int \prod_{i,j} u_{ij}^{k_{ij}}\,\nu(dU) + \sum_i\sum_{j \ne i} a_{ij}\,\mathbf{1}\{K = \mathrm{diag}(b) - E_{ii} + E_{ij}\}.$$

**Proposition (de Finetti measure process and duality).** The empirical type frequencies $R^{(n)}_i(t) = \#\{l \le n : Y_l(t) = i\}/n$ converge in $D([0,T], \Delta_{d-1})$ to the unique strong solution of
$$dR_i = \sum_{j \ne i}(a_{ji}R_j - a_{ij}R_i)\,dt + \int \sum_{j \ne i}\big(u_{ji}R_j(t-) - u_{ij}R_i(t-)\big)\,N(dt, dU),$$
with $N$ Poisson of intensity $dt \otimes \nu$. If $\sum_{j\ne i}(a_{ij} - a_{ji}) = 0$ for all $i$ and $\nu$ is supported on doubly stochastic matrices, $R$ is moment dual to a block-counting chain on $\mathbb{N}_0^d$ that moves single lineages $i \to j$ at rate $b_i a_{ji}$ and makes coordinated block moves driven by the transposed matrices $U^{\mathsf T}$.

## Expansion

Consistency of the rates says that adding one particle of type $j$ and summing over its possible destinations leaves the rates of the original block unchanged, $\gamma_{b,K} = \sum_l \gamma_{b + e_j, K + E_{jl}}$. This is a multi-index Hausdorff moment problem: for fixed $i$, the sequences behave like mixed moments of the rows of a random stochastic matrix, so a de Finetti/Hausdorff argument represents the coordinated part as an integral against $\nu$, and the remaining single-particle jumps (the part that survives at zero moments) are the constants $a_{ij}$. As $n \to \infty$ the frequency process inherits drift from the $a_{ij}$ and jumps $R \mapsto U^{\mathsf T}R$ from $\nu$.

## Sources

- Adrián González Casanova, Noemi Kurt, Imanol Nuñez Morales and José Luis Pérez, "Partially exchangeable Markov chains and characterisation of multitype Lambda-coalescents", arXiv:2511.05435 (2025), Section 2 (Definition of dice processes, Theorem 2.1, Propositions 2.1–2.3), <https://doi.org/10.48550/arXiv.2511.05435>.
