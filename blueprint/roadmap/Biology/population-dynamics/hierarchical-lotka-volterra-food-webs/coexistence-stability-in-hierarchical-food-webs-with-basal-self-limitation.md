# Coexistence stability in hierarchical food webs with basal self-limitation

**Model.** $N$ species are strictly ordered by trophic rank; species $k$ can eat any species $i<k$ (an acyclic, hierarchical food web, allowing omnivory). In the reduced mean-field model only the basal species $1$ grows and self-limits, with net growth $B_1=b_1-d_1>0$ and self-limitation $a_{11}>0$; each consumer $k\ge2$ dies at rate $d_k>0$ and converts prey with efficiency one:
$$\dot x_1 = x_1\Big(B_1 - a_{11}x_1 - \sum_{j>1}a_{1j}x_j\Big), \qquad \dot x_k = x_k\Big(-d_k + \sum_{i<k}a_{ik}x_i - \sum_{j>k}a_{kj}x_j\Big),\ k\ge2.$$
For a subset $A\ni1$ of surviving species, $M_A$ denotes the boundary equilibrium supported on $A$, and $M_0$ the origin.

**Theorem.**

1. If the coexistence state $x^{*}=M_{12\cdots N}$ is feasible (positive), then $V(x)=\sum_k\big(x_k-x_k^{*}-x_k^{*}\ln(x_k/x_k^{*})\big)$ satisfies $\dot V = -a_{11}(x_1-x_1^{*})^2\le0$ in the open orthant, so $x^{*}$ is Lyapunov stable for every $N$, and attracts all interior trajectories whenever the largest invariant subset of $\{x_1=x_1^{*}\}$ is $\{x^{*}\}$.
2. $M_0$ is a saddle with eigenvalues $B_1$ and $-d_2,\dots,-d_N$. Every feasible $M_A$ with $1\in A\subsetneq\{1,\dots,N\}$ is a saddle with exactly $N-|A|$ positive eigenvalues, one for each missing consumer; the coexistence state is the only feasible equilibrium that is Lyapunov stable.
3. For $N=3$ (the omnivory module with links $1\to2$, $1\to3$, $2\to3$), all five equilibria $M_0, M_1, M_{12}, M_{13}, M_{123}$ are feasible iff
$$a_{13}B_1>a_{11}d_3,\quad d_3(a_{11}a_{23}+a_{12}a_{13}) > a_{13}a_{23}B_1 + a_{13}^2d_2,\quad a_{12}a_{23}B_1 + a_{12}a_{13}d_2 > a_{11}a_{23}d_2 + a_{12}^2d_3,$$
and then every interior trajectory converges to $M_{123}$.

## Expansion

The interaction matrix is the sum of $-a_{11}e_1e_1^{\top}$ and an antisymmetric matrix (predation gains equal losses), so the Volterra function's derivative only sees the basal self-limitation. Determinants of the restricted Jacobians have sign $(-1)^{n+1}$ (a Pfaffian squared for odd $n$), which makes the invasion rate of each missing consumer at $M_A$ positive whenever the coexistence state is feasible. Since coexistence is stable but every boundary state is a saddle, extinction in the stochastic model is noise-induced, along paths escaping through these saddles.

## Sources

- V. Nevash, E. Forgoston, M. A. Hsieh, "Noise-induced extinction in hierarchical food webs", arXiv:2611.33569, Section 2 (reduced model), Proposition 1 and Theorem 1; Section 3, Propositions 2–3. <https://doi.org/10.48550/arXiv.2611.33569>
