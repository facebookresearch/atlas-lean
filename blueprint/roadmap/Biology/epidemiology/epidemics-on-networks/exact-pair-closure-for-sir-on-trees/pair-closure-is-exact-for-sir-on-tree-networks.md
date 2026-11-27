# Pair closure is exact for the stochastic SIR model on tree networks

**Model.** $P$ individuals form a transmission network with rates $T_{ij}\ge0$ (infection passes from $j$ to $i$ at rate $T_{ij}$ while $j$ is infectious and $i$ susceptible); individual $i$ recovers at rate $\gamma_i$; all events are Poisson. Write $\langle S_i\rangle,\langle I_i\rangle$ for the probabilities that $i$ is susceptible or infectious, $\langle A_iB_j\rangle$ for pair probabilities and $\langle A_iB_jC_k\rangle$ for triples. The exact (unclosed) individual-level equations are

$$\dot{\langle S_i\rangle}=-\sum_jT_{ij}\langle S_iI_j\rangle,\qquad \dot{\langle I_i\rangle}=\sum_jT_{ij}\langle S_iI_j\rangle-\gamma_i\langle I_i\rangle,$$

$$\dot{\langle S_iI_j\rangle}=\sum_{k\ne i}T_{jk}\langle S_iS_jI_k\rangle-\sum_{k\ne j}T_{ik}\langle I_kS_iI_j\rangle-(T_{ij}+\gamma_j)\langle S_iI_j\rangle,$$

$$\dot{\langle S_iS_j\rangle}=-\sum_{k\ne j}T_{ik}\langle I_kS_iS_j\rangle-\sum_{k\ne i}T_{jk}\langle S_iS_jI_k\rangle.$$

**Theorem.** Assume the underlying undirected graph of the network is a tree and the initial condition is a pure state (one of the $3^P$ configurations with probability $1$). Then for all $t\ge0$

$$\langle S_j\rangle\langle S_iS_jI_k\rangle=\langle S_iS_j\rangle\langle S_jI_k\rangle\quad(j\in N_i,\ k\in N_j,\ k\ne i),\qquad \langle S_i\rangle\langle I_kS_iI_j\rangle=\langle I_kS_i\rangle\langle S_iI_j\rangle\quad(j,k\in N_i,\ j\ne k),$$

where $N_i$ is the set of nodes with a link towards $i$. Hence the triple closure $\langle A_iB_jC_k\rangle=\langle A_iB_j\rangle\langle B_jC_k\rangle/\langle B_j\rangle$ is exact, and the closed pair-based system obtained from it reproduces the expected epidemic exactly; the expected population time series are $\sum_i\langle S_i\rangle$ and $\sum_i\langle I_i\rangle$.

More generally, $\langle\psi_W^A\rangle\langle\psi_X^B\rangle=\langle\psi_Y^C\rangle\langle\psi_Z^D\rangle$ for every "compatible" pair of subsystem-state pairs on a tree, the identities above being the special cases used for closure. The result extends to mixed initial conditions in which individuals' initial states are independent, but not to correlated initial conditions. It also extends beyond trees: if every independent segment of the **reduced representation** (the network with all routes that cannot carry infection, given the initial state, removed) is a tree, the pair system on the reduced representation is exact.

## Depends on

- [Epidemics on networks](../README.md)

## Expansion

The probability of any subsystem state obeys a linear forward equation (Theorem 2.1 of the source) in which, besides the subsystem's own transitions, infection enters from outside neighbors through generated larger subsystems. On a tree, a susceptible node $j$ separates the network: conditioning on $j$ being susceptible at time $t$ means no infection has passed through $j$, so the histories of the two branches meeting at $j$ are driven by disjoint sets of independent Poisson clocks and initial states, and are conditionally independent given $S_j$. This conditional independence is exactly the closure identity. The proof makes it rigorous by showing that both sides of each compatible-pair identity satisfy the same linear differential equations with the same initial values (equal at $t=0$ because the initial state is pure), so their difference vanishes for all time. For non-tree graphs the closure fails because a cycle lets the two branches at $j$ interact through other paths.

## Sources

- K. J. Sharkey, I. Z. Kiss, R. R. Wilkinson, P. L. Simon, "Exact equations for SIR epidemics on tree graphs", arXiv (2012). Section 1 (equations (0.3), closure (0.2), Theorem 1.1), Theorem 2.1, Section 3 (Theorem 3.1 and Corollary 3.1), Section 4 (reduced representation, Theorem 4.1). <https://doi.org/10.48550/arXiv.1212.2172>. Published version: Bulletin of Mathematical Biology 77(4) (2015), 614–645, <https://doi.org/10.1007/s11538-013-9923-5>; locators above refer to the arXiv version.
