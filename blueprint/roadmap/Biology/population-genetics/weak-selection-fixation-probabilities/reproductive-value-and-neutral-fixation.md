# Reproductive values and neutral fixation probability

Consider a finite population of $N$ sites occupied by alleles $A$ (coded $1$) or $B$ (coded $0$),
with state space $\mathbb{B}^N = \{0, 1\}^N$ and absorbing monoallelic states
$\mathbf{A} = (1, \dots, 1)$ and $\mathbf{B} = (0, \dots, 0)$.
At each step, a replacement event $(R, \alpha)$ — consisting of a subset $R \subseteq \{1, \dots, N\}$
of replaced sites and a parentage map $\alpha : R \to \{1, \dots, N\}$ — occurs with probability
$p_\delta(R, \alpha \mid x)$ depending smoothly on a selection intensity $\delta \ge 0$.
Let $e_{ij}(x)$ be the expected number of offspring at site $j$ produced by site $i$ in state $x$,
and $e_{ij}^\circ$ its value under neutral drift ($\delta = 0$), which is independent of $x$.

Assume the neutral process has positive probability of reaching $\mathbf{A}$ or $\mathbf{B}$ from
every state and that the site-to-site replacement graph is irreducible. Then the **reproductive values**
$\pi = (\pi_1, \dots, \pi_N)$ are the unique solution to

$$\sum_{j=1}^N e_{ij}^\circ \pi_j = \sum_{j=1}^N e_{ji}^\circ \pi_i \quad (1 \le i \le N), \qquad \sum_{i=1}^N \pi_i = 1.$$

For any initial configuration $\xi \in \mathbb{B}^N$, the reproductive-value-weighted frequency
$\hat\xi := \sum_{i=1}^N \pi_i \xi_i$ is a martingale under neutral drift, and the neutral
fixation probability of $A$ starting from $\xi$ equals

$$\rho_A^\circ(\xi) = \hat\xi.$$

## Sources

- A. McAvoy and B. Allen, "Fixation probabilities in evolutionary dynamics under weak selection", Journal of Mathematical Biology 82 (2021), 14, <https://doi.org/10.1007/s00285-021-01567-5>. (Section 2, Eqs. 12a–12b.)
