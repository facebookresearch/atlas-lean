# Supermodular upper bound on infections under edge deletion in the discrete-time networked SIR model

The discrete-time mean-field networked SIR (D-SIR) model on $n$ nodes evolves the infection and removal probabilities $\mathbf{x}(t), \mathbf{r}(t) \in [0,1]^n$ by

$$
\mathbf{x}(t+1) = \mathbf{x}(t) + (I - X(t) - R(t))\,B\,\mathbf{x}(t) - D\,\mathbf{x}(t), \qquad \mathbf{r}(t+1) = \mathbf{r}(t) + D\,\mathbf{x}(t),
$$

where $B = (B_{ij})$ holds the infection rates of edges $(j,i)$, $D = \operatorname{diag}(D_i)$ the healing rates, and $X(t) = \operatorname{diag}(\mathbf{x}(t))$, $R(t) = \operatorname{diag}(\mathbf{r}(t))$. Assume $D_i < 1$ and $\sum_j B_{ij} < 1$. For a set $P$ of deleted edges, let $B_{-P}$ set $B_{ij} = 0$ for $(j,i) \in P$, let $M_{-P} = I - D + (I - X(0) - R(0))B_{-P}$, and let $\sigma(P) = \|\mathbf{m}^* - \mathbf{m}(0)\|_1$ be the number of new infections, where $\mathbf{m} = \mathbf{x} + \mathbf{r}$ and $m^*_i = \sup_t m_i(t)$.

**Theorem.** Let $Q$ be a candidate set of deletable edges and suppose $\|M_{-P}\| < 1$ for all $P \subseteq Q$. Then

$$
\sigma(P) \le \hat\sigma(P) = \mathbf{1}^\top (M_{-P} + D - I)(I - M_{-P})^{-1}\,\mathbf{x}(0),
$$

and $\hat\sigma$ is a monotone (non-increasing) supermodular function of $P \subseteq Q$. The norm condition holds whenever there is $\epsilon > 0$ with $(1 - x_i(0) - r_i(0)) \sum_j B_{ij} \le D_i - \epsilon$ for all $i$; then $\|M_{-P}\| \le 1 - \epsilon$, $\hat{\mathbf{x}} = 0$ is the unique equilibrium and the system is exponentially stable.

## Expansion

Since susceptible fractions only decrease, $\mathbf{x}(t+1) \le M_{-P}\,\mathbf{x}(t)$ entrywise, so the total infection mass is dominated by the Neumann series $\sum_t M_{-P}^t \mathbf{x}(0) = (I - M_{-P})^{-1}\mathbf{x}(0)$, and the new infections per step are $(M_{-P} + D - I)\mathbf{x}(t)$. Deleting edges lowers entries of $M_{-P}$, and each entry of the Neumann series is a sum of products of entries, which gives supermodularity. Minimizing a supermodular surrogate under a cardinality constraint admits greedy algorithms with approximation guarantees, whereas exact minimization of $\sigma$ is NP-hard.

## Sources

- Yuhao Yi, Liren Shan, Philip E. Paré and Karl H. Johansson, *Edge Deletion Algorithms for Minimizing Spread in SIR Epidemic Models*, arXiv:2011.11087, section "Supermodularity for the D-SIR Model" (upper-bound theorem and sufficient condition for exponential stability). <https://doi.org/10.48550/arXiv.2011.11087> Published version: SIAM Journal on Control and Optimization 60 (2022) S246–S273, <https://doi.org/10.1137/20m1377011>.
