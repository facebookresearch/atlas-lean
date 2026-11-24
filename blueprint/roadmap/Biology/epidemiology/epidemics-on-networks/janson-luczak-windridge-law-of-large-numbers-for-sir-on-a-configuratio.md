# Law of large numbers for the SIR epidemic on a random graph with given degrees

Let $G^*$ be the configuration-model multigraph on $n$ vertices with a given degree sequence $(d_i)$, and run the Markovian SIR epidemic on it: each infective vertex transmits along each of its edges at rate $\beta$ and recovers at rate $\rho$. Janson, Luczak and Windridge (2014) assume conditions (D1)–(D6): the initial fractions of susceptible, infective and recovered vertices converge, with a positive susceptible fraction (D1); the degree of a random susceptible vertex converges in distribution to $(p_k)$ with finite positive mean $\lambda$ (D2), and its mean converges to $\lambda$ (D3); the average degrees of all vertices and of each class converge (D4); the maximum degree of the initially infective vertices is $o(n)$ (D5); and $p_1 > 0$ or $\rho > 0$ or $\mu_R > 0$ (D6). Theorem 2.6 states, when the limiting fraction $\mu_I$ of initially infective half-edges is positive: there is a unique $\theta_\infty \in (0, 1)$ with $h_I(\theta_\infty) = 0$; the equation $\dot\theta_t = -\beta\theta_t p_I(\theta_t)$, $\theta_0 = 1$, has a unique solution, which decreases to $\theta_\infty$; and the rescaled numbers of susceptible, infective and recovered vertices and half-edges converge in probability, uniformly on $[0, \infty)$, to explicit functions of $\theta_t$, so that the final fraction of susceptibles escaping infection converges to $v_S(\theta_\infty)$. Theorem 2.7 gives the same conclusions for the uniform simple graph with the given degrees under an additional condition (G1), and Theorem 2.9 treats a vanishing initial fraction of infectives, where an outbreak of size of order $n$ requires the source's $R_0 > 1$.

## Expansion

1. The model: the configuration model, the Markovian SIR dynamics on half-edges, and conditions (D1)–(D6).
2. The time change, the functions $h_I$, $p_I$ and $v_S$, and the existence and uniqueness of $\theta_\infty$.
3. The limiting equations (2.19)–(2.22) and their solution in terms of $\theta_t$.
4. Uniform convergence in probability (Theorem 2.6), and the transfer to simple graphs (Theorem 2.7).
5. The small-initial-infection regime and its threshold (Theorem 2.9), as a separate statement.

## Sources

- S. Janson, M. Luczak and P. Windridge, Law of large numbers for the SIR epidemic on a random graph with given degrees, Random Struct. Algorithms 45 (2014), 726–763, conditions (D1)–(D6) and Theorems 2.6, 2.7, 2.9. <https://arxiv.org/abs/1308.5493>
