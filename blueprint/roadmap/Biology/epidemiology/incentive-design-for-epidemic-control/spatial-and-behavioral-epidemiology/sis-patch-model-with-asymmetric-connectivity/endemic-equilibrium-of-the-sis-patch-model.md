# Endemic equilibrium of the SIS patch model and its small-dispersal limit

In the [SIS patch model](sis-patch-model-and-its-basic-reproduction-number.md), assume $\beta_j, \gamma_j \ge 0$, $d_S, d_I > 0$, $L$ irreducible and quasi-positive, $N > 0$, and that the low-risk set $H^- = \{j : \beta_j < \gamma_j\}$ and the high-risk set $H^+ = \{j : \beta_j > \gamma_j\}$ are both nonempty with $\Omega = H^- \cup H^+$. If $R_0 > 1$, then:

1. The model has exactly two nonnegative equilibria: the disease-free equilibrium $(\alpha N, 0)$ and a unique endemic equilibrium $(S, I)$ with $I_j > 0$ for every $j$.
2. As $d_S \to 0$ with $d_I$ fixed, the endemic equilibrium converges to a limiting disease-free equilibrium $(S^*, 0)$, and $S^*_j > 0$ for every low-risk patch $j \in H^-$.

The paper also gives a necessary and sufficient condition (in terms of an auxiliary problem with $d = d_I/d_S$) under which $S^*_j = 0$ on every high-risk patch, in which case $S^*_j = N(\alpha_j - \alpha_j^*)/\sum_{k\in H^-}(\alpha_k - \alpha_k^*)$ on $H^-$ for a vector $\alpha^*$ determined by the model.

## Depends on

- [SIS patch model and its basic reproduction number](sis-patch-model-and-its-basic-reproduction-number.md)
- [Monotonicity and limits of R0 in the infected dispersal rate](monotonicity-and-limits-of-r0-in-the-infected-dispersal-rate.md)
- [Endemic equilibrium of the SIS model](../../../sis-epidemic-model/is-solution-const-endemic.md)

## Expansion

At equilibrium, setting $\kappa$ by conservation, the equilibrium is written as $S_j = \kappa\check S_j$, $I_j = \kappa\check I_j/d_I$, where $\check I$ is the unique strongly positive solution of a reduced nonlinear system depending on $d = d_I/d_S$ (Theorem 3.3); uniqueness follows from monotonicity of that system. As $d_S \to 0$, $\kappa \to 0$ and $I_j \to 0$ (Lemma 3.4), while the susceptibles accumulate where infection cannot persist, in particular on every low-risk patch (Theorem 3.9). This extends the symmetric-$L$ results of Allen et al. (2007) and partially resolves their open problem on the $S$-profile.

## Sources

- S. Chen, J. Shi, Z. Shuai, Y. Wu, "Asymptotic profiles of the steady states for an SIS epidemic patch model with asymmetric connectivity matrix", Journal of Mathematical Biology 80 (2020), 2327–2361, <https://doi.org/10.1007/s00285-020-01497-8>.
