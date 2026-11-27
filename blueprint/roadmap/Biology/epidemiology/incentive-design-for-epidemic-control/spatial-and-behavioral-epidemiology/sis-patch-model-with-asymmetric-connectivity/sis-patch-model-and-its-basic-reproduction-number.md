# SIS patch model and its basic reproduction number

Let $\Omega = \{1, \dots, n\}$, $n \ge 2$, be a set of patches. Let $L = (L_{jk})$ be an $n\times n$ connectivity matrix with $L_{jk} \ge 0$ for $j \ne k$ (movement from patch $k$ to patch $j$) and $L_{jj} = -\sum_{k \ne j} L_{kj}$. The SIS patch model is

$$\frac{dS_j}{dt} = d_S\sum_{k\in\Omega} L_{jk}S_k - \frac{\beta_j S_jI_j}{S_j + I_j} + \gamma_j I_j, \qquad \frac{dI_j}{dt} = d_I\sum_{k\in\Omega} L_{jk}I_k + \frac{\beta_j S_jI_j}{S_j + I_j} - \gamma_j I_j, \qquad j \in \Omega,$$

with transmission rates $\beta_j \ge 0$, recovery rates $\gamma_j \ge 0$ and dispersal rates $d_S, d_I > 0$. Assume $L$ is irreducible and quasi-positive (nonnegative off the diagonal), and nonnegative initial data with total population $N = \sum_j (S_j(0) + I_j(0)) > 0$. Then:

1. The total population $\sum_j (S_j(t) + I_j(t)) = N$ is conserved.
2. The spectral bound $s(L) = 0$ is a simple eigenvalue of $L$ with a unique eigenvector $\alpha$ satisfying $\alpha_j > 0$ and $\sum_j \alpha_j = 1$.
3. The model has a unique disease-free equilibrium $(\hat S, 0)$ with $\hat S_j = \alpha_j N$.
4. With $F = \operatorname{diag}(\beta_j)$ and $V = \operatorname{diag}(\gamma_j) - d_I L$, if the $\gamma_j$ are not all zero then $V$ is a nonsingular M-matrix, the basic reproduction number is $R_0 = \rho(FV^{-1})$, and $R_0 - 1$ has the same sign as $s\big(d_I L + \operatorname{diag}(\beta_j - \gamma_j)\big)$. The disease-free equilibrium is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.

Patches with $\beta_j < \gamma_j$ are called low-risk ($H^-$) and those with $\beta_j > \gamma_j$ high-risk ($H^+$). When $L$ is symmetric, $\alpha_j = 1/n$.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Basic reproduction number of the SIS model](../../../sis-epidemic-model/r0-eq.md)

## Expansion

The columns of $L$ sum to zero, so adding all $2n$ equations gives conservation. Perron–Frobenius theory for the irreducible quasi-positive matrix $L$ gives item 2 (Lemma 2.1). A disease-free equilibrium satisfies $L\hat S = 0$, so $\hat S$ is a multiple of $\alpha$, fixed by conservation (Lemma 2.2). Item 4 is the next-generation-matrix construction applied to the linearized infected equations $\dot I = (F - V)I$ (Equation (2.2) and Proposition 2.4).

## Sources

- S. Chen, J. Shi, Z. Shuai, Y. Wu, "Asymptotic profiles of the steady states for an SIS epidemic patch model with asymmetric connectivity matrix", Journal of Mathematical Biology 80 (2020), 2327–2361, <https://doi.org/10.1007/s00285-020-01497-8>.
