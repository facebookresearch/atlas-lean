# Limit theorems for strictly balanced small urn models

An urn holds balls of $d$ colors with configuration $C_n = (C_{n,1},\dots,C_{n,d})$ and total $t_n = \sum_i C_{n,i} > 0$. At step $n$ a ball is drawn uniformly, giving the indicator row vector $\chi_n$ with $P(\chi_n = e_i \mid \mathcal F_{n-1}) = C_{n-1,i}/t_{n-1}$, and the configuration is updated by

$$C_n = C_{n-1} + \chi_n R$$

for a fixed real $d\times d$ replacement matrix $R$ (entries may be negative). Assume:
- (A1) *Tenable*: the replacement rule can always be followed.
- (A2) *Small*: all eigenvalues of $R$ are real, the largest $\lambda_1 = s$ is positive and $s > 2\lambda$ for every other eigenvalue $\lambda$.
- (A3) *Strictly balanced*: the all-ones column vector $e^\top$ is a right eigenvector for $s$ and some left eigenvector for $s$ is a stochastic vector; hence $t_n = t_0 + ns$.
- (A4) *Diagonalizable*: $U^{-1}RU = \operatorname{diag}(\lambda_1 \ge \dots \ge \lambda_d)$ for a real invertible $U$, with columns $u_j$ and rows $v_j$ of $U^{-1}$ normalized so that $u_1 = e^\top$ and $v_1$ is stochastic.

**Theorem.** Under (A1)–(A4),
1. (Strong law) $(ns)^{-1}C_n \to v_1$ almost surely and in $L^r$ for every $r > 0$;
2. (Central limit theorem) $n^{-1/2}(C_n - ns\,v_1) \to N(0,\Sigma)$ in distribution, where

$$\Sigma = \sum_{i,j=2}^d \frac{s\,\lambda_i\lambda_j}{s - \lambda_i - \lambda_j}\,\big(u_i^\top \operatorname{diag}(v_1)\,u_j\big)\, v_i^\top v_j .$$

## Expansion

Work with $Y_n = C_nU$, whose coordinates evolve along the eigen-directions, and the martingale differences $\xi_n = Y_n - E[Y_n\mid\mathcal F_{n-1}]$. Since $E[\chi_n\mid\mathcal F_{n-1}] = C_{n-1}/t_{n-1}$ and $t_\ell = t_0 + \ell s$, coordinate $j$ satisfies $Y_{n,j} = b_{n,0}(j)Y_{0,j} + \sum_k b_{n,k}(j)\,\xi_{k,j}$ with $b_{n,k}(j) = \prod_{\ell=k}^{n-1}(1 + \lambda_j/t_\ell)$, which grows like $(n/k)^{\lambda_j/s}$. For $j \ge 2$ the smallness condition $\lambda_j < s/2$ makes these coordinates $o(n)$ almost surely and of order $\sqrt n$; the first coordinate is deterministic, $Y_{n,1} = t_n$, giving the strong law. A martingale central limit theorem with a conditional Lindeberg condition, applied to the weighted sums of $\xi_k$, gives the normal limit; the covariance comes from $E[\chi_n^\top\chi_n\mid\mathcal F_{n-1}] = \operatorname{diag}(C_{n-1}/t_{n-1}) \to \operatorname{diag}(v_1)$. The proofs adapt the martingale approach of Bai and Hu to replacement matrices with negative entries, and the covariance agrees with Janson's branching-process result.

## Sources

- K. P. Choi, G. Kaur, T. Wu, "On asymptotic joint distributions of cherries and pitchforks for random phylogenetic trees", Journal of Mathematical Biology (2021), Eqs. (1)–(7), assumptions (A1)–(A4), Theorems 1–2 and Sect. 7, <https://doi.org/10.1007/s00285-021-01667-2>, PMCID PMC8460594.
