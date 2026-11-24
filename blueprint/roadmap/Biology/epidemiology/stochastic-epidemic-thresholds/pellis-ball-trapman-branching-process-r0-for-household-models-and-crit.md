# Basic reproduction number for household epidemic models

Pellis, Ball and Trapman (2012) define $R_0$ through the branching process that approximates the early epidemic, with individuals placed in generations by their minimal path length from the initial infective in the epidemic graph: $R_0 = \lim_{n\to\infty}\lim_{N\to\infty} E[X_n(N)]^{1/n}$, where $X_n(N)$ is the number of generation-$n$ individuals in a population of size $N$ (Eq. (2.3)). For a multitype approximating process with mean offspring matrix $M$, $R_0$ is the largest eigenvalue of $M$, which by Perron–Frobenius theory is real, positive and strictly dominant, and the process survives with positive probability if and only if $R_0 > 1$ (Section 2.2). If a perfect vaccine is given uniformly at random, the mean matrix becomes $(1 - p_c)M$, where $p_c$ is the fraction of blocked infectious contacts, so the approximating process is critical exactly when $(1 - p_c)R_0 = 1$, that is $p_c = 1 - 1/R_0$. For the households model the source computes $R_0$ as the largest eigenvalue of an explicit matrix built from the mean numbers of within-household infections per generation (Section 3.2, matrix (3.1)), and it notes that $R_0$ and the household reproduction number $R_*$ are both threshold parameters, so $R_0 = 1$ if and only if $R_* = 1$.

## Expansion

1. The model: households with homogeneous mixing within and global mixing between, the epidemic graph and generations by rank.
2. The definition (2.3) of $R_0$ and its multitype form as the Perron root of the mean offspring matrix, via the [Perron–Frobenius theorem](../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md).
3. The survival criterion for multitype branching processes in terms of the Perron root.
4. Uniform vaccination and the critical fraction $1 - 1/R_0$ for the approximating process; vaccination of selected types calls for the type reproduction number instead.
5. The households computation of Section 3.2, and the comparison with $R_*$.

## Sources

- L. Pellis, F. Ball and P. Trapman, Reproduction numbers for epidemic models with households and other social structures. I. Definition and calculation of $R_0$, Math. Biosci. 235 (2012), 85–97, Sections 2.2–3.2 and Eq. (2.3). <https://doi.org/10.1016/j.mbs.2011.10.009>
