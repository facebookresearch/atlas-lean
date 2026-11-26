# Life expectancy from the fundamental matrix

Let $U$ be the $s \times s$ transient matrix of a stage-structured model, with entry $u_{ij} \ge 0$ the probability of moving from stage $j$ to stage $i$ in one time step, column sums at most $1$, and spectral radius $\rho(U) < 1$; adding death as an absorbing state gives an absorbing Markov chain (Caswell 2019, Sec. 5.2.1). Let $\nu_{ij}$ be the number of visits to transient stage $i$, counting the present one, made by an individual now in stage $j$ before absorption. Then

$$N = \bigl(E(\nu_{ij})\bigr) = \sum_{t \ge 0} U^t = (I - U)^{-1}$$

is the fundamental matrix (Caswell, eq. (5.6)). The longevity $\eta_j = \sum_i \nu_{ij}$ of an individual in stage $j$ has expectation given by the column sums, $E(\eta^\top) = \mathbf 1^\top N$ (eq. (5.23)), and life expectancy at birth is $E(\eta_1) = \mathbf 1^\top N e_1$ when stage $1$ is the birth stage (eq. (5.24)).

## Expansion

1. The model: the absorbing Markov chain with transient stages and death, and the substochastic matrix $U$.
2. Convergence of the Neumann series under $\rho(U) < 1$, and nonnegativity of $N$.
3. The expected occupation times $E(\nu_{ij}) = \sum_t (U^t)_{ij}$ by linearity of expectation.
4. Longevity as column sums; the variance of longevity from $N$, as a separate statement.

## Sources

- H. Caswell, *Sensitivity Analysis: Matrix Methods in Demography and Ecology*, Springer, 2019, Secs. 5.2.1–5.2.2 and 5.3.2, eqs. (5.3), (5.6), (5.22)–(5.24). <https://doi.org/10.1007/978-3-030-10534-1>
