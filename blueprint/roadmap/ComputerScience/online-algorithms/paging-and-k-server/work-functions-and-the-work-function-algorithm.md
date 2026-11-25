# Work functions and the work function algorithm

For the $k$-server problem on a metric space with requests $r_1, r_2, \dots$, the *work function* $w_t(X)$ is the minimum cost of serving $r_1, \dots, r_t$ starting from the initial configuration and ending in configuration $X$. The *work function algorithm* serves $r_t$ by moving from its current configuration $A_{t-1}$ to the configuration $A_t \ni r_t$ that minimizes $w_t(A_t) + d(A_{t-1}, A_t)$. Each $w_t$ is $1$-Lipschitz with respect to the matching distance between configurations, and the offline optimum after $t$ requests is $\min_X w_t(X)$. Koutsoupias and Papadimitriou proved that the work function algorithm is $(2k-1)$-competitive.

## Depends on

- [The k-server problem](the-k-server-problem.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- E. Koutsoupias and C. H. Papadimitriou, "On the k-server conjecture", *Journal of the ACM* 42(5):971–983, 1995
