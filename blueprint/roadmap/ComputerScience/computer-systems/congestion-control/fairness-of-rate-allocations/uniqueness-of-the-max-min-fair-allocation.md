# Uniqueness of the max-min fair allocation

For a given set of feasible allocations, there is at most one [max-min fair](max-min-fair-rate-allocations.md) allocation. The argument uses only the definition and holds for any feasible set.

**Proof.** Let $x \ne y$ be max-min fair; by symmetry some $x_i < y_i$; let $i_0$ attain the least $x_i$ among those with $x_i < y_i$. Since $x$ is max-min fair, some $j$ has $y_j < x_j \le x_{i_0}$; since $y$ is max-min fair, some $k$ has $x_k < y_k \le y_j$. Then $x_k < y_k \le y_j < x_j \le x_{i_0}$ with $x_k < y_k$, contradicting the choice of $i_0$.

## Depends on

- [Max-min fair rate allocations](max-min-fair-rate-allocations.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.1, Theorem 1.2.2 with its proof (equations (1.2)–(1.4)).
