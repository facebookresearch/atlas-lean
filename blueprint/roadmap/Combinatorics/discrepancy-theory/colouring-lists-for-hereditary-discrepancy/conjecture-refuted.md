# The polynomial-size colouring list conjecture is false

There do not exist a real number
$C > 0$ and a natural number $k$ such that for all positive integers $n$ and $m$ and every real
$n \times m$ matrix $A$ there is a set $L$ of at most $m^k$ sign vectors in $\{-1, 1\}^m$ with
the following property: for every set $S$ of columns of $A$ some $\varepsilon \in L$ satisfies
$\left|\sum_{j \in S} A_{ij} \varepsilon_j\right| \le C \operatorname{herdisc}(A)$ for every row
$i$, where $\operatorname{herdisc}(A)$ is the hereditary discrepancy of $A$.

The AIM problem list records this negative answer: for the $0/1$ matrix with $m$ columns whose
$\sqrt{m}$ rows are the indicators of disjoint sets of $\sqrt{m}$ columns, the hereditary
discrepancy is $1$, yet for fixed $C$ and lists of polynomial size some set of columns has
discrepancy above $C$ under every listed colouring.

## Sources

- AIM Problem Lists, Hereditary discrepancy and factorization norms, Problem 1.85 (Polysize list of colorings), https://aimpl.org/hereddiscrep/1/. Moved from `OpenConjectures/Combinatorics/PolysizeColoringList`.
