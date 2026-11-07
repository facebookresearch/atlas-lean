# $(p,q)$-binomial coefficient

Let $R$ be a commutative semiring and $p, q \in R$. For
natural numbers $n$ and $k$, the $(p,q)$-binomial coefficient $\binom{n}{k}_{p,q} \in R$ is
defined recursively by $\binom{n}{0}_{p,q} = 1$, $\binom{0}{k+1}_{p,q} = 0$ and
$\binom{n+1}{k+1}_{p,q} = p^{n-k} \binom{n}{k}_{p,q} + q^{k+1} \binom{n}{k+1}_{p,q}$, where $n - k$
is truncated subtraction ($0$ when $k > n$).

For $k \le n$, where the $(p,q)$-factorials are invertible, $\binom{n}{k}_{p,q}$ equals
$[n]_{p,q}! / ([k]_{p,q}! \, [n-k]_{p,q}!)$, where $[j]_{p,q} = p^{j-1} + p^{j-2} q + \dots +
q^{j-1}$; this is the definition used in the source. At $p = 1$ it is the Gaussian binomial
coefficient $\binom{n}{k}_q$.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Section 3, Equation (3).
