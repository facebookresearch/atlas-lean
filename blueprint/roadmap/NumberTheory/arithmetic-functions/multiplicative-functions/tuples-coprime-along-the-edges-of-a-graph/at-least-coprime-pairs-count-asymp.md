# Asymptotic count of $k$-tuples with at least $r$ coprime pairs

Let $k \ge 2$ and
$r \ge 1$. For a set $E$ of pairs $(a, b)$ with $1 \le a < b \le k$, let $A_E$ be the coprimality
density of the graph on $\{1, \dots, k\}$ with edge set $E$, and put

$$C'_{k,r} = \sum_{j=r}^{k(k-1)/2} (-1)^{j-r} \binom{j-1}{r-1} \sum_{|E| = j} A_E,$$

where the inner sum runs over all sets $E$ of exactly $j$ such pairs. Then there is a real
constant $C$ such that for every integer $N \ge 2$, the number of tuples
$(n_1, \dots, n_k) \in \{1, \dots, N\}^k$ with $\gcd(n_a, n_b) = 1$ for at least $r$ pairs
$a < b$ differs from $C'_{k,r} N^k$ by at most $C N^{k-1} (\log N)^{k-1}$.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 11 (`jis-2024-24.8.5-thm-11`).
