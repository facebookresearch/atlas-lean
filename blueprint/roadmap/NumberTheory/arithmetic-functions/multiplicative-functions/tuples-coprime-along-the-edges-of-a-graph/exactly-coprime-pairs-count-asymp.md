# Asymptotic count of tuples with exactly $r$ coprime pairs

Let $k \ge 2$ and $r \ge 0$.
For a set $E$ of pairs $(a, b)$ with $0 \le a < b < k$, let $A_E$ be the coprimality density of
the graph with edge set $E$, and put

$$C_{k,r} = \sum_{j=r}^{k(k-1)/2} (-1)^{j-r} \binom{j}{r} \sum_{|E| = j} A_E,$$

where the inner sum runs over the $j$-element sets $E$ of such pairs. Then there is a real
constant $C$ such that for every integer $N \ge 2$ the number $T_r(N)$ of tuples
$n \in \{1, \dots, N\}^k$ with exactly $r$ coprime pairs satisfies

$$|T_r(N) - C_{k,r} N^k| \le C N^{k-1} (\log N)^{k-1}.$$

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 11 (`jis-2024-24.8.5-thm-11`).
