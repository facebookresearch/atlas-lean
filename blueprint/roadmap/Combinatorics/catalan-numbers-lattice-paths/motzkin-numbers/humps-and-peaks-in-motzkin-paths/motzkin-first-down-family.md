# Motzkin prefixes whose first non-up step is down

Use the steps $U = (1,1)$,
$F = (1,0)$ and $D = (1,-1)$, and call a word in these steps a Motzkin prefix if none of its
initial segments ends below height $0$. For a natural number $n$, this is the set of pairs
$(k, p)$ where $k$ is a natural number with $k \le n - 2$ and $p$ is a Motzkin prefix of length
$n$ ending at height $k$ whose first step other than $U$ exists and is $D$.

This is the paper's disjoint union $\bigcup_{0 \le k \le n-2} \mathcal{M}^{D*}_{n,k}$, keeping
the index $k$ with each path.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Lemma 6 (`jis-2025-25.8.1-lem-6`).
