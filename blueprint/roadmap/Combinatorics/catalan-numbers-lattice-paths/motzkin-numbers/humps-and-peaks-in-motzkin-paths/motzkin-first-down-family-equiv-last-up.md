# A bijection between first-down and even-height last-up Motzkin prefixes

Use the steps
$U = (1,1)$, $F = (1,0)$ and $D = (1,-1)$, and call a word in these steps a Motzkin prefix if
none of its initial segments ends below height $0$. For every natural number $n$ there is a
bijection between the set of pairs $(k, p)$, where $k$ is a natural number with $k + 2 \le n$ and
$p$ is a Motzkin prefix of length $n$ ending at height $k$ whose first step other than $U$ exists
and is $D$, and the set of pairs $(k, p)$, where $k$ is a natural number with
$1 \le k \le \lfloor n/2 \rfloor$ and $p$ is a Motzkin prefix of length $n$ ending at height $2k$
that contains a $U$ after which every step is $F$.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Lemma 6 (`jis-2025-25.8.1-lem-6`).
