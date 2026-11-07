# Partial-sum characterization of binomid indices

Let $\eta = (e_1, e_2, \dots)$ be a
sequence of nonnegative integers with partial sums $s_n = e_1 + \dots + e_n$ (so $s_0 = 0$).
Then $\eta$ is a binomid index if and only if $s_{n-k} + s_k \le s_n$ for all $k$ and $n$ with
$1 \le k < n$. Moreover, for every $m$, if $\eta$ is the lex-minimal extension of its first $m$
entries, then for every $n > m$

$$s_n = \max_{1 \le k < n} (s_{n-k} + s_k),$$

where the maximum over the empty range (for $n = 1$) is taken to be $0$.

## Sources

- Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 1 (`integers-2024-A53-lem-1`).
