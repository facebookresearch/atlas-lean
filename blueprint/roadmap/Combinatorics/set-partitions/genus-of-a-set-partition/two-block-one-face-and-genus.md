# Genus of two-block partitions

Let $\sigma$ be the cyclic permutation
$i \mapsto i + 1 \pmod n$ of $\{0, \dots, n-1\}$, and let $\tau$ be an increasing-cycle permutation
of $\{0, \dots, n-1\}$ with exactly two cycles, fixed points counted as cycles (so $\tau$ encodes a
set partition into two blocks). Then $\sigma \circ \tau^{-1}$ has exactly one cycle of length at
least $2$. Moreover, for every $x_0$ in $\{0, \dots, n-1\}$, if $B$ is the cycle of $\tau$
containing $x_0$ and $s$ is the number of elements of $B$ fixed by $\sigma \circ \tau^{-1}$, then
the genus $g$ of $\tau$ satisfies $g + 1 + s = |B|$.

Taking $x_0$ in each of the two blocks, of sizes $p$ and $n - p$, and writing $s_1$ and $s_2$ for
the corresponding values of $s$, gives $g = p - s_1 - 1 = (n - p) - s_2 - 1$.

## Sources

- Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*, Journal of Integer Sequences 27 (2024), Article 24.2.6, Lemma 13 (`jis-2024-24.2.6-lem-13`).
