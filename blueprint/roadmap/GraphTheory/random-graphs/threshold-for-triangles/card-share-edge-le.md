# A triangle shares an edge with at most 3n others

For a fixed vertex triple $T$, every other triple sharing a pair with $T$ consists of one of the three pairs of $T$ and one further vertex, so there are at most $3n$ of them. The exact count $3(n-3)$ is implicit in Zhao's variance computation for triangles, whose overlap term $\binom n2 (n-2)(n-3)(p^5 - p^6)$ equals $\binom n3 \cdot 3(n-3) \cdot (p^5 - p^6)$.

## Sources

- Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Example 4.5.
