# Probability that a random subset contains a given set

If the random subset $R$ contains each element $a$ independently with probability $p(a)$, then for every finite $S$,

$$\Pr[S \subseteq R] = \prod_{a \in S} p(a).$$

For $G(n, p)$ and the edge set $S$ of a fixed copy of a graph $H$ this is $p^{e(H)}$, the starting point of every first and second moment computation for subgraph counts.

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Setup 7.10.
