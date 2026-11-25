# Tavaré's formula

For every natural number $n$, every real $t$ and all $i, j \in \{0, \dots, n\}$ with $1 \le j \le i$, the entry in row $i$ and column $j$ of the matrix exponential $e^{t G_n}$ of the [block-counting generator](block-counting-generator.md) is

$$\bigl(e^{t G_n}\bigr)_{ij} = \sum_{k=j}^{i} e^{-k(k-1)t/2}\, \frac{(2k-1)(-1)^{k-j}\, j^{\overline{k-1}}\, i^{\underline{k}}}{j!\,(k-j)!\, i^{\overline{k}}},$$

where $a^{\overline{m}}$ and $a^{\underline{m}}$ are the rising and falling factorials ([Tavaré's formula for the number of ancestral lineages](tavare-prob.md)). For $t \ge 0$, $e^{t G_n}$ is the transition matrix at time $t$ of Kingman's block-counting process, and the entry is the probability that $i$ lineages have $j$ ancestors a time $t$ earlier.

## Sources

- S. Tavaré, *Line-of-descent and genealogical processes, and their applications in population genetics models*, Theoret. Population Biol. 26 (1984), 119–164.
