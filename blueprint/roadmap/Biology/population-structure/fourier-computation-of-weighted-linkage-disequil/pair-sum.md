# Brute-force pair sum at a cell offset

Let $S$ be a finite set of SNPs with grid cells $c : S \to \mathbb{N}$. For $u, v : S \to \mathbb{R}$ and $j \in \mathbb{N}$, the pair sum at offset $j$ is

$$\Pi_j(u, v) = \sum_{x, y \in S,\ c(y) = c(x) + j} u(x)\, v(y),$$

the sum over ordered SNP pairs whose grid cells differ by $j$.
