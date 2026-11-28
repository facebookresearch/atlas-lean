# The scaled table is the only table with its margins and its entropy value

Let $\iota$ and $\kappa$ be finite index sets, let $K_{ij} > 0$, $a_i > 0$ and $b_j > 0$ for all $i \in \iota$, $j \in \kappa$, and let $T_{ij} = a_i K_{ij} b_j$. Let $S \colon \iota \times \kappa \to \mathbb{R}$ be a nonnegative table with the same row and column sums as $T$:

$$\sum_j S_{ij} = \sum_j T_{ij} \ \text{for all } i, \qquad \sum_i S_{ij} = \sum_i T_{ij} \ \text{for all } j.$$

With the entropy functional $F(S) = \sum_{i,j} S_{ij} \log(S_{ij} / K_{ij})$ (terms with $S_{ij} = 0$ contribute $0$), we have $F(S) = F(T)$ if and only if $S = T$. In particular, no other nonnegative table with these margins has the same value of $F$ as $T$.
