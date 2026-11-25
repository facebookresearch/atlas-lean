# Entropy minimizer unique scaled Table

Let $m, n \in \mathbb{N}$, let $K \in \mathbb{R}^{m \times n}$ with $K_{ij} > 0$, let $a \in \mathbb{R}^m$ and $b \in \mathbb{R}^n$ with $a_i > 0$ and $b_j > 0$, and let $T_{ij} = a_i K_{ij} b_j$ be the scaled table. Let $S \in \mathbb{R}^{m \times n}$ satisfy $S_{ij} \ge 0$ for all $i, j$ and have the same row and column sums as $T$. Then, with $F(S) = \sum_{i,j} S_{ij} \log(S_{ij} / K_{ij})$ (terms with $S_{ij} = 0$ contribute $0$),

$$F(S) = F(T) \iff S = T.$$
