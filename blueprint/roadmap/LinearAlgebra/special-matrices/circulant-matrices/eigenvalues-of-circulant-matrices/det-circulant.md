# Determinant of a circulant matrix

Let $n \ge 1$, let $v : \mathbb{Z}/n\mathbb{Z} \to \mathbb{C}$, and let $C(v)$ be the circulant
matrix whose entry in row $k$ and column $l$ is $v(k - l)$. Then

$$\det C(v) = \prod_{j \in \mathbb{Z}/n\mathbb{Z}} \lambda_j(v), \qquad
\lambda_j(v) = \sum_{k \in \mathbb{Z}/n\mathbb{Z}} v(k)\, \zeta_n^{-kj},$$

where $\zeta_n = e^{2\pi i/n}$ and $k$, $j$ are read as integers in $\{0, \dots, n-1\}$.
