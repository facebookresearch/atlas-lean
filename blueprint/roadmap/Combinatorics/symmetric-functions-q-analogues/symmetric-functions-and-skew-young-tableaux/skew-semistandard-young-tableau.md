# Semistandard Young tableau of skew shape

Let $\lambda/\mu$ be a skew shape, and write
$\lambda_k$ and $\mu_k$ for the $k$-th parts of $\lambda$ and $\mu$, with $\lambda_k = 0$
($\mu_k = 0$) when $\lambda$ ($\mu$) has fewer than $k$ parts. The cells of $\lambda/\mu$ are the
pairs $(i, j) \in \mathbb{Z}_{\ge 1} \times \mathbb{Z}_{\ge 1}$ with $\mu_i < j \le \lambda_i$,
that is, the cells of $D(\lambda)$ that are not cells of $D(\mu)$. A semistandard Young tableau
of shape $\lambda/\mu$ is a function $T$ assigning a nonnegative integer $T_{i,j}$ to every pair
$(i, j) \in \mathbb{Z}_{\ge 1} \times \mathbb{Z}_{\ge 1}$ such that $T_{i,j} \ge 1$ for every cell
$(i, j)$ of $\lambda/\mu$; $T_{i,j} \le T_{i,j'}$ whenever $(i, j)$ and $(i, j')$ are cells of
$\lambda/\mu$ with $j < j'$ (rows weakly increase); $T_{i,j} < T_{i',j}$ whenever $(i, j)$ and
$(i', j)$ are cells of $\lambda/\mu$ with $i < i'$ (columns strictly increase); and $T_{i,j} = 0$
for every pair $(i, j)$ that is not a cell of $\lambda/\mu$.
