# Entrywise factorization $S_\alpha = S \, U_\alpha$

Let $\alpha \colon \mathbb{N} \to \mathbb{Q}$ and define rationals $S_{i,j}$ for all natural numbers $i, j$ by $S_{0,j} = 0$; $S_{1,0} = 0$ and $S_{1,j} = \alpha_{j-1}$ for $j \ge 1$; and for $i \ge 2$, $S_{i,1} = \alpha_0$, $S_{i,0} = 0$ and $S_{i,j} = S_{i-1,j-1} + j\, S_{i-1,j}$ for $j \ge 2$. For the same sequence, define $U_{i,j}$ for all natural numbers $i, j$ by recursion on $i$: $U_{0,j} = 0$; $U_{1,0} = 0$ and $U_{1,j} = \alpha_{j-1}$ for $j \ge 1$; and for $i \ge 2$, $U_{i,j} = 0$ when $j \le 1$ and $U_{i,j} = U_{i-1,j-1} + (j - i + 1)\, U_{i-1,j}$ when $j \ge 2$, the coefficient $j - i + 1$ being computed in $\mathbb{Q}$. The matrix $U_\alpha$ uses the indices $i, j \ge 1$. Write $S(i,k)$ for the Stirling numbers of the second kind (so $S(0,0) = 1$ and $S(i,k) = 0$ for $k > i$). Then for all natural numbers $N$ and $i$ with $i < N$ and every natural number $j$,

$$S_{i,j} = \sum_{k=0}^{N-1} S(i,k)\, U_{k,j}.$$
