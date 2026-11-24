# Column 0 of the recursion for $U_\alpha$ vanishes

Let $\alpha \colon \mathbb{N} \to \mathbb{Q}$ and define rationals $U_{i,j}$ for all natural numbers $i, j$ by recursion on $i$: $U_{0,j} = 0$; $U_{1,0} = 0$ and $U_{1,j} = \alpha_{j-1}$ for $j \ge 1$; and for $i \ge 2$, $U_{i,j} = 0$ when $j \le 1$ and $U_{i,j} = U_{i-1,j-1} + (j - i + 1)\, U_{i-1,j}$ when $j \ge 2$, the coefficient $j - i + 1$ being computed in $\mathbb{Q}$. The matrix $U_\alpha$ uses the indices $i, j \ge 1$. Then $U_{i,0} = 0$ for every natural number $i$; the index $0$ lies outside the matrix.
