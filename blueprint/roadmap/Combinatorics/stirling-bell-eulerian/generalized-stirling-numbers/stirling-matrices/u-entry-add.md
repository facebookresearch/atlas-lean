# Entries of $U_\alpha$ above the diagonal

Let $\alpha \colon \mathbb{N} \to \mathbb{Q}$ and define rationals $U_{i,j}$ for all natural numbers $i, j$ by recursion on $i$: $U_{0,j} = 0$; $U_{1,0} = 0$ and $U_{1,j} = \alpha_{j-1}$ for $j \ge 1$; and for $i \ge 2$, $U_{i,j} = 0$ when $j \le 1$ and $U_{i,j} = U_{i-1,j-1} + (j - i + 1)\, U_{i-1,j}$ when $j \ge 2$, the coefficient $j - i + 1$ being computed in $\mathbb{Q}$. Then for all natural numbers $i$ and $d$,

$$U_{i+1,\,i+1+d} = \sum_{l=0}^{i} \binom{i}{l} \frac{(l+d)!}{d!}\, \alpha_{l+d}.$$
