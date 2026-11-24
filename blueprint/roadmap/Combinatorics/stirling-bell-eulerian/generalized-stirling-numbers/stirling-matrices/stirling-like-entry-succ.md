# Closed form for the rows of the Stirling-like matrix

Let $\alpha \colon \mathbb{N} \to \mathbb{Q}$ and define rationals $S_{i,j}$ for all natural numbers $i, j$ by $S_{0,j} = 0$; $S_{1,0} = 0$ and $S_{1,j} = \alpha_{j-1}$ for $j \ge 1$; and for $i \ge 2$, $S_{i,1} = \alpha_0$, $S_{i,0} = 0$ and $S_{i,j} = S_{i-1,j-1} + j\, S_{i-1,j}$ for $j \ge 2$. Let $\Psi_\alpha(k) = \sum_{l=0}^{k-1} \frac{\alpha_l}{(k-1-l)!}$. Then for all natural numbers $i$ and $j$,

$$S_{i+1,j} = \sum_{k=1}^{j} k^i \, \frac{(-1)^{j-k}}{(j-k)!} \, \Psi_\alpha(k),$$

the right side being an empty sum, equal to $0 = S_{i+1,0}$, when $j = 0$.
