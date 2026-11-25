# Wrapped upstream sample is the sample one cell upstream

Let $N > 0$ cells, $L \ne 0$, $\Delta x = L/N$, real $c_0, a, v, \Delta t$, $n \in \mathbb{N}$ and $j \in \mathbb{Z}/N\mathbb{Z}$ with representative $\bar{j} \in \{0, \dots, N-1\}$. Then the sample at the node $j - 1$ (computed modulo $N$) satisfies

$$w_{j-1}^n = c\bigl(n\,\Delta t,\ \bar{j}\,\Delta x - \Delta x\bigr),$$

where $c(t,x) = c_0 + a \sin\!\left(\frac{2\pi (x - v t)}{L}\right)$; this includes $j = 0$, whose upstream node is $N - 1$.
