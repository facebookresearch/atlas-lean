# Composite midpoint load at the interior node

Let $\varphi$ be the hat function of the interior node of the mesh $0 < \tfrac12 < 1$ of $[0, 1]$. For $L \in \mathbb{R}$ and a load $q : \mathbb{R} \to \mathbb{R}$, the midpoint load of the two-cell mesh of $[0, L]$ is

$$F_{\mathrm{mid}}(L, q) = \frac{L}{2}\,q\Big(\frac{L}{4}\Big)\,\varphi\Big(\frac{L/4}{L}\Big) + \frac{L}{2}\,q\Big(\frac{3L}{4}\Big)\,\varphi\Big(\frac{3L/4}{L}\Big),$$

the cell width $L/2$ times the load times the pulled-back hat at the cell midpoints $L/4$ and $3L/4$. For $L = 0$ the hat arguments take the convention $x/0 = 0$, and the value is $0$.
