# Return path around a rectangle

For integers $\alpha, a_0, b_0, c, d$ with $\alpha \le a_0$, $\alpha \le b_0$ and $c \le d$, the walk in the square lattice from $(b_0, d)$ to $(a_0, c)$ that goes up one step to $(b_0, d+1)$, left along row $d+1$ to $(\alpha - 1, d+1)$, down along column $\alpha - 1$ to $(\alpha - 1, c - 1)$, right along row $c - 1$ to $(a_0, c - 1)$, and up one step to $(a_0, c)$. Apart from its endpoints it lies in row $d+1$, column $\alpha - 1$ or row $c - 1$, hence outside every rectangle $[\alpha, \beta] \times [c, d]$.
