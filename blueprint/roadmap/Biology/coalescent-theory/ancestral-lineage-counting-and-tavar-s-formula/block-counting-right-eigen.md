# Right eigenvectors of Kingman's block-counting generator

For a natural number $n$, the $(n+1) \times (n+1)$ real matrix $V_n$, with rows and columns indexed by $\{0, \dots, n\}$, whose entry in row $i$ and column $k$ is the falling factorial of $i$ of length $k$ divided by the rising factorial of $i$ of length $k$:

$$(V_n)_{ik} = \frac{i(i-1)\cdots(i-k+1)}{i(i+1)\cdots(i+k-1)},$$

with the convention that division by $0$ gives $0$ (so $(V_n)_{00} = 1$ and $(V_n)_{0k} = 0$ for $k \ge 1$). Its column $k$ is a right eigenvector of the block-counting generator for the eigenvalue $-\binom{k}{2}$.
