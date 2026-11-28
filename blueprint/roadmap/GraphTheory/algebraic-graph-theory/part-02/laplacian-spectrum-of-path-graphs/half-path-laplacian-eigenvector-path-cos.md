# Eigenvectors of the half path Laplacian

Let $A_n = \tfrac12 L(P_n)$ be one half of the real Laplacian matrix of the path graph $P_n$ on the vertices $0, 1, \dots, n-1$ (with $j$ adjacent to $j + 1$), and let $v_k(j) = \cos\bigl(\pi k (j + \tfrac12) / n\bigr)$ for $j = 0, \dots, n-1$. For $n \ge 1$ and $0 \le k < n$, the vector $v_k$ is nonzero and satisfies $A_n v_k = (1 - \cos(\pi k / n))\, v_k$; so $v_k$ is an eigenvector of $A_n$ with eigenvalue $1 - \cos(\pi k / n)$.

## Sources

- Kitaev, Shen and Vyalyi, *Classical and Quantum Computation*, Sections 14.4.2 and 14.4.4.
