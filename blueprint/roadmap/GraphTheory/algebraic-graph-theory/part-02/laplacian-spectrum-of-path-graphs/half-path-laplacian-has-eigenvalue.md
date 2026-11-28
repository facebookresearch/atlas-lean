# Cosine values are eigenvalues of the half path Laplacian

Let $A_n = \tfrac12 L(P_n)$ be one half of the real Laplacian matrix of the path graph $P_n$ on the vertices $0, 1, \dots, n-1$ (with $j$ adjacent to $j + 1$). For $n \ge 1$ and $0 \le k < n$, the number $1 - \cos(\pi k / n)$ is an eigenvalue of the linear map $\mathbb{R}^n \to \mathbb{R}^n$, $v \mapsto A_n v$.

Equivalently, $A_n - (1 - \cos(\pi k/n))\, I_n$ is not invertible, that is, $1 - \cos(\pi k/n)$ lies in the spectrum of $A_n$ in the algebra of real $n \times n$ matrices: for a finite real square matrix the kernel of $A_n - \mu I_n$ is exactly the $\mu$-eigenspace.

## Sources

- Kitaev, Shen and Vyalyi, *Classical and Quantum Computation*, Sections 14.4.2 and 14.4.4.
