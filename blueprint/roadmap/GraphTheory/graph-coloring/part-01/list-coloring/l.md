# Noel's 2-list assignment

Noel's graph $N$ has fourteen vertices: two terminals $s_1, s_2$ and, for each $i \in \{0, 1, 2, 3\}$, vertices $u_i, v_i, p_i$. Its edges are those of the four triangles $\{u_i, v_i, p_i\}$ and the edges from each terminal to every $u_i$ and every $v_i$; there are no other edges, so $s_1$ and $s_2$ are not adjacent and each $p_i$ is adjacent only to $u_i$ and $v_i$. Noel's $2$-list assignment $L$ on $N$ gives $L(s_1) = \{0, 1\}$, $L(s_2) = \{2, 3\}$, and to all three vertices of the $i$-th triangle the list $\{0, 2\}$, $\{0, 3\}$, $\{1, 2\}$ or $\{1, 3\}$ for $i = 0, 1, 2, 3$ respectively. Every list has exactly two colours. In the source's colours $1, 2, 3, 4$, written here as $0, 1, 2, 3$, the terminals get $\{1, 2\}$ and $\{3, 4\}$.

## Sources

- J. A. Noel, *The Partial List Colouring Conjecture is False*, arXiv:2609.23291, Theorem 1.1.
