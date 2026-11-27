# Graph matrices and their norm bounds

Let $G \sim G(n, 1/2)$ be a random graph on $[n]$, so that the edge indicators $\chi_e(G) \in \{\pm 1\}$ are independent and uniform. A **shape** $\alpha$ is a small graph with two distinguished ordered vertex tuples $U_\alpha, V_\alpha$. The **graph matrix** $M_\alpha$ has rows and columns indexed by tuples of distinct vertices of $[n]$ of sizes $|U_\alpha|$ and $|V_\alpha|$, with

$$
M_\alpha(I, J) = \sum_{\sigma} \prod_{e \in E(\alpha)} \chi_{\sigma(e)}(G),
$$

summed over injective embeddings $\sigma$ of the vertices of $\alpha$ into $[n]$ mapping $U_\alpha$ to $I$ and $V_\alpha$ to $J$. With high probability $\|M_\alpha\| \le \widetilde{O}\bigl(n^{(|V(\alpha)| - |S_{\min}| + |I_\alpha|)/2}\bigr)$, where $S_{\min}$ is a minimum-size vertex separator of $U_\alpha$ and $V_\alpha$ in $\alpha$ and $I_\alpha$ is the set of isolated vertices of $\alpha$ outside $U_\alpha \cup V_\alpha$.

## Sources

- C. Jones, A. Potechin, G. Rajendran, M. Tulsiani, J. Xu, "Sum-of-Squares Lower Bounds for Sparse Independent Set", FOCS (2021), arXiv:2111.09250, Corollary 6.64 (from Theorem 6.60 and Theorem A.7): the norm bound for graph matrices of $G(n, p)$, proved by the trace method, which at $p = 1/2$ is the bound stated here.
- K. Ahn, D. Medarametla, A. Potechin, "Graph matrices: norm bounds and applications", arXiv:1604.03423 (2016), Theorem 2.24.
- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", FOCS (2016); SIAM Journal on Computing 48 (2019), arXiv:1604.03084.
