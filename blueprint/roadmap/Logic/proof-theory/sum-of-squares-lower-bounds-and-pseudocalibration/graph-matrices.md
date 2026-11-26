# Graph matrices and their norm bounds

Let $G$ be a random graph on $[n]$ with edge indicators $\chi_e(G) \in \{\pm 1\}$. A **shape** $\alpha$ is a small graph with two distinguished ordered vertex tuples $U_\alpha, V_\alpha$. The **graph matrix** $M_\alpha$ has rows and columns indexed by tuples of distinct vertices of $[n]$ of sizes $|U_\alpha|$ and $|V_\alpha|$, with

$$
M_\alpha(I, J) = \sum_{\sigma} \prod_{e \in E(\alpha)} \chi_{\sigma(e)}(G),
$$

summed over injective embeddings $\sigma$ of the vertices of $\alpha$ into $[n]$ mapping $U_\alpha$ to $I$ and $V_\alpha$ to $J$. With high probability $\|M_\alpha\| \le \widetilde{O}\bigl(n^{(|V(\alpha)| - |S_{\min}|)/2}\bigr)$, where $S_{\min}$ is a minimum-size vertex separator of $U_\alpha$ and $V_\alpha$ in $\alpha$.

## Sources

- K. Ahn, D. Medarametla, A. Potechin, "Graph matrices: norm bounds and applications", arXiv:1604.03423 (2016).
- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", FOCS (2016); SIAM Journal on Computing 48 (2019), arXiv:1604.03084.
