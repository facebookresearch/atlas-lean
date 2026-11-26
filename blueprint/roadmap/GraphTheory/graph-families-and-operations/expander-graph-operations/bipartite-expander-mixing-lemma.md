# Bipartite expander mixing lemma for regular bipartite multigraphs

A $D$-regular bipartite multigraph between finite sets $L$ and $R$ is given by a bijection between left darts $L \times [D]$ and right darts $R \times [D]$; for $D \ge 1$ this forces $|L| = |R| = N$. Let $W_{\mathrm{left}}$ average a function on $R$ over the left neighbours, and let $\sigma_2$, the normalized nontrivial singular value, be the operator norm of $W_{\mathrm{left}}$ on mean-zero functions. Then for all $U \subseteq L$ and $T \subseteq R$, with $e(U, T)$ the number of edges between them counted with multiplicity,

$$\Bigl| e(U, T) - \frac{D\, |U|\, |T|}{N} \Bigr| \le \sigma_2\, D \sqrt{|U|\,|T|}.$$

The bipartite double cover of a $D$-regular multigraph $G$ (left and right copies of $V$, each edge of $G$ joining $v$ on the left to $v[i]$ on the right) has $\sigma_2$ equal to the spectral expansion $\lambda(G)$.

## Proof sketch

Write $e(U, T) = N D \langle 1_U, W_{\mathrm{left}} 1_T \rangle$ with the uniform inner product, split both indicators into their means and mean-zero parts, and bound the cross term by Cauchy-Schwarz and the definition of $\sigma_2$. For the double cover, $W_{\mathrm{left}}$ is $W_G$ itself.

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Expander mixing lemma](../expander-graphs/expander-mixing-lemma.md)

## Sources

- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
