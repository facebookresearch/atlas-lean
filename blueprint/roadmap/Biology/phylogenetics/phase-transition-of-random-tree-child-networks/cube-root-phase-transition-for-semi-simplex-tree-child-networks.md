# Cube-root phase transition for semi-simplex tree-child networks

A rooted binary **phylogenetic network** is a directed acyclic graph with a root (indegree $0$, outdegree $1$), $n$ labeled leaves, tree nodes (indegree $1$, outdegree $2$) and $k$ reticulation nodes (indegree $2$, outdegree $1$). It is **tree-child** if every non-leaf node has a child that is a tree node or a leaf. It is **simplex** if the child of every reticulation is a leaf, and **semi-simplex** if the child of every reticulation is the root of a subtree. Let $\mathrm{TC}_{n,k}$ and $\mathrm{SSTC}_{n,k}$ count tree-child and semi-simplex tree-child networks. It is known that, uniformly for $k = o(n^{1/2})$,

$$
\mathrm{TC}_{n,k} \sim \frac{2^{k-1}\sqrt2}{k!}\Big(\frac{2}{e}\Big)^n n^{n+2k-1}.
$$

**Proposition.** As $n \to \infty$ with $k = o(n^{1/2})$,

$$
\mathrm{SSTC}_{n,k} \sim \frac{2^{k-1}\sqrt2}{k!}\Big(\frac{2}{e}\Big)^n n^{n+2k-1} e^{-\sqrt{2k^3/n}}.
$$

**Theorem (phase transition).** Let $E_{n,k}$ be the event that a uniformly random tree-child network with $n$ leaves and $k$ reticulations is semi-simplex. As $n \to \infty$ with $k = o(n^{1/2})$,

$$
\mathbb{P}(E_{n,k}) \to \begin{cases} 1, & k = o(n^{1/3}), \\ e^{-\sqrt2\, c^{3/2}}, & k \sim c\, n^{1/3}, \\ 0, & k/n^{1/3} \to \infty. \end{cases}
$$

## Expansion

Simplex tree-child networks have the closed form $\binom{n}{k}\frac{(2n-2)!}{2^{n-1}(n-k-1)!}$. Hanging phylogenetic trees, with exponential generating function $T(z) = 1 - \sqrt{1 - 2z}$, below the $k$ reticulation leaves gives the semi-simplex generating function $F_k(z)\,T(z)^k/k!$, with $F_k(z) = \frac{(2k)!}{2^k}(1 - 2z)^{-2k + 1/2} p_k(z)$ for an explicit degree-$k$ polynomial $p_k$. A uniform transfer lemma, $[z^n]\,(1-z)^{-\alpha}(1 - \sqrt{1-z})^m = \frac{n^{\alpha-1}}{\Gamma(\alpha)} e^{-m\sqrt{\alpha/n}}(1 + O(\sqrt{k/n} + k^2/n))$ for $\alpha = \Theta(k)$ and $m \le k$, produces the factor $e^{-\sqrt{2k^3/n}}$. Dividing by $\mathrm{TC}_{n,k}$ gives the limit law.

## Sources

- Michael Fuchs, Hao Yu, "A cube-root phase transition in tree-child networks and the enumeration threshold for galled networks", arXiv (2026). Definitions 1.1-1.2, Proposition 1.3, Theorem 1.4, Lemma 2.1, Lemma 2.2, Lemma 2.4, Corollary 2.6. <https://doi.org/10.48550/arXiv.2608.20860>
