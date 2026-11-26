# Number of one-reticulation tree-child networks containing a trident

A binary phylogenetic network is a directed acyclic graph with a root of indegree $0$ and outdegree $1$, leaves of indegree $1$ and outdegree $0$ bijectively labelled, tree nodes of indegree $1$ and outdegree $2$, and reticulation nodes of indegree $2$ and outdegree $1$; it is **tree-child** if every non-leaf vertex has a child that is not a reticulation node. A **trident** is a reticulation node whose child is a leaf and whose two parents each have a leaf as their other child. Let $\mathrm{TC}_{m,1}$ be the number of tree-child networks with $m$ labelled leaves and one reticulation node, and $\mathrm{TR}_{m,1}$ the number of those containing a trident.

**Theorem 5.1 (bijection).** Let $\mathcal{A}_n$ be the set of trident tableaux: fillings of a two-row Young shape with $n$ columns plus one extra cell below one column by $1, \dots, 2n+1$, increasing along rows and up columns, whose three-cell column with entries $k < j < i$ has $k+1$ and $j+1$ in the top row and either $i+1$ in the top row or $i = 2n+1$. Let $\mathcal{B}_n$ be the set of two-wall tableaux: two-row fillings of $n$ columns by $1, \dots, 2n$ increasing along rows, with two designated wall columns in which the vertical order is not imposed. For every $n \ge 2$ there is a bijection $\mathcal{B}_n \to \mathcal{A}_{n+1}$ respecting the three-part decompositions of both classes, and

$$ |\mathcal{A}_{n+1}| = |\mathcal{B}_n| = \binom{n+1}{2} C_n, $$

where $C_n$ is the $n$-th Catalan number; the three parts have sizes $\binom{n}{2} C_n$, $(n-1) C_n$ and $C_n$.

**Corollary 5.2.** For $m \ge 3$,

$$ \mathrm{TR}_{m,1} = 3 \binom{m}{3} (2m-5)!!, \qquad \frac{\mathrm{TR}_{m,1}}{\mathrm{TC}_{m,1}} \longrightarrow \frac{1}{8} \quad (m \to \infty). $$

So asymptotically one in eight tree-child networks with a single reticulation contains a trident.

## Expansion

A tree-child network with $m$ leaves and one reticulation has $m$ tree nodes, $m-2$ of them free (not parents of the reticulation). A word encoding of tree-child networks associates to such a network, together with one choice of free edge at each free tree node and a permutation of leaf labels, a tableau in $\mathcal{Y}_{m-1}$, giving $2^{m-2} \mathrm{TC}_{m,1} = m!\, |\mathcal{Y}_{m-1}|$. The network contains a trident exactly when the three-cell column of its tableau is a trident column (Lemma 2.1), independently of the free-edge choices, so $2^{m-2} \mathrm{TR}_{m,1} = m!\, |\mathcal{A}_{m-1}|$. Substituting $|\mathcal{A}_{m-1}| = \binom{m-1}{2} C_{m-2}$ from Theorem 5.1 (with $|\mathcal{A}_2| = 1$) gives the closed form. Combining with $\mathrm{TC}_{m,1} = m (2m-1)!! - 2^{m-1} m!$, whose second term is $O(m^{-1/2})$ relative to the first, yields the limit $\frac{3\binom{m}{3}(2m-5)!!}{m(2m-1)!!} \to \frac{1}{8}$. The bijection itself decomposes both tableau classes into three parts and matches them through a Chung-Feller type encoding of two-row fillings with an insertion map.

## Sources

- Hexuan Liu, "Trident Tableaux for Tree-Child Networks with One Reticulation Node: A Bijection with Two-Wall Tableaux", arXiv (2026). Lemma 2.1, Lemma 3.1, Theorem 5.1, Corollary 5.2. <https://doi.org/10.48550/arXiv.2609.28892>
