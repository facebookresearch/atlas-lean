# Maximum size of a 2-weakly compatible split system

**Definitions.** A split of a finite set $X$ is a bipartition $A|B$ into nonempty parts, and a split system is a set of splits. A split system $\mathcal S$ on $X$ is 2-weakly compatible if no six elements of $X$, relabeled $1,\dots,6$, carry four splits of $\mathcal S$ whose restrictions are

$$\{123|456,\ 124|356,\ 125|346,\ 126|345\}.$$

These are exactly the split systems reconstructed consistently from quartet weights. A linear-algebra argument bounds their size by $3\binom n4+\binom n2$ when $|X|=n$.

**Theorem.** If $|X|=n$, every 2-weakly compatible split system on $X$ has $O(n^{5/2})$ splits.

**Method.** For $x\in X$ let $\partial_x\mathcal S=\{A|B:\ (A+x)|B\in\mathcal S\text{ and }A|(B+x)\in\mathcal S\}$, the restrictions to $X-x$ arising from an $x$-pair of splits (empty splits allowed). Then

$$\#\mathcal S-\#(\mathcal S|_{X-x})=\#\partial_x\mathcal S .$$

Fix $r\in X$ and represent each split by its side $a_r(s)$ not containing $r$; the digraph $G_r(\mathcal S)$ on these sets has an edge $a\to a+x$ labelled $x$ for each $x$-pair. For $n\ge6$ there is a constant $c$ such that every digraph $G=(V,E)$ representing a 2-weakly compatible system satisfies $\#E\le\frac52\#V+cn^2$. Finally, if every restriction $\mathcal S|_Y$ has representing graphs with $\#E\le k\#V+c(\#Y)^\ell$, $\ell<k$, then $\#\mathcal S=O(n^k)$.

## Expansion

Removing one element at a time, the deletion identity shows that $\#\mathcal S$ is controlled by the number of $x$-pairs, i.e. the labelled edges of the representing digraphs; an edge bound of the form $\#E\le k\#V+O(n^\ell)$ for every restriction then yields $\#\mathcal S=O(n^k)$. The main work is the edge bound with $k=5/2$, proved by a case analysis showing that a vertex with too many labelled neighbours produces the forbidden configuration.

## Sources

- P. Wu, S. Grünewald, "On the maximum size of 2-weakly compatible split systems", arXiv:2608.23275 (2026), Theorem 1, Proposition 1, Theorems 2 and 3, Section 1 (forbidden configuration and the prior bound), <https://doi.org/10.48550/arXiv.2608.23275>.
