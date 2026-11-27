# Decisiveness under random taxon sampling

Let $T$ be an unknown rooted binary phylogenetic tree on a set $X$ of $n$ taxa (equivalently an unrooted tree on $n+1$ taxa with a reference taxon $y$ present in every locus). Sample $k$ loci independently: in locus $i$ each taxon $x$ is included in $S_i$ independently with probability $p(x)$. Under **uniform coverage** (UC), $p(x) = p$ for all $x$; under UC+1, $p(y) = 1$ and $p(x) = p$ otherwise. To model lack of resolution, each internal edge of every induced tree $T|S_i$ is kept with probability $q$ and collapsed with probability $1-q$, independently. Let $E_k(T)$ be the event that the resulting partially resolved induced subtrees define $T$ (for $q = 1$ this is the event that $\{S_1, \dots, S_k\}$ is decisive for $T$).

**Theorem 2.**

(i) For every rooted $T$ on $n$ leaves under UC (equivalently every unrooted $T$ on $n+1$ leaves under UC+1),

$$\mathbb P(E_k(T)) \;\ge\; 1 - (n-2)\,(1 - p^3 q)^k .$$

Consequently $\mathbb P(E_k(T)) \ge 1 - \varepsilon$ as soon as $k \ge \ln\!\big((n-2)/\varepsilon\big) \big/ \big(-\ln(1 - p^3 q)\big)$. For an unrooted tree on $n+1$ leaves under plain UC the same holds with $p^3$ replaced by $p^4$. The bound remains valid if $p(x) \ge p$ for all $x$.

(ii) Conversely, there are (exponentially many) trees $T$ for which

$$\mathbb P(E_k(T)) \;\le\; \big(1 - (1 - p^3 q)^k\big)^{\lfloor n/3 \rfloor},$$

so for such trees $k$ must grow like $\ln(n/\varepsilon)/(-\ln(1-p^3 q))$ to reach probability $1 - \varepsilon$.

## Depends on

- [Decisiveness of taxon coverage for all trees and the triple-covering bound](decisiveness-for-all-trees-and-the-triple-covering-bound.md)

## Expansion

A collection of rooted induced subtrees defines $T$ exactly when every internal edge $e$ of $T$ is distinguished by some subtree, that is, some kept triple $ab|c$ has $a$ and $b$ in the two subtrees below $e$ and $c$ in the sibling subtree. If these three subtrees contain $n_1, n_2, n_3 \ge 1$ taxa, one locus distinguishes $e$ with probability $q\prod_{t=1}^{3}\big(1 - (1-p)^{n_t}\big) \ge p^3 q$, so $e$ is missed by all $k$ loci with probability at most $(1 - p^3 q)^k$; a union bound over the $n-2$ internal edges gives (i). For (ii), hang a 3-leaf rooted tree from each leaf of an arbitrary tree on $\lfloor n/3 \rfloor$ leaves: each of the $\lfloor n/3 \rfloor$ new edges has exactly one leaf in each of its three subtrees, so it is distinguished with probability exactly $p^3 q$ per locus, and these edge events are independent. Without a reference taxon, unrooted definition needs quartets through a common leaf, which costs one more factor of $p$. The bound in (ii) is the product form appearing in the Appendix proof.

## Sources

- M. J. Sanderson, M. M. McMahon, M. Steel, "Phylogenomics with incomplete taxon coverage: the limits to inference", BMC Evolutionary Biology 10:155 (2010), Theorem 2 and the Appendix proof of Theorem 2, <https://doi.org/10.1186/1471-2148-10-155>, PMCID PMC2897806.