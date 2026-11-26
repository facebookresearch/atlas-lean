# B-quartet inference rule on phylogenetic networks

Let $\mathcal{N}^+$ be a rooted binary phylogenetic network on $n \ge 5$ taxa, and suppose
$\{a, b, c, d\}$ and $\{b, c, d, e\}$ are both [B-quartets](blob-and-tree-of-blobs-of-a-phylogenetic-network.md)
on $\mathcal{N}^+$. Say two taxa $a, e$ are **separated** in a resolved quartet if they lie in
different cherries (i.e., $ab|ce$ or $ac|be$, not $ae|bc$).

If, on the induced 4-taxon network, at least one of $\{a, b, c, e\}$, $\{a, b, d, e\}$, or
$\{a, c, d, e\}$ is either:
- a T-quartet with $a$ and $e$ separated in the reduced unrooted tree of blobs of that induced 4-taxon network, or
- a B-quartet,

then all three of $\{a, b, c, e\}$, $\{a, b, d, e\}$, and $\{a, c, d, e\}$ are B-quartets
on $\mathcal{N}^+$.

## Depends on

- [Blobs and the reduced unrooted tree of blobs of a phylogenetic network](blob-and-tree-of-blobs-of-a-phylogenetic-network.md)

## Expansion

The triple $\{b, c, d\}$ determines a unique blob $B$ corresponding to a node $v$ in
$T_{\mathrm{rd}}(\mathcal{N}^-)$. Because $\{a, b, c, d\}$ and $\{b, c, d, e\}$ are
B-quartets, $a$ and $e$ attach to $B$ via cut edges distinct from those leading to $b, c, d$.
The hypothesis rules out $a$ and $e$ attaching through the same cut edge of $B$, forcing all five
taxa to lie in five distinct components upon deleting the cut edges incident to $B$; hence every
4-subset containing $\{a, e\}$ and two of $\{b, c, d\}$ is a B-quartet.

## Sources

- E. S. Allman, H. Baños, J. D. Mitchell, and J. A. Rhodes, "The tree of blobs of a species network: identifiability under the coalescent", Journal of Mathematical Biology 86 (2023), 10 (published online 2022), <https://doi.org/10.1007/s00285-022-01838-9> (PMC10062380). (Theorem 2.)
