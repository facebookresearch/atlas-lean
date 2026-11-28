# Weight of a text representation of a k-mer multiset and the minimum-word criterion

**Definitions.** Fix $k\ge 2$. For a word $w=w_1\cdots w_\ell$ with $\ell\ge k$, its $k$-mer multiset $\mathrm{km}(w)$ consists of the $\ell-k+1$ windows $w_i\cdots w_{i+k-1}$; for a set of words $\mathbb W$, $\mathrm{km}(\mathbb W)$ is the multiset union. A *text representation* of a $k$-mer multiset $\mathbb M$ is a set of words $\mathbb W$ with $\mathrm{km}(\mathbb W)=\mathbb M$ (frequencies included). Its *weight*, the total length with one separator between consecutive words, is

$$\omega(\mathbb W) = \sum_{w\in\mathbb W}|w| + |\mathbb W| - 1,$$

and storing $\mathbb M$ as a plain list of $k$-mers has weight $\omega(\mathbb M) = (k+1)|\mathbb M| - 1$. $\mathbb W$ is a *compressed* text representation if $\omega(\mathbb W)<\omega(\mathbb M)$, with compression ratio $\mathrm{cr}_{\mathbb M}(\mathbb W)=\omega(\mathbb M)/\omega(\mathbb W)$.

**Theorem.** For every text representation $\mathbb W$ of $\mathbb M$,

$$\omega(\mathbb W) = |\mathbb M| + k\,|\mathbb W| - 1.$$

Hence the weight-optimal representations are exactly those with the fewest words,

$$\arg\min_{\mathrm{km}(\mathbb W)=\mathbb M}\omega(\mathbb W) = \arg\min_{\mathrm{km}(\mathbb W)=\mathbb M}|\mathbb W|,$$

and every compressed representation satisfies

$$\mathrm{cr}_{\mathbb M}(\mathbb W) \le k+1-\frac{k^2}{|\mathbb M|+k-1} < k+1.$$

## Depends on

- [The k-mers of a string](../../de-bruijn-graph-genome-assembly/kmers.md)

## Expansion

Each word $w$ contributes $|w|-k+1$ $k$-mers, so $|\mathbb M| = \sum_w|w| - (k-1)|\mathbb W|$; substituting into the weight gives the identity. The weight is therefore an increasing affine function of the number of words, and the best possible case is a single word, $\omega=|\mathbb M|+k-1$, which yields the ratio bound. In de Bruijn graph terms, each word spells a trail and the words of $\mathbb W$ form an edge-disjoint trail cover of the de Bruijn multigraph of $\mathbb M$, so minimizing weight is the same as finding an Eulerian cover with the fewest trails (see minimum Eulerian covers).

## Sources

- Herman Z. Q. Chen, Sergey Kitaev, Xiaoyu Lang, Artem Pyatkin, Runbin Tang, "Efficient $k$-mer dataset compression using Eulerian covers of de Bruijn graphs and BWT", RAIRO - Theoretical Informatics and Applications 59 (2025), 20, <https://doi.org/10.1051/ita/2025020>. Published version of arXiv:2510.22404, cited next; locators there refer to the arXiv version.
- H. Z. Q. Chen, S. Kitaev, X. Lang and A. Pyatkin, "Efficient k-mer Dataset Compression Using Eulerian Covers of de Bruijn Graphs and BWT", arXiv:2510.22404 (2025), Section "Preliminaries" (Theorems 1 and 2), Section "Algorithm for Minimum Compressed Text Representation" (Lemma 1, local Eulerization and Eulerian cover generation algorithms, complexity analysis), <https://doi.org/10.48550/arXiv.2510.22404>.
