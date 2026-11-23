# The branch length score

Let $T$ be an [unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md) on a finite set $X$ with real edge lengths $w$, and $S \subseteq X$. For a dart $(p, v)$ let $B(p, v)$ be the set of taxa $x$ whose leaf $\ell_x$ satisfies $\mathrm{dist}(\ell_x, v) < \mathrm{dist}(\ell_x, p)$. The branch length score of $S$ is

$$\mathrm{BLS}(S) = \frac12 \sum_{(p, v)} w(pv)\, [S \text{ meets both } B(p, v) \text{ and } X \setminus B(p, v)],$$

the sum running over the darts of $T$: the total length of the edges of the smallest subtree connecting the leaves of $S$.
