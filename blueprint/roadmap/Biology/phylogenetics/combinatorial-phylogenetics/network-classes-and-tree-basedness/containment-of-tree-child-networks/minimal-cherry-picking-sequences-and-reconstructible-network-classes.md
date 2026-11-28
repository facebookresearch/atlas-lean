# Minimal cherry-picking sequences and reconstructible network classes

**Setting.** A (rooted) phylogenetic network on a finite taxon set $X$ is a directed acyclic multigraph with a root of out-degree $1$, leaves of in-degree $1$ bijectively labelled by $X$, tree nodes (in-degree $1$, out-degree $\ge 2$) and reticulations (in-degree $\ge 2$, out-degree $1$). An ordered pair of leaves $(x,y)$ with parents $p_x,p_y$ is a *cherry* if $p_x=p_y$ and a *reticulated cherry* if $p_x$ is a reticulation, $p_y$ is a tree node and $p_y$ is a parent of $p_x$. *Reducing* $(x,y)$ deletes $x$ (cherry) or the reticulation edge $p_y p_x$ (reticulated cherry), then suppresses degree-$2$ nodes; it does nothing if $(x,y)$ is neither. A sequence $S$ of ordered pairs *reduces* $N$ if applying its pairs in order leaves a single leaf below the root. A *cherry-picking sequence* (CPS) is a sequence of ordered pairs of distinct taxa in which the second coordinate of every pair occurs as a first coordinate later in the sequence, or is the second coordinate of the last pair. A *cherry-picking network* (CPN) is a network reduced by some CPS. Reversing a CPS rebuilds a network once one fixes, for cherries and for reticulated cherries, how a pair is re-attached; the paper lists such construction rules and calls a class of CPNs built with a fixed rule pair *reconstructible* if two networks of the class with a common minimal CPS are isomorphic.

**Results.**

1. If $S$ is a shortest sequence of ordered pairs that reduces a network $N$ with $n$ leaves and reticulation number $r$, then $S$ is a CPS and

$$ |S| = n + r - 1 . $$

2. *Order does not matter.* If $S$ is a partial CPS each of whose pairs changes the network when applied to a CPN $N$, then some minimal CPS of $N$ starts with $S$. In particular, reducing any reducible pair of a CPN leaves a CPN.
3. Fix a total order on $X$. Every CPN on $X$ has a unique lexicographically smallest minimal CPS, every CPS builds a unique CPN within each of the paper's eight construction classes, and within a reconstructible class two CPNs are isomorphic if and only if they have the same smallest CPS.

## Expansion

A cherry reduction removes one leaf and a reticulated-cherry reduction removes one reticulation edge, so any reducing sequence needs at least $n-1$ cherry steps and $r$ reticulated-cherry steps; a minimal one uses exactly these, and every useless pair can be deleted, which forces the CPS shape. The order-independence statement is proved by showing that the reducible pairs created or destroyed by one reduction only involve the two leaves of that pair, so a pair available now can be moved to the front of any minimal sequence. Choosing the smallest available pair at every step then gives a canonical sequence, which serves as an isomorphism certificate inside a reconstructible class.

## Sources

- R. Janssen and Y. Murakami, *On cherry-picking and network containment*, arXiv:1812.08065 (2018). <https://doi.org/10.48550/arXiv.1812.08065> Lemma 4, Theorem 1, Theorem 2 and Corollary 2 (Sections 2 and 3). Published version: Theoretical Computer Science 856 (2021) 121–150, <https://doi.org/10.1016/j.tcs.2020.12.031>.
