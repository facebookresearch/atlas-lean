# Tree-child sequences decide network containment in linear time

**Setting.** Networks, cherries, reticulated cherries, reductions and cherry-picking sequences (CPS) are as in the companion article. A network is *tree-child* if it has no reticulation whose child is a reticulation (stack-free) and every tree node has a child that is a tree node or a leaf. A CPS is a *tree-child sequence* (TCS) if no leaf that occurs as a first coordinate occurs as a second coordinate later in the sequence. A network $N'$ is *contained* in $N$ if $N'$ can be obtained from $N$ by deleting reticulation edges, suppressing degree-$2$ vertices and contracting edges. A network is *semi-binary* if every tree node has out-degree $2$ (reticulations may have any in-degree $\ge 2$).

**Theorem.** Every tree-child network is reduced by some TCS. Let $N$ and $N'$ be tree-child networks on the same leaf set $X$ that lie in a common reconstructible class of cherry-picking networks. Then

$$ N' \text{ is contained in } N \iff \text{every TCS of } N \text{ reduces } N' , $$

and in that case any single TCS of $N$ already witnesses containment. For semi-binary tree-child networks the same statement holds with "contained in" replaced by "is a subnetwork of" (obtained by deleting reticulation edges and suppressing degree-$2$ vertices).

**Algorithm.** Given semi-binary tree-child networks $N$ and $N'$ on $X$, with $r$ the reticulation number of $N$, one can decide in time $O(|X|+r)$ whether $N'$ is a subnetwork of $N$: compute one minimal TCS of $N$ in $O(|X|+r)$ time and test whether it reduces $N'$ in time linear in its length. Consequently, isomorphism of two semi-binary tree-child networks on $X$ is also decidable in $O(|X|+r)$ time.

## Depends on

- [Minimal cherry-picking sequences and reconstructible network classes](minimal-cherry-picking-sequences-and-reconstructible-network-classes.md)

## Expansion

One direction holds for all cherry-picking networks in a reconstructible class: if a minimal sequence for $N$ also reduces $N'$, then reducing both in parallel and re-attaching pairs in reverse embeds $N'$ in a refinement of $N$. The converse fails for general cherry-picking networks (the paper exhibits a network containing a tree that no minimal sequence of the network reduces), and this is where the tree-child property enters: a TCS never reuses a leaf that has already been picked as a first coordinate, so reducing a tree-child network and any tree-child subnetwork by the same TCS keeps the subnetwork relation at every step. The linear bound uses constant-time detection of a reducible pair containing a given leaf and constant-time reductions.

## Sources

- R. Janssen and Y. Murakami, *On cherry-picking and network containment*, arXiv:1812.08065 (2018). <https://doi.org/10.48550/arXiv.1812.08065> Lemma 16, Theorem 5 and Theorem 6 (Section 5), Lemma 24, Theorem 7 and Corollary 5 (Section 6); Theorem 4 (Section 4) for the counterexample in general cherry-picking networks. Published version: Theoretical Computer Science 856 (2021) 121–150, <https://doi.org/10.1016/j.tcs.2020.12.031>.
