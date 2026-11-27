# Level-2 semi-directed networks are encoded by quarnets

**Setting.** Semi-directed binary phylogenetic networks $N$ on $X$, restrictions $N|_A$, quarnets and $Q(N)$ are as in the companion article. A network is *simple* if deleting its leaves leaves a single blob, *level-$k$* if every blob contains at most $k$ reticulations, and *strict level-$k$* if moreover some blob contains exactly $k$. A class $\mathcal C$ of semi-directed phylogenetic networks with at least four leaves is **encoded by quarnets** if, for every $N\in\mathcal C$ and every semi-directed phylogenetic network $N'$ on the same leaf set, $Q(N)\simeq Q(N')$ implies $N\cong N'$ (with $N'$ unrestricted); it is *weakly encoded* if this holds whenever both $N,N'\in\mathcal C$.

**Theorem.**

1. The class of simple level-2 semi-directed binary phylogenetic networks with at least four leaves is weakly encoded by quarnets.
2. If $N$ is strict level-$k$ with $k\ge3$ and $|X|\ge4$, then some quarnet in $Q(N)$ is not level-2.
3. **(Main result.)** The class of level-2 semi-directed binary phylogenetic networks with at least four leaves is encoded by quarnets.
4. **(Sharpness.)** The class of level-3 semi-directed binary phylogenetic networks with at least four leaves is *not* encoded by quarnets: there are two non-isomorphic level-3 networks with the same five quarnets, and the example extends to any number of leaves.

## Depends on

- [Quarnet detection of cut-edge splits and blob-tree encoding](quarnet-detection-of-cut-edge-splits-and-blob-tree-encoding.md)

## Expansion

Let $N$ be level-2 and $Q(N)\simeq Q(N')$. By part 2, $N'$ is also level-2: a blob with $k\ge3$ reticulations can be covered by three overlapping "excellent" cycles whose sinks lead to four leaves, and the restriction to those leaves keeps a non-level-2 blob. Induct on the number of non-trivial cut-edge splits of $N$, which equal those of $N'$ by the quarnet split test. With none, both networks are simple level-2 and part 1 (a case analysis over the level-2 generators and the sides on which leaves hang) gives $N\cong N'$. Otherwise take a non-trivial split $A|B$, pick $a\in A$, $b\in B$; the quarnets of $N|_{A\cup\{b\}}$ and $N|_{B\cup\{a\}}$ are the quarnets of $N$ on those leaves, so these smaller restrictions agree for $N$ and $N'$ by induction, and $N$ is reassembled from them by deleting $a,b$ and rejoining along the cut-edge, identically for $N'$. Level $2$ is thus the largest level at which semi-directed networks are determined by four-taxon subnetworks.

## Sources

- Katharina T. Huber, Leo van Iersel, Mark Jones, Vincent Moulton and Leonie Veenema - Nipius, "When are Quarnets Sufficient to Reconstruct Semi-directed Phylogenetic Networks?", Bulletin of Mathematical Biology 87 (2025), 136, <https://doi.org/10.1007/s11538-025-01510-5>; numbering as in arXiv:2408.12997: Theorem 1.1 (level-3 counterexample), Theorem 4.5, Lemma 6.1, Theorem 6.2.
