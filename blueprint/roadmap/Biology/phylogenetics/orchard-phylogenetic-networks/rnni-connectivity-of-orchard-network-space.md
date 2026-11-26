# rNNI connectivity of the space of orchard networks

Let $N$ be a binary network with an arc $(z,w)$ and an arc $e$ with endpoints $x$ and $y$, and let $p$ and $c$ be the parent and child of $x$ other than $y$. The **rSPR move** $(p,x,c)\xrightarrow{e}(z,w)$ replaces the arcs $(p,x)$, $(x,c)$, $(z,w)$ by $(p,c)$, $(z,x)$, $(x,w)$; it is an **rNNI move** if $\{p,c\}\cap\{z,w\}\ne\emptyset$, and it is valid if the result is a network.

**Validity via labellings.** If $N$ is a binary orchard network and the graph produced by an rSPR move admits an HGT-consistent labelling (defined for directed graphs with parallel arcs allowed), then that graph has no parallel arcs and no directed cycle, so the move is valid and the result is orchard.

**Theorem.** For $n\ge2$ leaves and $k\ge0$ reticulations, the space of binary [orchard](orchard-networks-and-cherry-picking.md) networks on a fixed taxon set is connected under rNNI moves, with diameter at most

$$4kn+n\lceil\log_2 n\rceil+2k+6n-8=O(kn+n\log n).$$

For $n=1$ the space consists of the one-leaf tree alone (a reducible pair needs two distinct leaves, so no reticulation can be added) and has diameter $0$; the displayed formula, which would give $-2$, does not apply. Since every rNNI move is an rSPR move, the same space is connected under rSPR moves with the same diameter bound.

## Depends on

- [HGT-consistent labellings characterize orchard networks](hgt-consistent-labellings-characterize-orchard-networks.md)
- [Orchard networks and cherry picking](orchard-networks-and-cherry-picking.md)

## Expansion

Fix a leaf $l$ and normalize each of the two networks. Every reticulation is moved to the top of the network, just below the root, with at most $2n$ rNNI moves per reticulation (Lemma 8), keeping an HGT-consistent labelling so each intermediate graph is a valid orchard network. At most $k$ further moves reorient the horizontal arcs at the top so that $l$ lies below the head of the lowest one, and at most $2n-4$ moves put every other leaf below its tail (Lemma 9). When $k=0$ there are no horizontal arcs and these reticulation steps are vacuous. The two networks now differ only in a tree $T_i$ on the $n-1$ leaves other than $l$, and the rNNI diameter of rooted binary trees, at most $2n+n\lceil\log_2 n\rceil$, finishes the job: $2(2kn+k+2n-4)+2n+n\lceil\log_2n\rceil$ is the stated bound. Connectivity matters for Bayesian MCMC over orchard networks with local moves.

## Sources

- L. van Iersel, R. Janssen, M. Jones, Y. Murakami, *Orchard networks are trees with additional horizontal arcs*, Bulletin of Mathematical Biology 84 (2022), <https://doi.org/10.1007/s11538-022-01037-z> (PMCID: PMC9213324). Section 4: Definitions 7–8, Lemma 4, Lemmas 8–9, Theorem 3 (with its proof) and Corollary 2.
