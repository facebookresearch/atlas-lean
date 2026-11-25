# Split decomposition of a tree metric and uniqueness of lengths

Let $X$ be a finite set with $|X|\ge2$, let $d$ be the tree metric of an $X$-tree with edge lengths positive on internal edges, and let $\beta$ be its [Buneman index](buneman-split-index-and-split-weights-of-a-tree.md). Let $\mathcal S^+=\{\sigma:\beta(\sigma)>0\}$ together with the trivial splits, and let $T$ be the $X$-tree with split set $\mathcal S^+$ given by [the realization theorem for compatible splits](pairwise-compatible-splits-determine-a-unique-un.md), with the edge inducing $\sigma$ given length $\beta(\sigma)$ (a trivial split has $\beta\ge0$ by the triangle inequality, so its pendant edge may have length $0$). Then for all $x,y\in X$

$$d(x,y)=\sum_{\sigma\in\mathcal S^+:\ \sigma\text{ separates }x,y}\beta(\sigma),$$

where $\sigma=A\mid B$ separates $x,y$ if exactly one of them lies in $A$. Moreover the edge lengths are unique given the topology: the split pseudometrics $\delta_\sigma(x,y)=[\sigma\text{ separates }x,y]$, $\sigma\in\Sigma(T)$, are linearly independent, so if $\sum_\sigma\lambda_\sigma\delta_\sigma=\sum_\sigma\lambda'_\sigma\delta_\sigma$ on $X\times X$ then $\lambda=\lambda'$.

The distance identity for a given tree with edge lengths, as a sum over darts, is [Split decomposition of a tree metric](dist-eq-sum-darts.md).

## Depends on

- [Pairwise compatible splits determine a unique unrooted X-tree](pairwise-compatible-splits-determine-a-unique-un.md)
- [Buneman split index and split weights of a tree metric](buneman-split-index-and-split-weights-of-a-tree.md)

## Proof depends on

- [Split decomposition of a tree metric](dist-eq-sum-darts.md)

## Expansion

A proof page must establish:

- by the Buneman index lemma, the splits with $\beta>0$ are exactly the splits of the internal edges of the original tree together with the positive-length pendant edges, with $\beta$ equal to the edge length, so they are pairwise compatible and the reconstructed tree is the original one up to zero-length pendant edges;
- the distance formula from the path-length identity of [Split decomposition of a tree metric](dist-eq-sum-darts.md);
- linear independence of the split pseudometrics of an $X$-tree, by induction or by evaluating at pairs of taxa adjacent across a single edge;
- an exact reconstruction of a four-leaf tree metric, and the linear independence of the five split pseudometrics of a four-leaf binary tree.

## Sources

- C. Semple and M. Steel, *Phylogenetics*, Oxford University Press (2003) (split decomposition of tree metrics).
