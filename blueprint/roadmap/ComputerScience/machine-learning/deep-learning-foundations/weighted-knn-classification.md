# Weighted k-nearest-neighbor classification

Encode a query and labelled training examples as nonzero vectors, then normalize them to $u$ and $u_i$ of unit length. For $n$ labelled training examples and $1\le k\le n$, let $N_k$ be the $k$ training IDs of largest $u^\top u_i$, breaking ties by index. For temperature $\tau>0$, assign each class $c$ the score

$$s(c)=\sum_{i\in N_k}\mathbf1\{y_i=c\}\exp(u^\top u_i/\tau).$$

Return a class maximizing this score, using a fixed ordering of the finite class set to resolve a tie. Normalizing all scores by their common positive sum does not affect the prediction. This tests a frozen representation using training labels without fitting a new classifier.

## Depends on

- [Exact top-k neighbors in embedding space](top-k-neighbors-in-embedding-space.md)

## Background

- [Contrastive learning with paired views (NT-Xent)](contrastive-loss-for-paired-views.md)

## Sources

- Wu et al., [*Unsupervised Feature Learning via Non-parametric Instance Discrimination*](https://arxiv.org/abs/1805.01978) (CVPR 2018), §3.4, weighted kNN classifier.
