# Contrastive learning with paired views (NT-Xent)

Draw two augmented views of each of $N\ge2$ examples. Let $p(i)$ index the other view of the same example. An encoder produces $h_i=f(x_i)$; a projection head produces $z_i=g(h_i)\ne0$. For $s_{ij}=z_i^\top z_j/(\|z_i\|_2\|z_j\|_2)$ and temperature $\tau>0$, the SimCLR loss is

$$\frac1{2N}\sum_{i=1}^{2N}-\log\frac{\exp(s_{i,p(i)}/\tau)}{\sum_{j\ne i}\exp(s_{ij}/\tau)}.$$

For each anchor the denominator includes its positive partner and $2N-2$ negatives, but excludes the anchor itself. The sum includes both directions of every positive pair. The projection is used for this loss; the encoder representation before projection is used for downstream prediction. Here the cross-entropy uses natural logarithms.

## Depends on

- [Multilayer perceptron (MLP)](multilayer-perceptron.md)
- [Softmax](../../not-yet-classified/basic/part-06/softmax.md)
- [Cross-entropy loss](../supervised-learning/cross-entropy-loss/cross-entropy-loss.md)

## Background

- [Exact top-k neighbors in embedding space](top-k-neighbors-in-embedding-space.md)

## Sources

- Chen et al., [*A Simple Framework for Contrastive Learning of Visual Representations*](https://proceedings.mlr.press/v119/chen20j.html) (ICML 2020), §2.1, equation (1) and algorithm 1.
