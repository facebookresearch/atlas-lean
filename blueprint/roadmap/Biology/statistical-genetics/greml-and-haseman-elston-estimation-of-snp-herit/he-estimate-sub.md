# Haseman–Elston error formula when some $A_{ij}$ with $i<j$ is nonzero

Let $A$ be a real $N \times N$ matrix with $S = \sum_{i<j} A_{ij}^2 \ne 0$, that is, some entry
$A_{ij}$ with $i < j$ is nonzero, let $y \in \mathbb{R}^N$ and let $h \in \mathbb{R}$. Then the
[Haseman–Elston estimator](he-estimate.md) $\hat h^2$ satisfies

$$\hat h^2 - h = \frac{1}{S} \sum_{i<j} A_{ij} \bigl(y_i y_j - h A_{ij}\bigr):$$

the estimation error is the sum, over the [pairs](../../bioinformatics/sequence-alignment/multiple-sequence-alignment/pair-finset.md) $i < j$, of the deviations
$y_i y_j - h A_{ij}$ of the cross-products from $h A_{ij}$, weighted by $A_{ij} / S$.
