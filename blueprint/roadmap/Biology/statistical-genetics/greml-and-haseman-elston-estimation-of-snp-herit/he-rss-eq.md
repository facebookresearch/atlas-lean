# Pythagoras for the Haseman–Elston residual sum of squares

Let $A$ be a real $N \times N$ matrix with $S = \sum_{i<j} A_{ij}^2 \ne 0$, that is, some entry
$A_{ij}$ with $i < j$ is nonzero, let $y \in \mathbb{R}^N$, and let $\hat h^2$ be the
[Haseman–Elston estimator](he-estimate.md). Then for every slope $b \in \mathbb{R}$ the
[residual sum of squares](he-rss.md) satisfies

$$\mathrm{RSS}(b) = \mathrm{RSS}(\hat h^2) + (b - \hat h^2)^2\, S.$$
