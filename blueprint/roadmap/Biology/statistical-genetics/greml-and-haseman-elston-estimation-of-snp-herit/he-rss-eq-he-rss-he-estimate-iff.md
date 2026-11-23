# Unique Haseman–Elston slope when some $A_{ij}$ with $i<j$ is nonzero

Let $A$ be a real $N \times N$ matrix with $\sum_{i<j} A_{ij}^2 \ne 0$, that is, some entry
$A_{ij}$ with $i < j$ is nonzero, and let $y \in \mathbb{R}^N$. Then a slope $b \in \mathbb{R}$
has the same [residual sum of squares](he-rss.md) as the
[Haseman–Elston estimator](he-estimate.md) $\hat h^2$ only if it equals it:

$$\mathrm{RSS}(b) = \mathrm{RSS}(\hat h^2) \iff b = \hat h^2.$$

Since $\hat h^2$ [minimizes the residual sum of squares](he-rss-he-estimate-le.md), it is the
unique least-squares slope.
