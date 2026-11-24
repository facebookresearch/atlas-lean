# The Haseman–Elston estimator minimizes the residual sum of squares

For every real $N \times N$ matrix $A$, every $y \in \mathbb{R}^N$ and every slope
$b \in \mathbb{R}$, the [Haseman–Elston estimator](he-estimate.md) $\hat h^2$ satisfies

$$\mathrm{RSS}(\hat h^2) \le \mathrm{RSS}(b)$$

for the [residual sum of squares](he-rss.md). No condition on $A$ is needed: if every entry
$A_{ij}$ with $i < j$ is $0$, the residual sum of squares does not depend on the slope, and
$\hat h^2 = 0$ by the convention $x/0 = 0$.
