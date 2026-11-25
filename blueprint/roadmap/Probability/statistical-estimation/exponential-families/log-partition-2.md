# Log-partition function of an exponential family with base weights

Let $X$ be a finite set, $\iota$ a finite index set, $h : X \to \mathbb{R}$ base weights and
$T : X \to \mathbb{R}^\iota$ a sufficient statistic. The log-partition function at the natural
parameter $\eta \in \mathbb{R}^\iota$ is

$$A(\eta) = \log \sum_{x \in X} h(x)\, e^{\eta \cdot T(x)} ,$$

with the real logarithm extended by $\log y = \log |y|$ for $y < 0$ and $\log 0 = 0$. When $h$ is
nonnegative with positive total mass, the sum is positive and $A$ is the log-partition function of
an exponential family. Unlike [the log-partition function of a finite exponential family](log-partition.md),
which uses the counting measure and a statistic in an inner product space, it carries base weights
$h$ and a statistic in $\mathbb{R}^\iota$.
