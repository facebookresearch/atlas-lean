# Density of an exponential family with base weights

Let $X$ be a finite set, $\iota$ a finite index set, $h : X \to \mathbb{R}$ base weights and
$T : X \to \mathbb{R}^\iota$ a sufficient statistic. The density at the natural parameter
$\eta \in \mathbb{R}^\iota$ is

$$p_\eta(x) = h(x)\, e^{\eta \cdot T(x) - A(\eta)} ,$$

where $A(\eta)$ is the [log-partition function](log-partition-2.md), the logarithm of
$\sum_{y \in X} h(y) e^{\eta \cdot T(y)}$ with $\log y = \log |y|$ for $y < 0$ and $\log 0 = 0$. When
$h$ is nonnegative with positive total mass, $p_\eta$ is nonnegative and sums to $1$: a probability
mass function on $X$. Unlike [the density of a finite exponential family](density.md), it carries
base weights $h$ and a statistic in $\mathbb{R}^\iota$.
