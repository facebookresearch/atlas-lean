# Pearl's formula for the probability of necessity

**Pearl's formula for the probability of necessity** (Pearl, *Statistics Surveys* 2009,
Theorem 3, eq. (54)): let $M$ be a Markovian structural causal model on the nodes
$0, \dots, n - 1$ whose variables all take values in $\{0, 1\}$, with disturbances in a finite
set, and let $i, j$ be a treatment and an outcome node. Write $x, y$ for $X_i = 1, X_j = 1$ and
$x', y'$ for $X_i = 0, X_j = 0$. If $Y$ is monotonic in $X$ (for every disturbance value $u$,
$Y_{x'}(u) = 1$ implies $Y_x(u) = 1$) and $P(x, y) > 0$, then

$$\mathrm{PN} = \frac{P(y \mid x) - P(y \mid x')}{P(y \mid x)} + \frac{P(y \mid x') - P(y \mid \mathrm{do}(x'))}{P(x, y)},$$

the excess risk ratio plus a correction for confounding, where
$\mathrm{PN} = P(Y_{x'} = y' \mid X = x, Y = y)$ and a conditional probability given a null event
is $0$.
