# The probability of necessity under monotonicity

**The probability of necessity under monotonicity** (Pearl, *Statistics Surveys* 2009,
eq. (53) and Theorem 3): let $M$ be a Markovian structural causal model on the nodes
$0, \dots, n - 1$ whose variables all take values in $\{0, 1\}$ (the framework uses one value
type), with disturbances in a finite set, and let $X = X_i$ be the treatment and $Y = X_j$ the
outcome. The probability of necessity $\mathrm{PN} = P(Y_{x'} = y' \mid X = x, Y = y)$ (with
$x, y$ the value $1$ and $x', y'$ the value $0$) is identified from the observational law and the
interventional law of $\mathrm{do}(X_i = 0)$ when $Y$ is monotonic in $X$ ($Y_{x'}(u) = 1$
implies $Y_x(u) = 1$ for every disturbance value $u$) and $P(x, y) > 0$:

$$\mathrm{PN} = \frac{P(y) - P(y \mid \mathrm{do}(x'))}{P(x, y)}.$$

[Pearl's formula](cf-prob-necessity-eq.md) rewrites this as the right-hand side of eq. (54).
Pearl needs only the treatment and the outcome to be binary.

The probability of necessity is a counterfactual (third-rung) quantity: it conditions on the
factual treatment and outcome and asks about the outcome under the opposite treatment. It is not
identified in general; monotonicity, together with the interventional law of $\mathrm{do}(x')$,
makes it identifiable. The proof is pointwise in the disturbances: by consistency, a unit with
$X = x$ has $Y = Y_x$, and a unit with $X = x'$ has $Y = Y_{x'}$, so under monotonicity the
indicator of $\{X = x, Y = y, Y_{x'} = y'\}$ equals that of $\{Y = y\}$ minus that of
$\{Y_{x'} = y\}$.
