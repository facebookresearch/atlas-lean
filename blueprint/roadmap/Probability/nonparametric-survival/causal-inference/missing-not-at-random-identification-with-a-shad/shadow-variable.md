# Shadow variable assumption (discrete-fibre form)

Let $\mathcal{Y}$ and $\mathcal{Z}$ be measurable spaces and let $P$ be a measure on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$, with coordinates $R$, $Y$, $Z$. $P$ satisfies the shadow variable assumption, in its discrete-fibre form, when for every measurable $B \subseteq \mathcal{Z}$ and every $y \in \mathcal{Y}$

$$P(R = \mathrm{true}, Z \in B, Y = y)\; P(Y = y) = P(R = \mathrm{true}, Y = y)\; P(Z \in B, Y = y),$$

all measures being read as real numbers (an infinite value counts as $0$). Only the test set $B$ must be measurable: a fibre $\{Y = y\}$ that is not measurable is evaluated by the outer measure.

When $\mathcal{Y}$ and $\mathcal{Z}$ have measurable singletons, $P$ is a probability measure and $\mathcal{Y}$ is countable, this condition is the conditional independence $Z \perp R \mid Y$. In general it is weaker, since it only tests the fibres $\{Y = y\}$: if $Y$ is uniform on $[0, 1]$, $R$ is an independent fair bit and $Z = R$, every fibre has probability $0$, so all the displayed products vanish, although $Z$ and $R$ are equal and not conditionally independent given $Y$.
