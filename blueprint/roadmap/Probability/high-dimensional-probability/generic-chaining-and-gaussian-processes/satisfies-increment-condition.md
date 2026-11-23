# Sub-Gaussian increment condition

A process $(X_t)_{t \in T}$ of real random variables on a probability space, indexed by a pseudometric space
$(T, d)$, satisfies the increment condition when

$$\mathbb{P}(|X_s - X_t| \ge u) \le 2\exp\Big(-\frac{u^2}{2 d(s, t)^2}\Big)$$

for all $s, t \in T$ and $u > 0$ (Talagrand, *Upper and Lower Bounds for Stochastic Processes*,
2nd ed., 2021, (2.4)). A centred Gaussian process satisfies it for its canonical distance
$d(s, t) = (\mathbb{E}(X_s - X_t)^2)^{1/2}$.

When $d(s, t) = 0$ the right-hand side is read with $u^2/0 = 0$, so it equals $2$ and the condition says nothing
about $X_s - X_t$. The generic chaining bounds are stated for metric spaces, where $d(s, t) = 0$ only for
$s = t$.
