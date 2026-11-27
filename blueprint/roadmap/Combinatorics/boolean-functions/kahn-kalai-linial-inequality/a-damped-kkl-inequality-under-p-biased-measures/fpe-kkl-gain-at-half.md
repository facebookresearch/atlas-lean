# KKL inequality with constant $2$ at $p = 1/2$

Let $E$ be a finite nonempty set and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\mathrm{Inf}_e = \mathbb{E}\lvert f(x^{e \to 1}) - f(x^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the uniform measure on $\{0, 1\}^E$, $\delta = \max_{e \in E} \mathrm{Inf}_e$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. Then

$$2\, \mathrm{Var}(f) \log \frac{1}{\delta} \le I,$$

with the variance taken under the uniform measure (with $\log(1/\delta)$ read as $0$ when $\delta = 0$). This is the case $p = 1/2$ of the [damped KKL inequality](fpe-damped-var-log-gain.md), where the damped variance is the [variance](fpe-q-eq-var-at-half.md).
