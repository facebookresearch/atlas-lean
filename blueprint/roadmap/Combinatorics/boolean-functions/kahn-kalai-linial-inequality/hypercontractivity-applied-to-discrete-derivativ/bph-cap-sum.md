# Sum of influence powers capped by the maximal influence

Let $E$ be a finite nonempty set and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S) = 2^{-\lvert E\rvert} \sum_{x} f(x) \prod_{i \in S} (-1)^{x_i}$, for $S \subseteq E$, for its [Walsh–Fourier coefficients](../walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-fourier-coeff.md), $\mathrm{Inf}_e = \mathbb{E}\lvert f(x^{e \to 1}) - f(x^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the uniform measure on $\{0, 1\}^E$, $\delta = \max_{e \in E} \mathrm{Inf}_e$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. For every $\rho \in [0, 1]$, with $\theta = 2/(1 + \rho^2)$,

$$\sum_{e \in E} \mathrm{Inf}_e^{\theta} \le \delta^{\theta - 1} \sum_{S \subseteq E} 4 \lvert S\rvert\, \hat f(S)^2.$$
