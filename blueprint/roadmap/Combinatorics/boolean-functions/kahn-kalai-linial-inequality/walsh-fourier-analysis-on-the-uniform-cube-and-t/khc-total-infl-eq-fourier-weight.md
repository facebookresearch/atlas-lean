# Total influence as Fourier weight

Let $E$ be a finite set and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$, with [Walsh–Fourier coefficients](khc-fourier-coeff.md) $\hat f(S)$. Its total [influence](../../osss-inequality-for-decision-trees/infl.md) under the uniform measure is

$$\sum_{e \in E} \mathbb{E}\big\lvert f(x^{e \to 1}) - f(x^{e \to 0})\big\rvert = \sum_{S \subseteq E} 4 \lvert S\rvert\, \hat f(S)^2.$$
