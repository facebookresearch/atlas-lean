# Bonami–Beckner applied to a discrete derivative

Let $E$ be a finite set and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$, with Walsh–Fourier coefficients $\hat f(S)$ under the uniform measure, and let $\mathrm{Inf}_e = \mathbb{E}\lvert f(x^{e \to 1}) - f(x^{e \to 0})\rvert$ be the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$. For every $\rho \in [0, 1]$ and every $e \in E$,

$$\sum_{S \ni e} \rho^{2\lvert S \setminus \{e\}\rvert} \cdot 4 \hat f(S)^2 \le \mathrm{Inf}_e^{2/(1 + \rho^2)}.$$

The left side is $\lVert T_\rho\, \partial_e f\rVert_2^2$ for the discrete derivative $\partial_e f$, so this is the Bonami–Beckner inequality $\lVert T_\rho g\rVert_2 \le \lVert g\rVert_{1+\rho^2}$ applied to $g = \partial_e f$, whose values lie in $\{-1, 0, 1\}$.
