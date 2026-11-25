# Indicator-bound form of KKL implies the hypercontractive form

For every real number $c$: if the [Fourier-form KKL inequality conditional on the indicator Bonami–Beckner bound](kls-log-optimisation.md) holds with constant $c$, then so does the Fourier-form KKL inequality conditional on hypercontractivity: for every finite nonempty set $E$ and every indicator $f = 1_A$ of a set $A \subseteq \{0, 1\}^E$, if $\sum_{S \subseteq E} \rho^{2\lvert S\rvert} \hat f(S)^2 \le \lVert f\rVert_{1+\rho^2}^2$ for every $\rho \in [0, 1]$, then

$$c \Big(\sum_{\emptyset \ne S \subseteq E} \hat f(S)^2\Big) \log \frac{1}{\delta} \le \sum_{S \subseteq E} 4 \lvert S\rvert\, \hat f(S)^2$$

(with $\log(1/\delta)$ read as $0$ when $\delta = 0$). Here $\hat f(S)$ are the Walsh–Fourier coefficients of $f$, $\lVert f\rVert_r = (\mathbb{E}\lvert f\rvert^r)^{1/r}$ under the uniform measure, and $\delta$ is the maximal [influence](../../osss-inequality-for-decision-trees/infl.md) of $f$.
