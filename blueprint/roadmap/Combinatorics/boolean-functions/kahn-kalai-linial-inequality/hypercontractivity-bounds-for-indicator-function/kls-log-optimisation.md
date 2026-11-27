# Fourier-form KKL inequality given the indicator Bonami–Beckner bound

For a real number $c$, this is the assertion that for every finite nonempty set $E$ and every indicator $f = 1_A$ of a set $A \subseteq \{0, 1\}^E$, with mean $m = \mathbb{E} f$ under the uniform measure: if

$$\sum_{\emptyset \ne S \subseteq E} \rho^{2\lvert S\rvert}\, \hat f(S)^2 \le m^{2/(1 + \rho^2)} - m^2$$

for every $\rho \in [0, 1]$, then

$$c \Big(\sum_{\emptyset \ne S \subseteq E} \hat f(S)^2\Big) \log \frac{1}{\delta} \le \sum_{S \subseteq E} 4 \lvert S\rvert\, \hat f(S)^2$$

(with $\log(1/\delta)$ read as $0$ when $\delta = 0$). Here $\hat f(S)$ are the Walsh–Fourier coefficients of $f$ and $\delta = \max_e \mathrm{Inf}_e$ is its maximal [influence](../../osss-inequality-for-decision-trees/infl.md) under the uniform measure. The hypothesis always holds by the [Bonami–Beckner bound for indicators](kls-fluct-weight-le-pow.md).
