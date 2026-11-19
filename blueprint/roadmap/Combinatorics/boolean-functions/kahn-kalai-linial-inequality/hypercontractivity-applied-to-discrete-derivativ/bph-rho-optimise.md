# Fourier-form KKL at $p = 1/2$ conditional on the capped estimate

For a real number $c$, this is the assertion that for every finite nonempty set $E$ and every indicator $f = 1_A$ of a set $A \subseteq \{0, 1\}^E$: if

$$\sum_{\emptyset \ne S \subseteq E} 4 \lvert S\rvert\, \rho^{2(\lvert S\rvert - 1)}\, \hat f(S)^2 \le \delta^{2/(1 + \rho^2) - 1} \sum_{\emptyset \ne S \subseteq E} 4 \lvert S\rvert\, \hat f(S)^2$$

for every $\rho \in [0, 1]$, then

$$c \Big(\sum_{\emptyset \ne S \subseteq E} \hat f(S)^2\Big) \log \frac{1}{\delta} \le \sum_{S \subseteq E} 4 \lvert S\rvert\, \hat f(S)^2$$

(with $\log(1/\delta)$ read as $0$ when $\delta = 0$). Here $\hat f(S)$ are the Walsh–Fourier coefficients of $f$ under the uniform measure and $\delta = \max_e \mathrm{Inf}_e$ is its maximal [influence](../../osss-inequality-for-decision-trees/infl.md). The hypothesis always holds by the [capped per-coordinate estimate](bph-capped-hc.md), and the assertion is true with $c = 2$.
