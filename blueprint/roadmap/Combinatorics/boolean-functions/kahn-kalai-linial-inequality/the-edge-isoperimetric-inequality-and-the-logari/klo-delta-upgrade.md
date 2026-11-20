# Fourier-form KKL inequality given the measure–influence bound

For a real number $c$, this is the assertion that for every finite nonempty set $E$ and every indicator $f = 1_A$ of a set $A \subseteq \{0, 1\}^E$, with mean $m = \mathbb{E} f$ under the uniform measure and $W = \sum_{S \subseteq E} 4 \lvert S\rvert \hat f(S)^2$: if

$$m - m^{2/(1 + \rho^2)} \le \frac{(1 - \rho^2)\, W}{4}$$

for every $\rho \in [0, 1]$, then

$$c \Big(\sum_{\emptyset \ne S \subseteq E} \hat f(S)^2\Big) \log \frac{1}{\delta} \le W$$

(with $\log(1/\delta)$ read as $0$ when $\delta = 0$). Here $\hat f(S)$ are the Walsh–Fourier coefficients of $f$ and $\delta = \max_e \mathrm{Inf}_e$ is its maximal [influence](../../osss-inequality-for-decision-trees/infl.md) under the uniform measure; $W$ is the total influence. The hypothesis always holds by the [bound on $m - m^{2/(1+\rho^2)}$](klo-master-le.md).
