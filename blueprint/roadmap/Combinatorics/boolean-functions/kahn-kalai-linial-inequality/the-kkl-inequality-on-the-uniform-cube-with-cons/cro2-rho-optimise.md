# KKL inequality

For every finite nonempty set $E$ and every set $A \subseteq \{0, 1\}^E$, with $f = 1_A$, Walsh–Fourier coefficients $\hat f(S)$ and maximal [influence](../../osss-inequality-for-decision-trees/infl.md) $\delta$ under the uniform measure,

$$2 \Big(\sum_{\emptyset \ne S \subseteq E} \hat f(S)^2\Big) \log \frac{1}{\delta} \le \sum_{S \subseteq E} 4 \lvert S\rvert\, \hat f(S)^2$$

(with $\log(1/\delta)$ read as $0$ when $\delta = 0$). Precisely, the [Fourier form of the KKL inequality conditional on the capped estimate](../hypercontractivity-applied-to-discrete-derivativ/bph-rho-optimise.md) holds with $c = 2$, and its hypothesis always holds. This is the KKL inequality for the uniform measure (after J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988; the proof follows D. Falik, A. Samorodnitsky, *Edge-isoperimetric inequalities and influences*, 2007).
