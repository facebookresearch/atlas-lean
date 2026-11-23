# Kahn–Kalai–Linial inequality

For every finite nonempty set $E$ and every set $A \subseteq \{0, 1\}^E$, with $f = 1_A$ and the uniform measure on $\{0, 1\}^E$,

$$2\, \mathrm{Var}(f) \log \frac{1}{\max_{e \in E} \mathrm{Inf}_e} \le \sum_{e \in E} \mathrm{Inf}_e,$$

where $\mathrm{Inf}_e$ is the probability that $e$ is pivotal for $A$ and $\log(1/0)$ is read as $0$ (J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988; the proof follows D. Falik and A. Samorodnitsky, 2007). This is the [KKL inequality with constant $2$](../the-kkl-inequality-statement-and-elementary-boun/kklhypercontractive.md) at $p = 1/2$, the case $p = 1/2$ of the $p$-biased KKL inequality.
