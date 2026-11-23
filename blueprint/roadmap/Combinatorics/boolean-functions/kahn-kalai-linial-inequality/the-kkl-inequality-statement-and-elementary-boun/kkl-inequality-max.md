# Kahn–Kalai–Linial inequality

Let $p$ and $c$ be real numbers such that the [KKL inequality with constant $c$](kklhypercontractive.md) holds at $p$. Then for every finite nonempty set $E$ and every set $A \subseteq \{0, 1\}^E$, with $f = 1_A$ and $\delta = \max_e \mathrm{Inf}_e$,

$$c\, \mathrm{Var}_p(f) \log \frac{1}{\delta} \le \lvert E\rvert\, \delta$$

(with $\log(1/\delta)$ read as $0$ when $\delta = 0$, and $\log x = \log \lvert x\rvert$ for $x < 0$), where the variance and the [influence](../../osss-inequality-for-decision-trees/infl.md) are taken for the product weights $w_p(1) = p$, $w_p(0) = 1 - p$. For $0 \le p \le 1$ and $c > 0$ this says that $\delta$ is at least of order $\mathrm{Var}_p(f) \log \lvert E\rvert / \lvert E\rvert$ (J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988).
