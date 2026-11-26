# Kahn–Kalai–Linial inequality

Let $p$ and $c$ be real numbers such that the [KKL inequality with constant $c$](kklhypercontractive.md) holds at $p$. Then for every finite nonempty set $E$ and every set $A \subseteq \{0, 1\}^E$, with $f = 1_A$,

$$c\, \mathrm{Var}_p(f) \log \frac{1}{\max_{e \in E} \mathrm{Inf}_e} \le \sum_{e \in E} \mathrm{Inf}_e,$$

with $\log(1/0)$ read as $0$, $\log x = \log \lvert x\rvert$ for $x < 0$, and the variance and [influence](../../osss-inequality-for-decision-trees/infl.md) taken for the product weights $w_p(1) = p$, $w_p(0) = 1 - p$ (J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988).
