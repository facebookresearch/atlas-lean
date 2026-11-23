# KKL inequality with constant $c$ for the $p$-biased measure

For real numbers $p$ and $c$, the KKL inequality with constant $c$ at $p$ is the assertion that for every finite nonempty set $E$ and every set $A \subseteq \{0, 1\}^E$, with $f = 1_A$,

$$c\, \mathrm{Var}_p(f) \log \frac{1}{\max_{e \in E} \mathrm{Inf}_e} \le \sum_{e \in E} \mathrm{Inf}_e,$$

with $\log(1/0)$ read as $0$ and $\log x = \log \lvert x\rvert$ for $x < 0$. Here $\mathrm{Var}_p$ is the [variance](../../osss-inequality-for-decision-trees/var.md) and $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ the [influence](../../osss-inequality-for-decision-trees/infl.md) for the product weights $w_p(1) = p$, $w_p(0) = 1 - p$, which for $p \notin [0, 1]$ are signed.

For $0 \le p \le 1$ these are the variance and the pivotal probabilities under the $p$-biased product measure, the assertion then holds trivially with $c = 0$ ([nonnegativity of the total influence](kkl-hypercontractive-zero.md)), and it holds at $p = 1/2$ with $c = 2$ ([the Kahn–Kalai–Linial inequality](../the-kkl-inequality-at-p-1-2-and-the-p-biased-bas/fsr-pbiased-endpoint.md)).
