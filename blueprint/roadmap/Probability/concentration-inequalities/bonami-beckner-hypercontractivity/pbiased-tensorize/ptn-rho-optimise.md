# $p$-biased KKL inequality conditional on the capped estimate

For $q \in \mathbb{R}$, the conditional KKL statement at $q$ asserts: for every $p \in (1/2, q)$
with $p < 1$, every nonempty finite set $E$ and every $A \subseteq \{0, 1\}^E$ with indicator
$f = \mathbf{1}_A$, if the [capped estimate](ptn-capped-hc.md)

$$\frac{1}{p(1-p)} \sum_{S \ne \emptyset} |S|\, \rho^{2(|S|-1)}\, \hat f(S)^2 \le \Big(\max_e \mathrm{Inf}_e(f)\Big)^{2/q' - 1} \sum_e \mathrm{Inf}_e(f)$$

holds for all $\rho \in [0, 1]$ and $q' \in [1, 2]$ with $\rho^2 = 4p(1-p)(q'-1)$, then

$$2 \operatorname{Var}_p(f) \log \frac{1}{\max_e \mathrm{Inf}_e(f)} \le \sum_e \mathrm{Inf}_e(f) .$$
