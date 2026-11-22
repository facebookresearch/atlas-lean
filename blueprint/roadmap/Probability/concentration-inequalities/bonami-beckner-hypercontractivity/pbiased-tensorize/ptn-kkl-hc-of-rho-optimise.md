# Conditional $p$-biased KKL statement yields KKL with constant $2$

Let $q \in \mathbb{R}$ be such that the [conditional KKL statement](ptn-rho-optimise.md) holds at
$q$, and let $p \in (1/2, q)$ with $p < 1$. Then the KKL inequality with constant $2$ holds at $p$:
for every nonempty finite set $E$ and every $A \subseteq \{0, 1\}^E$, with
$f = \mathbf{1}_A$,

$$2 \operatorname{Var}_p(f) \log \frac{1}{\max_e \mathrm{Inf}_e(f)} \le \sum_{e \in E} \mathrm{Inf}_e(f),$$

where $\mathrm{Inf}_e(f) = \mathbb{E}_p|f(\omega^{e \to 1}) - f(\omega^{e \to 0})|$ and
$\log(1/0)$ is read as $0$.
