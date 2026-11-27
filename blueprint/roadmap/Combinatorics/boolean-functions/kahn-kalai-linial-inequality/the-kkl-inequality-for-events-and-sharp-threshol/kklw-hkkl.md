# KKL on $(1/2, q)$ implies its event form there

Let $E$ be a finite nonempty set, $A \subseteq \{0, 1\}^E$ and $q$ a real number, and let $J$ be the interior of the interval $[1/2, q]$ (so $J = (1/2, q)$ if $q > 1/2$, and $J = \emptyset$ otherwise). If the [KKL inequality with constant $2$](../the-kkl-inequality-statement-and-elementary-boun/kklhypercontractive.md) holds at every $p \in J$, then for every $p \in J$

$$2\, P_p(A)\big(1 - P_p(A)\big) \log \frac{1}{\max_{e \in E} \mathrm{Inf}_e(A)} \le \sum_{e \in E} \mathrm{Inf}_e(A),$$

where $P_p(A) = \sum_{\omega \in A} \prod_e w_p(\omega_e)$ with $w_p(1) = p$ and $w_p(0) = 1 - p$ (the $p$-biased product measure when $p \le 1$), $\mathrm{Inf}_e(A)$ is the same weighted sum over the configurations at which $e$ is pivotal for $A$, and $\log(1/0)$ is read as $0$ and $\log x = \log \lvert x\rvert$ for $x < 0$ (for $p > 1$ the weights can be negative).
