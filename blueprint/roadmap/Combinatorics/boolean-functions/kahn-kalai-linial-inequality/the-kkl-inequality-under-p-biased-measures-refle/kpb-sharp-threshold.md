# Sharp-threshold bound under the $p$-biased KKL hypothesis

Let $E$ be a finite nonempty set and $A \subseteq \{0, 1\}^E$ an increasing event with $P_{1/2}(A) = 1/2$, where $P_p(B) = \sum_{\omega \in B} \prod_e w_p(\omega_e)$ with $w_p(1) = p$ and $w_p(0) = 1 - p$ (the $p$-biased product measure when $0 \le p \le 1$). Let $q \ge 1/2$, $v_0 \ge 0$ and $L \ge 0$. Suppose that the [KKL inequality with constant $2$](../the-kkl-inequality-statement-and-elementary-boun/kklhypercontractive.md) holds at every $p \in (1/2, q)$, and that for every such $p$, $P_p(A)(1 - P_p(A)) \ge v_0$ and $\log(1/\max_e \mathrm{Inf}_e(A)) \ge L$ (with $\log(1/0) = 0$ and $\log x = \log \lvert x\rvert$ for $x < 0$), where $\mathrm{Inf}_e(A)$ is the weight under $P_p$ of the configurations at which $e$ is pivotal for $A$. Then

$$P_q(A) \ge \frac12 + 2 v_0 L \Big(q - \frac12\Big).$$
