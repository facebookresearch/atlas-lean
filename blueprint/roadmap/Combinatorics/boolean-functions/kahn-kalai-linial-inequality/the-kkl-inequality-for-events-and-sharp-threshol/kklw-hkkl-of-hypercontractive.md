# KKL inequality with constant 2 at $p$ implies its event form

Let $p$ be a real number such that the [KKL inequality with constant $2$](../the-kkl-inequality-statement-and-elementary-boun/kklhypercontractive.md) holds at $p$. Then for every finite nonempty set $E$ and every set $A \subseteq \{0, 1\}^E$,

$$2\, P_p(A)\big(1 - P_p(A)\big) \log \frac{1}{\max_{e \in E} \mathrm{Inf}_e(A)} \le \sum_{e \in E} \mathrm{Inf}_e(A),$$

where $P_p(A) = \sum_{\omega \in A} \prod_{e} w_p(\omega_e)$ with $w_p(1) = p$ and $w_p(0) = 1 - p$, $\mathrm{Inf}_e(A)$ is the same weighted sum over the configurations at which $e$ is pivotal for $A$, and $\log(1/0)$ is read as $0$ and $\log x = \log \lvert x\rvert$ for $x < 0$. For $0 \le p \le 1$ these are probabilities under the $p$-biased product measure.
