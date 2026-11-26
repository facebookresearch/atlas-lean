# Sharp threshold from a KKL-type influence inequality

Let $E$ be a finite set and let $A \subseteq \{0, 1\}^E$ be an [increasing](../../../correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md) event. For real $p$ let $\mathbb{P}_p(A)$ be the [weight](../../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/prob.md) $\sum_{\omega \in A} \prod_{e} p^{\omega_e}(1 - p)^{1 - \omega_e}$ and $I_e^p(A)$ the [influence](influence.md) of $e$ on $A$. Let $q \ge 1/2$, $C > 0$, $v_0 \ge 0$ and $L \ge 0$ be real numbers and $L' : \mathbb{R} \to \mathbb{R}$ a function. Assume $\mathbb{P}_{1/2}(A) = 1/2$ and, for every $p \in (1/2, q)$,

- (KKL-type inequality) $\displaystyle C\, \mathbb{P}_p(A)\big(1 - \mathbb{P}_p(A)\big)\, L'(p) \le \sum_{e \in E} I_e^p(A)$,
- $\mathbb{P}_p(A)\big(1 - \mathbb{P}_p(A)\big) \ge v_0$, and
- $L'(p) \ge L$.

Then

$$\mathbb{P}_q(A) \ge \frac{1}{2} + C v_0 L \Big(q - \frac{1}{2}\Big).$$

The KKL-type inequality is an assumption, not a consequence.
