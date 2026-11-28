# Self-normalized bound for vector-valued martingales

For conditionally $R$-sub-Gaussian noise $\eta_t$ and predictable vectors $X_t$, the squared norm of the noise sum $S_t = \sum_{s \le t} \eta_s X_s$ in the inverse regularized Gram matrix stays below $2R^2 \log(\det(\bar V_t)^{1/2} \det(V)^{-1/2} / \delta)$ for all $t$ at once, with probability $1-\delta$.

**Statement.** Let $(\mathcal{F}_t)_{t \ge 0}$ be a filtration. Let $(\eta_t)_{t \ge 1}$ be real-valued with $\eta_t$ $\mathcal{F}_t$-measurable and conditionally $R$-sub-Gaussian for some $R \ge 0$:

$$
\mathbb{E}\big[e^{\lambda \eta_t} \mid \mathcal{F}_{t-1}\big] \le \exp\Big(\frac{\lambda^2 R^2}{2}\Big) \quad \text{for all } \lambda \in \mathbb{R}.
$$

Let $(X_t)_{t \ge 1}$ be $\mathbb{R}^d$-valued with $X_t$ $\mathcal{F}_{t-1}$-measurable, and let $V$ be a $d \times d$ positive definite matrix. For $t \ge 0$ put

$$
\bar V_t = V + \sum_{s=1}^{t} X_s X_s^{\mathsf T}, \qquad S_t = \sum_{s=1}^{t} \eta_s X_s .
$$

Then for every $\delta > 0$, with probability at least $1 - \delta$, simultaneously for all $t \ge 0$,

$$
\lVert S_t \rVert^2_{\bar V_t^{-1}} \le 2R^2 \log\Big( \frac{\det(\bar V_t)^{1/2} \det(V)^{-1/2}}{\delta} \Big),
$$

where $\lVert u \rVert_A^2 = u^{\mathsf T} A u$. At $t = 0$ both sides are consistent ($S_0 = 0$ and the right side is $2R^2 \log(1/\delta)$, nonnegative for $\delta \le 1$; for $\delta > 1$ the claim is vacuous).

The conditional sub-Gaussian condition implies $\mathbb{E}[\eta_t \mid \mathcal{F}_{t-1}] = 0$. The bound is uniform in time; no independence between $X_t$ and past noise is needed beyond predictability. No integrability of $X_t$ is assumed, so $S_t$ need not be an integrable martingale (for example when $X_1$ has infinite mean); the title follows the source, which calls $S_t$ a martingale.

## Depends on

- [Filtrations and stopping times](../../../../../Probability/martingales/stopping-times-and-martingale-problems/filtrations-and-stopping-times.md)
- [Conditional expectation given a σ-field](../../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)

## Proof depends on

- [Ville's maximal inequality](../../../../../Probability/hypothesis-testing/sequential-tests-and-quickest-change-detection/anytime-valid-confidence-sequences/ville/ville-maximal-ineq.md)

## Expansion

After dividing $\eta_t$ by $R$ (the case $R = 0$ is trivial), take $R = 1$. For fixed $x \in \mathbb{R}^d$, $M^x_t = \exp\big(\langle x, S_t \rangle - \tfrac12 \lVert x \rVert^2_{\bar V_t - V}\big)$ is a nonnegative supermartingale with $M^x_0 = 1$ by the sub-Gaussian condition. Integrating $x$ against the Gaussian law $N(0, V^{-1})$ (the method of mixtures) gives a supermartingale $M_t$ that evaluates in closed form to $(\det V / \det \bar V_t)^{1/2} \exp(\tfrac12 \lVert S_t \rVert^2_{\bar V_t^{-1}})$. Since $M_0 = 1$, Ville's maximal inequality gives $\Pr[\exists t : M_t \ge 1/\delta] \le \delta$, which rearranges to the claim. The source reaches the same conclusion through a stopping time and Markov's inequality. With $V = \lambda I$ and $\lVert X_t \rVert_2 \le L$ this gives the confidence ellipsoid of ridge regression used by optimistic linear bandit and linear MDP algorithms.

A complete expansion adds a page for the Gaussian mixture integral, $\int \exp(\langle x, S\rangle - \tfrac12\lVert x\rVert^2_{A})\, dN(0,V^{-1})(x) = (\det V/\det(A+V))^{1/2}\exp(\tfrac12\lVert S\rVert^2_{(A+V)^{-1}})$ for $A \succeq 0$, $V \succ 0$, and for the fact that a mixture of nonnegative supermartingales is a supermartingale.

## Sources

- Y. Abbasi-Yadkori, D. Pál and Cs. Szepesvári, "Improved Algorithms for Linear Stochastic Bandits", Advances in Neural Information Processing Systems 24 (NIPS 2011), Theorem 1 (self-normalized bound for vector-valued martingales) and Theorem 2 (confidence ellipsoid). <https://proceedings.neurips.cc/paper_files/paper/2011/file/e1d5be1c7f2f456670de3d53c7b54f4a-Paper.pdf>
- C. Jin, Z. Yang, Z. Wang and M. I. Jordan, "Provably Efficient Reinforcement Learning with Linear Function Approximation", Conference on Learning Theory (COLT 2020), PMLR 125. Numbers from arXiv:1907.05388v2: Theorem D.3 restates the bound with $\Lambda_0$ in place of $V$. <https://arxiv.org/abs/1907.05388v2>
