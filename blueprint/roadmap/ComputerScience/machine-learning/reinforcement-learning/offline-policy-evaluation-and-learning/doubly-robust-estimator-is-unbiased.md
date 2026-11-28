# Unbiasedness and variance of the sequential doubly robust estimator

With a model and target policy fixed independently of the evaluation data, behavior-policy coverage and the stated finite-variance Markov reward model, the sequential doubly robust estimator is unbiased for the target's $H$-step value. Its conditional variance has an action term using $\widehat Q-Q$, plus terms for transitions, rewards and later-step variance.

Use the setting and notation of the [sequential doubly robust estimator](sequential-doubly-robust-estimator.md): a trajectory from $(\mu,\pi_0)$, target policy $\pi_1$, ratios $\rho_t$, values $Q=Q^{H+1-t}$ and $V=V^{H+1-t}$ of $\pi_1$ with the remaining number of steps left implicit, model functions $\widehat Q$ and $\widehat V(s)=\sum_a\pi_1(a\mid s)\widehat Q(s,a)$, and the estimates $V^{H+1-t}_{\mathrm{DR}}$. Assume:

- the model functions $\widehat Q^{h}$ and the target policy $\pi_1$ are fixed: they do not depend on the trajectory, nor, for an average over a dataset, on any of the trajectories being averaged (the source's independence requirement, met for example by fitting $\widehat Q$ on a separate split of the data);
- every ratio is defined and $\mathbb E_{a\sim\pi_0(\cdot\mid s)}[\rho\, g(s,a)]=\mathbb E_{a\sim\pi_1(\cdot\mid s)}[g(s,a)]$ for the functions $g$ involved, which holds when $\pi_0(a\mid s)>0$ whenever $\pi_1(a\mid s)>0$;
- the trajectory follows the Markov reward model the source's proof uses: given the history $s_1,a_1,\ldots,s_t,a_t$, the next state has law $P(\cdot\mid s_t,a_t)$, and the reward $r_t$ has conditional mean $R(s_t,a_t)$ and is conditionally independent of $(s_{t+1},a_{t+1},r_{t+1},\ldots)$;
- the expectations and variances below are finite, for example because the state and action sets are finite.

All expectations are under the law of the trajectory from $(\mu,\pi_0)$. Write $\mathbb E_t[\cdot]=\mathbb E[\cdot\mid s_1,a_1,\ldots,s_{t-1},a_{t-1}]$ and $\mathbb V_t$ for the corresponding conditional variance, so that $\mathbb E_1$ and $\mathbb V_1$ are unconditional and $\mathbb E_{t+1}$, $\mathbb V_{t+1}$ condition on the history through $a_t$.

**Theorem (Jiang and Li, Theorem 1).** $V_{\mathrm{DR}}=V^{H}_{\mathrm{DR}}$ is an unbiased estimator of $v^{\pi_1,H}$, and for every $t=1,\ldots,H$

$$
\mathbb V_t\big[V^{H+1-t}_{\mathrm{DR}}\big]
=\mathbb V_t\big[V(s_t)\big]
+\mathbb E_t\Big[\mathbb V_t\big[\rho_t\,\Delta(s_t,a_t)\,\big|\,s_t\big]\Big]
+\mathbb E_t\Big[\rho_t^{2}\,\mathbb V_{t+1}[r_t]\Big]
+\mathbb E_t\Big[\gamma^{2}\rho_t^{2}\,\mathbb V_{t+1}\big[V^{H-t}_{\mathrm{DR}}\big]\Big],
$$

where $\Delta(s_t,a_t)=\widehat Q(s_t,a_t)-Q(s_t,a_t)$ and $\mathbb V_{H+1}\big[V^{0}_{\mathrm{DR}}\big]=0$.

The estimate averaged over $|D|$ independent trajectories, with $\widehat Q$ and $\pi_1$ independent of all of them, is again unbiased, with variance that of one trajectory divided by $|D|$. Taking $\widehat Q\equiv 0$ gives the step-wise importance-sampling estimate, for which $\Delta=-Q$. Even with $\widehat Q=Q$ the first, third and fourth terms remain: the estimator reduces only the variance due to the randomness of the behavior policy's actions.

## Depends on

- [Sequential doubly robust estimator](sequential-doubly-robust-estimator.md)

## Proof depends on

- [Importance sampling is unbiased](../../bayesian-inference-and-sampling/monte-carlo-and-importance-sampling/integral-is-estimate.md)

## Expansion

Induct backwards from $t=H+1$, where $V^{0}_{\mathrm{DR}}=0$ is exact. Given the history, the change of measure from $\pi_0$ to $\pi_1$ at step $t$ gives $\mathbb E_t[\rho_t\widehat Q(s_t,a_t)\mid s_t]=\widehat V(s_t)$ and $\mathbb E_t[\rho_t Q(s_t,a_t)\mid s_t]=V(s_t)$, and the induction hypothesis gives $\mathbb E_{t+1}[V^{H-t}_{\mathrm{DR}}]=\mathbb E_{t+1}[V(s_{t+1})]$; hence $\mathbb E_t[V^{H+1-t}_{\mathrm{DR}}\mid s_t]=V(s_t)$, and at $t=1$ the mean is $\mathbb E_{s_1\sim\mu}V^{H}(s_1)=v^{\pi_1,H}$. For the variance, write

$$
V^{H+1-t}_{\mathrm{DR}}=\big(\widehat V(s_t)-\rho_t\Delta(s_t,a_t)\big)+\rho_t\big(r_t-R(s_t,a_t)\big)+\rho_t\gamma\big(V^{H-t}_{\mathrm{DR}}-\mathbb E_{t+1}[V(s_{t+1})]\big).
$$

Given the history through $a_t$ the last two terms have mean zero and, by the reward model, are conditionally independent, so the second moment splits into the four terms; the first summand contributes $\mathbb V_t[V(s_t)]$ plus the conditional variance of $\rho_t\Delta$ given $s_t$.

## Sources

- N. Jiang and L. Li, *Doubly Robust Off-policy Value Evaluation for Reinforcement Learning*, Proceedings of the 33rd International Conference on Machine Learning, PMLR 48:652–661 (2016). [arXiv:1511.03722v3](https://arxiv.org/abs/1511.03722v3), §4.2, Theorem 1 and Eq. (11); proof in Appendix A.
