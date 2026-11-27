# Sequential doubly robust estimator

The sequential doubly robust estimator evaluates a target policy from one behavior-policy trajectory by a backward recursion that, at each step, adds to a model value $\widehat V(s_t)$ the importance-weighted correction $\rho_t\,(r_t+\gamma\cdot\text{next estimate}-\widehat Q(s_t,a_t))$; with $\widehat Q\equiv 0$ it is step-wise importance sampling.

**Setting.** Use the finite-horizon setting of the [importance-sampling estimators](importance-sampling-estimators-for-off-policy.md): states $S$, actions $A$, transitions $P$, mean reward $R$, discount $\gamma\in[0,1]$, initial distribution $\mu$, horizon $H$, behavior policy $\pi_0$, target policy $\pi_1$, and a trajectory $(s_1,a_1,r_1,\ldots,s_H,a_H,r_H,s_{H+1})$ drawn from $(\mu,\pi_0)$, with per-step ratios $\rho_t=\pi_1(a_t\mid s_t)/\pi_0(a_t\mid s_t)$.

For $h=1,\ldots,H$ let $Q^{h}$ be the action value of $\pi_1$ with $h$ remaining steps: $V^{0}\equiv 0$, $Q^{h}(s,a)=R(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[V^{h-1}(s')]$ and $V^{h}(s)=\sum_{a}\pi_1(a\mid s)\,Q^{h}(s,a)$. An approximate model supplies functions $\widehat Q^{h}:S\times A\to\mathbb R$, for example by regression on a separate dataset, and $\widehat V^{h}(s)=\sum_a\pi_1(a\mid s)\,\widehat Q^{h}(s,a)$. At step $t$ the number of remaining steps is $H+1-t$, and $\widehat Q(s_t,a_t)$, $\widehat V(s_t)$ abbreviate $\widehat Q^{H+1-t}(s_t,a_t)$, $\widehat V^{H+1-t}(s_t)$.

**Estimator.** Set $V^{0}_{\mathrm{DR}}=0$ and, for $t=H,H-1,\ldots,1$,

$$
V^{H+1-t}_{\mathrm{DR}}=\widehat V(s_t)+\rho_t\Big(r_t+\gamma V^{H-t}_{\mathrm{DR}}-\widehat Q(s_t,a_t)\Big).
$$

The doubly robust estimate of $v^{\pi_1,H}$ from the trajectory is $V_{\mathrm{DR}}=V^{H}_{\mathrm{DR}}$; from a dataset of trajectories it is the average of the single-trajectory estimates.

With $H=1$ this is the doubly robust estimator for contextual bandits, $\widehat V(s)+\rho\,(r-\widehat R(s,a))$, and with $\widehat Q^{h}\equiv 0$ for all $h$ it is the recursive form of the step-wise importance-sampling estimate. The model functions and the target policy must not depend on the trajectories the estimator averages; with a given target policy one may split the data, fitting $\widehat Q$ on one part and averaging on the other.

## Depends on

- [Importance-sampling estimators for off-policy evaluation](importance-sampling-estimators-for-off-policy.md)

## Proof depends on

None. This page is a definition.

## Expansion

The step-wise importance-sampling recursion treats each step as a contextual bandit with context $s_t$, action $a_t$ and observed return $r_t+\gamma V^{H-t}_{\mathrm{step\text{-}IS}}$, whose conditional mean given $(s_t,a_t)$ is $Q^{H+1-t}(s_t,a_t)$. Applying the bandit doubly robust correction at every step, with the model value $\widehat Q$ as control variate, gives the recursion above.

## Sources

- N. Jiang and L. Li, *Doubly Robust Off-policy Value Evaluation for Reinforcement Learning*, Proceedings of the 33rd International Conference on Machine Learning, PMLR 48:652–661 (2016). [arXiv:1511.03722v3](https://arxiv.org/abs/1511.03722v3), §3.2.1, Eqs. (2)–(3) (the $h$-step values); §3.3, Eq. (8) and the paragraph on the requirement of independence; §4.1, Eqs. (9)–(10).
