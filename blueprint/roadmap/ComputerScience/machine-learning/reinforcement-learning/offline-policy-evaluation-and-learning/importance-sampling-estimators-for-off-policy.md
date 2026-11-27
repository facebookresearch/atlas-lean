# Importance-sampling estimators for off-policy evaluation

From length-$H$ trajectories collected with a behavior policy $\pi_0$, the trajectory-wise and step-wise importance-sampling estimators reweight the observed rewards by products of action-probability ratios $\pi_1/\pi_0$ to estimate the $H$-step discounted value of a target policy $\pi_1$; the weighted variants divide by the average ratio instead.

**Setting.** An MDP has states $S$, actions $A$, transition probabilities $P(s'\mid s,a)$, mean reward $R(s,a)$, discount $\gamma\in[0,1]$ and initial state distribution $\mu$. A stationary stochastic policy $\pi$ gives a distribution $\pi(\cdot\mid s)$ on $A$ for each $s$. For a horizon $H\ge 1$, a trajectory $\tau=(s_1,a_1,r_1,\ldots,s_H,a_H,r_H,s_{H+1})\sim(\mu,\pi)$ has $s_1\sim\mu$ and, for $t=1,\ldots,H$, $a_t\sim\pi(\cdot\mid s_t)$, $s_{t+1}\sim P(\cdot\mid s_t,a_t)$, and $r_t$ with conditional mean $R(s_t,a_t)$ given $(s_t,a_t)$. The $H$-step value of $\pi$ is

$$
v^{\pi,H}=\mathbb E_{\tau\sim(\mu,\pi)}\Big[\sum_{t=1}^{H}\gamma^{t-1}r_t\Big].
$$

The data $D$ are $|D|$ trajectories drawn independently from $(\mu,\pi_0)$ for a fixed behavior policy $\pi_0$, and the goal is $v^{\pi_1,H}$ for a given target policy $\pi_1$. Precup, Sutton and Singh take the behavior policy to be soft, $\pi_0(a\mid s)>0$ for every $s$ and $a$, so that every ratio below is defined.

**Ratios.** On a trajectory, the per-step importance ratio is $\rho_t=\pi_1(a_t\mid s_t)/\pi_0(a_t\mid s_t)$ and the cumulative ratio is $\rho_{1:t}=\prod_{t'=1}^{t}\rho_{t'}$.

**Estimators.** For one trajectory, the trajectory-wise and step-wise importance-sampling estimates are

$$
V_{\mathrm{IS}}=\rho_{1:H}\sum_{t=1}^{H}\gamma^{t-1}r_t,
\qquad
V_{\mathrm{step\text{-}IS}}=\sum_{t=1}^{H}\gamma^{t-1}\rho_{1:t}\,r_t .
$$

The estimate from $D$ is the average of the single-trajectory estimates over its $|D|$ trajectories. Write $\rho^{(i)}_{1:t}$ for the cumulative ratio on the $i$-th trajectory and $w_t=\frac{1}{|D|}\sum_{i=1}^{|D|}\rho^{(i)}_{1:t}$ for its average at step $t$. The trajectory-wise and step-wise weighted importance-sampling estimates of a trajectory of $D$ are

$$
V_{\mathrm{WIS}}=\frac{\rho_{1:H}}{w_H}\sum_{t=1}^{H}\gamma^{t-1}r_t,
\qquad
V_{\mathrm{step\text{-}WIS}}=\sum_{t=1}^{H}\gamma^{t-1}\frac{\rho_{1:t}}{w_t}\,r_t ,
$$

again averaged over the trajectories of $D$. They are defined when the averages $w_t$ that occur are positive.

**Recursive form.** Setting $V^{0}_{\mathrm{step\text{-}IS}}=0$ and, for $t=1,\ldots,H$,

$$
V^{H+1-t}_{\mathrm{step\text{-}IS}}=\rho_t\big(r_t+\gamma V^{H-t}_{\mathrm{step\text{-}IS}}\big),
$$

gives $V^{H}_{\mathrm{step\text{-}IS}}=V_{\mathrm{step\text{-}IS}}$; unrolling the recursion multiplies the reward at step $t$ by $\gamma^{t-1}\rho_{1:t}$.

Jiang and Li describe the two importance-sampling estimates as unbiased for $v^{\pi_1,H}$ and the weighted ones as biased but consistent; the step-wise estimate is the case $\widehat Q\equiv 0$ of the [sequential doubly robust estimator](sequential-doubly-robust-estimator.md). Its [unbiasedness theorem](doubly-robust-estimator-is-unbiased.md) states the required Markov reward model. For unbiasedness the target policy must not depend on the trajectories that are averaged.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Proof depends on

None. This page is a definition.

## Expansion

The recursion follows by induction on the number of remaining steps: if $V^{H-t}_{\mathrm{step\text{-}IS}}=\sum_{u=t+1}^{H}\gamma^{u-t-1}\big(\prod_{t'=t+1}^{u}\rho_{t'}\big)r_u$, then $\rho_t(r_t+\gamma V^{H-t}_{\mathrm{step\text{-}IS}})$ is the same sum started at $u=t$. The step-wise estimate weights the reward at step $t$ only by the ratios of the actions taken up to $t$, whereas the trajectory-wise one uses the full product $\rho_{1:H}$ for every reward.

## Sources

- N. Jiang and L. Li, *Doubly Robust Off-policy Value Evaluation for Reinforcement Learning*, Proceedings of the 33rd International Conference on Machine Learning, PMLR 48:652–661 (2016). [arXiv:1511.03722v3](https://arxiv.org/abs/1511.03722v3), §3.1, Eq. (1) (setting and $v^{\pi,H}$), §3.2.2, Eqs. (4)–(7), and §4.1, Eq. (9); §3.3 on the independence requirement.
- D. Precup, R. S. Sutton and S. Singh, *Eligibility Traces for Off-Policy Policy Evaluation*, Proceedings of the 17th International Conference on Machine Learning (ICML 2000). [Author copy](https://hdl.handle.net/20.500.14394/10401), §2 (soft behavior policy), §3, Eqs. (2)–(3), and §4 (per-decision importance sampling).
