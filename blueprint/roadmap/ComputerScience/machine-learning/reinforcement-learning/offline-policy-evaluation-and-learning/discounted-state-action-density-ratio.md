# Discounted state-action density ratio

For off-policy evaluation in a discounted MDP, the density ratio $w_{\pi_e/\pi_b}(s,a)=d_{\pi_e,\gamma}(s,a)/d_{\pi_b}(s,a)$ compares the target policy's normalized discounted occupancy with the data distribution; reweighting observed rewards by it recovers the target policy's normalized return.

**Setting.** A discounted MDP has finite state and action sets $S$ and $A$, $\mathcal X=S\times A$, transition kernel $P(\cdot\mid s,a)$, reward distributions $\mathcal R(s,a)$ on $[0,R_{\max}]$, discount $\gamma\in[0,1)$ and initial state distribution $d_0$. For a stochastic policy $\pi$ with trajectory $s_0\sim d_0$, $a_t\sim\pi(\cdot\mid s_t)$, $r_t\sim\mathcal R(s_t,a_t)$, $s_{t+1}\sim P(\cdot\mid s_t,a_t)$, the normalized expected discounted return is

$$
R_\pi=(1-\gamma)\,\mathbb E_{d_0,\pi}\Big[\sum_{t=0}^{\infty}\gamma^{t}r_t\Big],
$$

and the normalized discounted occupancy is $d_{\pi,\gamma}=(1-\gamma)\sum_{t\ge 0}\gamma^{t}d_{\pi,t}$, where $d_{\pi,t}$ is the law of $(s_t,a_t)$, and $R_\pi=\mathbb E_{(s,a)\sim d_{\pi,\gamma},\,r\sim\mathcal R(s,a)}[r]$.

**Data.** The data are $n\ge1$ independent tuples $(s,a,r,s')$ with $s\sim d_{\pi_b}$, $a\sim\pi_b(\cdot\mid s)$, $r\sim\mathcal R(s,a)$ and $s'\sim P(\cdot\mid s,a)$, for a behavior policy $\pi_b$ and some state distribution $d_{\pi_b}$, which need not be the occupancy of $\pi_b$. Write $d_{\pi_b}(s,a)=d_{\pi_b}(s)\pi_b(a\mid s)$ for the law of $(s,a)$ and $\mathbb E_{d_{\pi_b}}$ for expectations over one tuple.

**Definition.** For a target (evaluation) policy $\pi_e$, the state-action density ratio is

$$
w_{\pi_e/\pi_b}(s,a)=\frac{d_{\pi_e,\gamma}(s,a)}{d_{\pi_b}(s,a)}\quad\text{at pairs with }d_{\pi_b}(s,a)>0 .
$$

The source works with densities and does not discuss pairs with $d_{\pi_b}(s,a)=0$; set $w_{\pi_e/\pi_b}(s,a)=0$ there. Its values at those pairs do not affect any expectation under $d_{\pi_b}$. Uehara, Huang and Jiang assume a constant $C_w<\infty$ with $w_{\pi_e/\pi_b}(s,a)\le C_w$ for all $(s,a)$ (their Assumption 2), which on a finite $\mathcal X$ is read as the *coverage condition* $d_{\pi_e,\gamma}(s,a)\le C_w\,d_{\pi_b}(s,a)$ for all $(s,a)$; in particular $d_{\pi_b}(s,a)>0$ wherever $d_{\pi_e,\gamma}(s,a)>0$. Because of the zero extension, a bound on $w_{\pi_e/\pi_b}$ alone does not imply coverage, so the pages that use properties of the true ratio assume the coverage condition explicitly. Under this coverage condition

$$
R_{\pi_e}=\mathbb E_{d_{\pi_b}}\big[w_{\pi_e/\pi_b}(s,a)\,r\big],
$$

so the ratio converts an average over the data into the target policy's return without using $\pi_b$ or the trajectory structure. Unlike the cumulative ratio of [trajectory-wise importance sampling](importance-sampling-estimators-for-off-policy.md), it is bounded by the overlap of the two marginal distributions, not by a product over the horizon. The ratio $d_{\pi_e,\gamma}(s)/d_{\pi_b}(s)$ of state marginals, times $\pi_e(a\mid s)/\pi_b(a\mid s)$, is the marginalized importance weight of Liu, Li, Tang and Zhou; it needs $\pi_b$, which $w_{\pi_e/\pi_b}$ does not.

## Depends on

- [Discounted state-action occupancy of a row-stochastic policy](../stochastic-policies-and-discounted-occupancy/occupancy.md)
- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Proof depends on

None. This page is a definition.

## Expansion

The identity $R_\pi=\mathbb E_{d_{\pi,\gamma}}[r]$ is the exchange of the discounted sum with the expectation: $(1-\gamma)\sum_t\gamma^t\mathbb E[r_t]=(1-\gamma)\sum_t\gamma^t\sum_{(s,a)}d_{\pi,t}(s,a)\,\bar r(s,a)$, with $\bar r$ the mean reward. Reweighting this sum from $d_{\pi_e,\gamma}$ to $d_{\pi_b}$ is valid exactly when $d_{\pi_b}$ charges every pair that $d_{\pi_e,\gamma}$ charges.

## Sources

- M. Uehara, J. Huang and N. Jiang, *Minimax Weight and Q-Function Learning for Off-Policy Evaluation*, Proceedings of the 37th International Conference on Machine Learning, PMLR 119:9659–9668 (2020). [arXiv:1910.12809v4](https://arxiv.org/abs/1910.12809v4), §2, Eqs. (1)–(2) and the data-generation protocol; §3, Eq. (3); §4, Eq. (4), Assumptions 1–2 (Assumption 1's footnote covers finite $\mathcal X$ with counting measure) and the identity $R_{\pi_e}=R_{\mathrm w}[w_{\pi_e/\pi_b}]$.
- Q. Liu, L. Li, Z. Tang and D. Zhou, *Breaking the Curse of Horizon: Infinite-Horizon Off-Policy Estimation*, Advances in Neural Information Processing Systems 31 (NeurIPS 2018). [Proceedings copy](https://proceedings.neurips.cc/paper/2018/file/dda04f9d634145a9c68d5dfe53b21272-Paper.pdf), §3, in particular §3.2 (discounted case), for comparison only.
