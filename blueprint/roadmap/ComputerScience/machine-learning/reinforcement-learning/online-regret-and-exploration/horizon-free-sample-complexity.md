# Horizon-free sample complexity for stationary episodic MDPs

In an episodic MDP with time-invariant transitions and rewards, nonnegative rewards and total reward at most $1$ per episode, an $\varepsilon$-optimal non-stationary policy can be found with probability at least $1-\delta$ from $(SA)^{O(S)}\log(1/\delta)/\varepsilon^5$ episodes, a number that does not depend on the horizon $H$.

Let $M = (\mathcal{S}, \mathcal{A}, P, R, H, \mu)$ be a stationary [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md): finite state and action sets with $S = |\mathcal{S}|$ and $A = |\mathcal{A}|$, one transition kernel $P$ and one reward distribution $R(s, a)$ on $\mathbb{R}$ for all stages, horizon $H$ and initial distribution $\mu$, where $P$, $R$ and $\mu$ are unknown. Assume that for every policy the rewards $r_0, \dots, r_{H-1}$ of an episode satisfy $r_h \in [0, 1]$ and $\sum_{h=0}^{H-1} r_h \le 1$ almost surely. The learner plays episodes from $s_0 \sim \mu$ as in the [online episodic protocol](online-episodic-learning-and-regret.md), each episode counting in full even if abandoned early. For a policy $\pi$ let $V^\pi_{M,H} = \mathbb{E}[\sum_{h=0}^{H-1} r_h]$. Then for every $\varepsilon > 0$ and $0 < \delta < 1$ there is an algorithm that, with probability at least $1 - \delta$, returns a non-stationary policy $\pi$ with $V^\pi_{M,H} \ge V^{\pi^\star}_{M,H} - \varepsilon$ after at most

$$
(SA)^{O(S)} \cdot \frac{\log(1/\delta)}{\varepsilon^5}
$$

episodes, where $\pi^\star$ is an optimal non-stationary policy.

## Depends on

- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)
- [Online episodic learning and regret](online-episodic-learning-and-regret.md)

## Proof depends on

- [Multiplicative Chernoff bounds for independent [0,1]-valued scores](../../../../Probability/concentration-inequalities/chernoff-and-bernoulli-comparison-bounds/multiplicative-chernoff-bounds.md)
- [Bennett's inequality and its Bernstein relaxation](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/bennett-inequality.md)
- [Chebyshev's inequality](../../../../Probability/moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)

## Expansion

Two assumptions carry the result, and neither can be dropped silently. Stationarity is essential: with stage-dependent transitions the [minimax lower bound](episodic-minimax-regret-lower-bound.md) grows polynomially in $H$. The normalization is total reward at most $1$, so $\varepsilon$ is a fraction of the largest possible return; in the per-step normalization with returns up to $H$ the same accuracy is $H\varepsilon$. The bound also says nothing good about $S$, $A$ or $\varepsilon$: its dependence on them is far worse than that of algorithms whose bounds grow with $H$. In the generative-model setting, where a batch of $H$ queries counts as one unit, the same paper finds an $\varepsilon$-optimal policy with $O(S^6A^4\log(1/\delta)/\varepsilon^3)$ batches.

The comparison class matters. With $H$ finite, the best stationary policy can be much worse than the best non-stationary one: with two states, staying in the first state gives reward $1/(2H)$ per step and leaving gives reward $1/2$ once (after which no reward is collected), so every episode's total reward is at most $1$ as the theorem assumes, the optimal non-stationary value is $1 - 1/(2H)$, and deterministic stationary policies get at most $1/2$. The source states this example with the rewards doubled, outside its own normalization. The proof nevertheless works with stationary policies, of which there are $A^S$. It shows that for $H$ large compared with $S\log S$ there is a stationary policy whose visitation of any state-action pair is within a factor $\exp(O(S\log S))$ of what any non-stationary policy achieves, using a link between finite-horizon and discounted values. It then collects data by running each stationary policy, estimates transitions and rewards to a relative accuracy governed by quantiles of visitation counts, and shows that every non-stationary policy's value in every model consistent with the estimates is within $\varepsilon/2$ of its true value, so the policy that is best in the estimated models is $\varepsilon$-optimal. The same data give an oracle that estimates the value of every non-stationary policy to accuracy $\varepsilon$. The concentration steps of the full version are multiplicative Chernoff bounds for indicators of quantile events, Bernstein's inequality for i.i.d. sums that include the random rewards, which follows from Bennett's inequality, and a per-trajectory bound on transition counts proved by orthogonality of martingale increments and Chebyshev's inequality.

## Sources

- Y. Li, R. Wang and L. F. Yang, "Settling the Horizon-Dependence of Sample Complexity in Reinforcement Learning", *2021 IEEE 62nd Annual Symposium on Foundations of Computer Science* (FOCS 2021): Theorems I.1 to I.3, Section II (the interaction model, the stationary-policy example and Assumption II.1), and Section IV (Corollaries IV.7 to IV.9), doi:10.1109/FOCS52979.2021.00097. The full version arXiv:2111.00633v1 states Theorem I.1 informally and proves it as a corollary with explicit constants. [DOI](https://doi.org/10.1109/FOCS52979.2021.00097)
