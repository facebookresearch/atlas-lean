# Planning lower bound under linear realizability of the optimal state values

In infinite-horizon total-cost planning with local simulator access, exact linear realizability of $v^\star$ with $d+1$ features of $2$-norm $O(1)$ and parameter norm $O(\sqrt d)$ does not prevent an exponential query cost: with $\Theta(d)$ actions, constant suboptimality needs $\Omega(2^{\min\{d, A/2\}}/d)$ queries per call.

**Setting.** An MDP with states $\mathcal{S}$, finite actions and a simulator; in the infinite-horizon setting a policy's value is its total expected reward (here rewards are nonpositive costs), and $v^\star$ is the best value over admissible policies. A featurized MDP adds a feature map $\varphi : \mathcal{S} \to \mathbb{R}^d$ (no stage dependence), and $v^\star$ is *linearly realizable* if $v^\star(s) = \langle \varphi(s), \theta^\star \rangle$ for all $s$. Access is *local*: a planner called at a state may query the simulator only at states it was given or has received from the simulator, and sees features only of those states; each query returns a fresh next state, reward and next feature. The *worst-case per-state query cost* is the largest number of simulator calls made in one call of the planner. The planner, called at every visited state, induces a policy whose suboptimality $\delta$ is its gap to $v^\star$.

**Theorem.** Fix $d \ge 1$ and a local planner whose worst-case per-state query cost is at most $\beta_{\mathrm{sim}}$. There is a deterministic featurized MDP on the grid $\{-1,0,1\}^d$ with at most $2d+1$ actions and features of dimension $d+1$ such that $v^\star$ is exactly linearly realizable and takes values in $[-2, 0]$, the feature vectors have $2$-norm $O(1)$, the parameter of $v^\star$ has $2$-norm $O(\sqrt d)$, and the policy the planner induces has suboptimality

$$
\delta \ge \frac12 \Big( \Big\lfloor \frac{2^{d-1}}{d\,(\beta_{\mathrm{sim}} + 1)} \Big\rfloor - 1 \Big).
$$

In particular, $\delta \le 1/2$ forces $\beta_{\mathrm{sim}} = \Omega\big(2^{\min\{d, A/2\}}/d\big)$, where $A$ is the number of actions.

The source's Theorem 3.1 states the result for $d$-dimensional features with $2d - 1$ actions and the display $\delta \ge 2^{d-2}/(d(\beta_{\mathrm{sim}}+1)) - 1$. Its proof (Appendix B) treats features of dimension $d+1$ on the $d$-dimensional grid, and the explicit inequality above is the one that proof establishes. In terms of the feature dimension it is weaker than the displayed one by about a factor of two; the asymptotic consequence is unchanged.

**Scope.** The bound is for the undiscounted infinite-horizon total-cost setting with deterministic dynamics and costs, diameter $\Theta(d)$ and $\Theta(d)$ actions. In the fixed-horizon setting with a constant number $A$ of actions, the same source gives a planner (TensorPlan) that is sound for $B$-bounded realizable $v^\star$ with $\mathrm{poly}((dH/\delta)^A, B)$ queries per episode. Whether its computation is similarly bounded is left open, so that positive result is statistical only. Realizing $v^\star$ is weaker than realizing $q^\star$: even with $v^\star$ known, picking a good action among $A$ needs $\Omega(A)$ queries.

## Depends on

- [Probability measure](../../../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

None.

## Expansion

The MDPs share deterministic dynamics on $\{-1,0,1\}^d$: each action increments or decrements one coordinate or stays put. In the MDP $M_{s^\star}$ with goal $s^\star \in \{-1,1\}^d$, every action costs $1/d$ except staying put at $s^\star$, which costs $0$. Then $v^\star(s) = -\tfrac1d \lVert s - s^\star\rVert_1$, and since $|x - x^\star| = 1 - x x^\star$ for $x \in \{-1,0,1\}$ and $x^\star \in \{-1,1\}$, this equals $\langle \varphi(s), \theta^\star\rangle$ with $\varphi(s) = (1, s/d)$ and $\theta^\star = (-1, s^\star)$.

A test MDP $M_\emptyset$ with all costs $1/d$ is used to choose $s^\star$ adversarially. Some $s^\star$ is among the first $2^{d-1}$ distinct states the planner encounters in $M_\emptyset$ with probability at most $1/2$, and the event that it is not has the same probability in $M_{s^\star}$, since the two MDPs differ only at $s^\star$. Each call encounters at most $\beta_{\mathrm{sim}} + 1$ new states, so on that event the planner takes at least $\lfloor 2^{d-1}/(\beta_{\mathrm{sim}}+1)\rfloor$ actions of cost $1/d$ before reaching $s^\star$. This gives the bound.

## Sources

- G. Weisz, P. Amortila, B. Janzer, Y. Abbasi-Yadkori, N. Jiang and Cs. Szepesvári, "On Query-efficient Planning in MDPs under Linear Realizability of the Optimal State-value Function", Conference on Learning Theory (COLT 2021), PMLR 134:4355–4385. Numbers from arXiv:2102.02049v3: Section 2 (infinite-horizon setting, Eq. (2), Section 2.2 local access and per-state query cost), Theorem 3.1 with its proof sketch, Appendix B (proof of Theorem 3.1, the source of the explicit bound and construction stated here), Theorem 4.2 and Corollary 4.3 (TensorPlan). <https://arxiv.org/abs/2102.02049v3>
