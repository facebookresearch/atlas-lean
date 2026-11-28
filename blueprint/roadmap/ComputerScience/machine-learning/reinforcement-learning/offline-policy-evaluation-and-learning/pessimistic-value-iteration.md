# Pessimistic value iteration

Pessimistic value iteration is a backward dynamic-programming scheme for offline episodic reinforcement learning that subtracts from each estimated Bellman backup a penalty $\Gamma_h$ bounding its estimation error with high probability, truncates the result to the feasible value range, and acts greedily on the penalized action values.

**Setting.** An episodic MDP $(S,A,H,\mathcal P,r)$ has horizon $H$, step-dependent transition kernels $\mathcal P_h(\cdot\mid x,a)$ and reward functions $r_h\in[0,1]$, $h\in[H]=\{1,\ldots,H\}$. For a policy $\pi=(\pi_h)_{h\in[H]}$, $V^\pi_h(x)=\mathbb E_\pi[\sum_{i=h}^{H}r_i(s_i,a_i)\mid s_h=x]$, and $\pi^*$, $V^*_h$ are optimal, with $V^*_{H+1}=0$. For $f:S\to\mathbb R$ the Bellman operator is $(\mathbb B_hf)(x,a)=\mathbb E[r_h(s_h,a_h)+f(s_{h+1})\mid s_h=x,a_h=a]$. The suboptimality of $\pi$ from $x$ is $\mathrm{SubOpt}(\pi;x)=V^{\pi^*}_1(x)-V^{\pi}_1(x)$.

**Data.** The dataset $\mathcal D=\{(x^\tau_h,a^\tau_h,r^\tau_h)\}_{\tau\in[K],h\in[H]}$ has $K\ge1$ trajectories, collected with law $\mathbb P_{\mathcal D}$. It is *compliant* with the MDP (Jin, Yang and Wang, Definition 2.1 and Assumption 2.2) if, for every $h$ and $\tau$, conditional on $\{(x^j_h,a^j_h)\}_{j\le\tau}$ and $\{(r^j_h,x^j_{h+1})\}_{j<\tau}$, the pair $(r^\tau_h,x^\tau_{h+1})$ has the law of $(r_h(s_h,a_h),s_{h+1})$ in the MDP given $(s_h,a_h)=(x^\tau_h,a^\tau_h)$. The actions may be chosen arbitrarily, even adaptively, and no coverage is assumed; a fixed behavior policy is a special case.

**Uncertainty quantifier (Definition 4.1).** Let an algorithm build, from $\mathcal D$, estimates $\widehat V_{h+1}:S\to\mathbb R$ and estimated backups $(\widehat{\mathbb B}_h\widehat V_{h+1})(x,a)$. For $\xi\in(0,1)$, functions $\Gamma_h:S\times A\to\mathbb R$, $h\in[H]$, form a $\xi$-uncertainty quantifier with respect to $\mathbb P_{\mathcal D}$ if the event

$$
\mathcal E=\Big\{\big|(\widehat{\mathbb B}_h\widehat V_{h+1})(x,a)-(\mathbb B_h\widehat V_{h+1})(x,a)\big|\le\Gamma_h(x,a)\ \text{for all }(x,a)\in S\times A,\ h\in[H]\Big\}
$$

satisfies $\mathbb P_{\mathcal D}(\mathcal E)\ge1-\xi$.

**Algorithm (Algorithm 1).** Set $\widehat V_{H+1}\equiv0$. For $h=H,H-1,\ldots,1$: construct $\widehat{\mathbb B}_h\widehat V_{h+1}$ and $\Gamma_h$ from $\mathcal D$; set $\overline Q_h=\widehat{\mathbb B}_h\widehat V_{h+1}-\Gamma_h$ and $\widehat Q_h=\min\{\overline Q_h,H-h+1\}^{+}$, where $y^+=\max(y,0)$; let $\hat\pi_h(\cdot\mid x)$ be a distribution on $A$ that maximizes $\langle\widehat Q_h(x,\cdot),\pi_h(\cdot\mid x)\rangle_A$; and set $\widehat V_h(x)=\langle\widehat Q_h(x,\cdot),\hat\pi_h(\cdot\mid x)\rangle_A$. The output is $\mathrm{Pess}(\mathcal D)=(\hat\pi_h)_{h\in[H]}$. The source writes this maximization without discussing existence; a maximizer exists when $A$ is finite and nonempty, for instance a point mass on an action maximizing $\widehat Q_h(x,\cdot)$, and the algorithm is defined when one exists for every $h$ and $x$. The event $\mathcal E$ and the probability statements about it also need measurable estimates and policy choices; on general state spaces the estimates and chosen maximizers must be jointly measurable in the state and the data, so that the output policy is a measurable kernel. The source likewise does not discuss this; the result pages assume it and separately require $\mathcal E$ to be measurable.

The penalty is the exploration bonus of optimistic online algorithms with its sign flipped. The construction of $\widehat{\mathbb B}_h$ and $\Gamma_h$ is left open; for linear MDPs, ridge regression and an elliptical penalty give [pessimistic value iteration in linear MDPs](pessimistic-value-iteration-in-linear-mdps.md).

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Proof depends on

None. This page is a definition.

## Expansion

The suboptimality of any greedy-on-estimates policy decomposes into a term from evaluation errors $\iota_h=\mathbb B_h\widehat V_{h+1}-\widehat Q_h$ along the learned policy's trajectories (spurious correlation, since $\hat\pi$ and $\iota_h$ both depend on $\mathcal D$), a term along the optimal policy's trajectories (intrinsic uncertainty), and a nonpositive optimization term (their Lemma 3.1). On $\mathcal E$, the penalty together with the truncation at $0$ makes $\iota_h\ge0$ pointwise, which removes the spurious-correlation term.

## Sources

- Y. Jin, Z. Yang and Z. Wang, *Is Pessimism Provably Efficient for Offline RL?*, Proceedings of the 38th International Conference on Machine Learning, PMLR 139:5084–5096 (2021). [arXiv:2012.15085v3](https://arxiv.org/abs/2012.15085v3), §2.1–§2.2 (episodic MDP, Definition 2.1, Assumption 2.2), §3.1 (Lemma 3.1) and §4.1 (Definition 4.1, Algorithm 1); these numbers match the conference version.
