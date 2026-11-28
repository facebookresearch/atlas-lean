# PAC-MDP theorem for optimistic greedy algorithms

A greedy learning algorithm whose action values stay optimistic and accurate on a known state-action MDP, and which has at most $\zeta$ update events (steps at which some action value changes) and escapes from the known set, acts $4\varepsilon$-optimally, with probability at least $1-2\delta$, on all but $O(V_{\max}\zeta\,\varepsilon^{-1}(1-\gamma)^{-1}\ln(1/\delta)\ln(1/(\varepsilon(1-\gamma))))$ steps.

**Setting.** Let $M = \langle S, A, T, R, \gamma\rangle$ be a finite MDP with rewards in $[0, 1]$ and $0 \le \gamma < 1$, and let $V_{\max} \le 1/(1-\gamma)$ be a known bound with $V^*_M \le V_{\max}$ (in the source this follows from its standing admissible-heuristic assumption $Q^* \le U \le V_{\max}$). A learning algorithm maintains action values $Q_t(s, a)$ (the values just before the $t$-th action) and is greedy if its $t$-th action is $a_t = \arg\max_a Q_t(s_t, a)$, with ties broken by a fixed rule, so that the same action values give the same action at each state; write $V_t(s) = \max_a Q_t(s, a)$ and $\pi_t$ for the greedy policy of $Q_t$ under this rule. For a set $K$ of state-action pairs, the known state-action MDP $M_K$ has states $S \cup \{z_{s,a} : (s, a) \notin K\}$; it agrees with $M$ (rewards and transitions) on pairs in $K$, while a pair $(s, a) \notin K$ pays $(1-\gamma)Q(s, a)$ and moves to $z_{s,a}$, which loops to itself under every action with reward $(1-\gamma)Q(s, a)$. If $K_t$ is a set of pairs determined by the history up to time $t$, the escape event at time $t$ is that the pair experienced at time $t$ is not in $K_t$. An update event at time $t$ is a time step at which at least one maintained action value changes, $Q_{t+1} \ne Q_t$; it counts once, however many entries change and however many computation steps (for example sweeps of value iteration) produce the change.

**Theorem.** Let $\mathcal A(\varepsilon, \delta)$ be a greedy learning algorithm such that for every time $t$ there is a set $K_t$ of state-action pairs depending only on the history up to $t$, with $K_t = K_{t+1}$ unless an update event or the escape event occurs at time $t$. Let $M_{K_t}$ be the known state-action MDP built from $Q_t$, and assume $Q_t(s, a) \le V_{\max}$ for all $t, s, a$. Suppose that for all inputs $\varepsilon, \delta$, with probability at least $1-\delta$, for all states $s$, actions $a$ and times $t$:

1. (optimism) $V_t(s) \ge V^*(s) - \varepsilon$;
2. (accuracy) $V_t(s) - V^{\pi_t}_{M_{K_t}}(s) \le \varepsilon$;
3. (learning complexity) the number of update events plus the number of escape events is at most $\zeta(\varepsilon, \delta)$.

Then there is an absolute constant $C$ such that, when $\mathcal A(\varepsilon, \delta)$ is run on $M$, with probability at least $1-2\delta$ it follows a $4\varepsilon$-optimal policy from its current state, that is $V^{\mathcal A_t}_M(s_t) \ge V^*_M(s_t) - 4\varepsilon$, on all but

$$C\,\frac{V_{\max}\,\zeta(\varepsilon, \delta)}{\varepsilon(1-\gamma)}\ln\frac{1}{\delta}\ln\frac{1}{\varepsilon(1-\gamma)}$$

time steps, for $0 < \varepsilon < 1/(1-\gamma)$ and $0 < \delta < 1$.

The source concludes "when run on any MDP $M$"; since the hypotheses refer to the optimal values of a given MDP, the conclusion is stated for that MDP, which is how the theorem is applied to R-max and Delayed Q-learning, whose hypotheses hold on every MDP.

## Depends on

- [Sample complexity of exploration](sample-complexity-of-exploration.md)
- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md)

## Proof depends on

- [Epsilon-horizon time truncation](epsilon-horizon-time-truncation.md)
- [Multiplicative Chernoff bounds](../../../../Probability/concentration-inequalities/chernoff-and-bernoulli-comparison-bounds/multiplicative-chernoff-bounds.md)
- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/azuma-hoeffding-bounded-conditional-ranges.md)

## Expansion

Let $H = (1/(1-\gamma))\ln(1/(\varepsilon(1-\gamma)))$, so that $H$-step values are within $\varepsilon$ of infinite-horizon values. Let $W$ be the event that within $H$ steps of following the algorithm from $s_t$ an update event occurs or some pair outside $K_t$ is experienced. Until $W$ occurs the algorithm behaves exactly like $\pi_t$ in $M_{K_t}$, and optimal values of $M_{K_t}$ are at most $2V_{\max}$, so

$$V^{\mathcal A_t}_M(s_t, H) \ge V^{\pi_t}_{M_{K_t}}(s_t) - \varepsilon - 2V_{\max}\Pr(W) \ge V^*(s_t) - 3\varepsilon - 2V_{\max}\Pr(W)$$

by accuracy and optimism. If $\Pr(W) < \varepsilon/(2V_{\max})$ the step is $4\varepsilon$-optimal. Otherwise each such step starts an $H$-step trial that succeeds with probability at least $\varepsilon/(2V_{\max})$; since at most $\zeta$ successes can occur, a coin-flipping bound (the source's Lemma 8, stated for independent tosses; the trials here overlap and are chosen adaptively, which the martingale form of the bound covers) shows that, with probability $1-\delta$, there are only $O(\zeta H V_{\max}\varepsilon^{-1}\ln(1/\delta))$ such steps. The theorem is the general tool behind the PAC-MDP bounds for R-max and Delayed Q-learning and generalizes the known-state arguments of E3 and R-max.

## Sources

- A. L. Strehl, L. Li and M. L. Littman, "Reinforcement Learning in Finite MDPs: PAC Analysis", *Journal of Machine Learning Research* 10 (2009), 2413–2444, [jmlr.org](https://jmlr.org/papers/volume10/strehl09a/strehl09a.pdf): Section 1.3 (admissible heuristics, p. 2417), Definitions 5–7, Lemmas 8 and 9, and Theorem 10 with its proof (Section 3.1, pp. 2425–2428).
