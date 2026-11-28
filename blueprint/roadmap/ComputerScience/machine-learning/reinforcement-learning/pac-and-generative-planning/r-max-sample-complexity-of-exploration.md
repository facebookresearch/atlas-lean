# Sample complexity of exploration of R-max

With an optimistic initial value $U \ge Q^*$ bounded by $V_{\max}$, R-max with suitable inputs in a discounted MDP is, with probability $1-\delta$, $\varepsilon$-optimal on all but $\tilde O(|\{(s,a) : U(s,a) \ge V^*(s) - \varepsilon\}|\, S\, V_{\max}^3/(\varepsilon^3(1-\gamma)^3))$ steps, which is $\tilde O(S^2 A/(\varepsilon^3(1-\gamma)^6))$ when $U \equiv 1/(1-\gamma)$.

**Setting.** Let $M = \langle S, A, T, R, \gamma\rangle$ be a finite MDP with reward distributions in $[0, 1]$ and $0 \le \gamma < 1$, and let $U$ be an admissible heuristic: $Q^*(s, a) \le U(s, a) \le V_{\max} \le 1/(1-\gamma)$ for all pairs. R-max with inputs $m$ (a visit threshold) and $\varepsilon_1$ (a planning accuracy) counts the experiences $n(s, a)$ of each pair, capped at $m$, and keeps the empirical mean reward $\hat R(s, a)$ and empirical next-state distribution $\hat T(\cdot \mid s, a)$ of the first $m$ experiences. Its action values approximately solve, to accuracy $\varepsilon_1$ by value iteration,

$$Q(s, a) = \hat R(s, a) + \gamma\sum_{s'}\hat T(s' \mid s, a)\max_{a'}Q(s', a') \ \text{ if } n(s, a) \ge m, \qquad Q(s, a) = U(s, a) \ \text{ otherwise},$$

recomputed whenever some $n(s, a)$ reaches $m$, and it always acts greedily with respect to $Q$.

**Theorem.** Suppose $0 < \varepsilon < 1/(1-\gamma)$ and $0 < \delta < 1$, and let $M$ be any such MDP. There are inputs $m = m(1/\varepsilon, 1/\delta)$ and $\varepsilon_1$ with

$$m = O\Big(\frac{(S + \ln(SA/\delta))V_{\max}^2}{\varepsilon^2(1-\gamma)^2}\Big), \qquad \frac{1}{\varepsilon_1} = O\Big(\frac{1}{\varepsilon}\Big),$$

such that, if R-max runs on $M$ with these inputs and $\mathcal A_t$, $s_t$ denote its policy and state at time $t$, then with probability at least $1-\delta$ the inequality $V^{\mathcal A_t}_M(s_t) \ge V^*_M(s_t) - \varepsilon$ holds for all but

$$O\Big(\frac{|\{(s, a) \in S \times A : U(s, a) \ge V^*(s) - \varepsilon\}|}{\varepsilon^3(1-\gamma)^3}\Big(S + \ln\frac{SA}{\delta}\Big)V_{\max}^3\ln\frac{1}{\delta}\ln\frac{1}{\varepsilon(1-\gamma)}\Big)$$

time steps $t$; the constants in the $O(\cdot)$ terms are absolute. The source prints $0 \le \varepsilon$ and $0 \le \delta$, but $m$ is defined only for positive values. With $U(s, a) = V_{\max} = 1/(1-\gamma)$ the counted set has at most $SA$ pairs and the bound is $\tilde O(S^2 A/(\varepsilon^3(1-\gamma)^6))$, where $\tilde O$ hides logarithmic factors.

## Depends on

- [Sample complexity of exploration](sample-complexity-of-exploration.md)

## Proof depends on

- [PAC-MDP theorem for optimistic greedy algorithms](pac-mdp-theorem-for-optimistic-algorithms.md)
- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)
- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/azuma-hoeffding-bounded-conditional-ranges.md)
- [Bellman's operator is a contraction](../../../heuristic-search-and-planning/value-iteration/bellman-contracting.md)

## Expansion

Take $K_t = \{(s, a) : n_t(s, a) \ge m\}$ and $\varepsilon_1 = \varepsilon/2$. Hoeffding's inequality for rewards and the $\ell_1$ deviation bound of Weissman et al. for next-state distributions, with a union bound over pairs, show that for $m \ge C V_{\max}^2 (S + \ln(SA/\delta))/(\varepsilon_1^2(1-\gamma)^2)$ every policy's value in the empirical known state-action MDP is within $\varepsilon_1$ of its value in the true one, by a simulation bound for models with nearby rewards and transitions. Value iteration, a $\gamma$-contraction, reaches accuracy $\varepsilon_1$ in $\lceil \ln(1/(\varepsilon_1(1-\gamma)))/(1-\gamma) \rceil$ iterations. Optimism follows because replacing unknown pairs by self-loops paying $(1-\gamma)U$ can only raise values, and accuracy follows from the same event. With high probability a pair with $U(s, a) < V^*(s) - \varepsilon$ is never tried, and every other pair escapes at most $m$ times before joining $K$, so the learning complexity is at most $|\{(s, a) : U(s, a) \ge V^*(s) - \varepsilon\}|\, m$; the PAC-MDP theorem then gives the bound. The online samples are not independent, but the tail bounds still hold by a martingale argument. The source pairs this with a lower bound of order $(SA/\varepsilon^2)\ln(S/\delta)$ for algorithms with deterministic policies that change only at the current state (its Theorem 26).

## Sources

- A. L. Strehl, L. Li and M. L. Littman, "Reinforcement Learning in Finite MDPs: PAC Analysis", *Journal of Machine Learning Research* 10 (2009), 2413–2444, [jmlr.org](https://jmlr.org/papers/volume10/strehl09a/strehl09a.pdf): Sections 1.2–1.3 (pp. 2416–2417), Section 2.1 and Algorithm 1 (pp. 2419–2422), Theorem 11, Lemmas 12–15 and the proof of Theorem 11 (Section 3.2, pp. 2428–2432); Theorem 26 (Section 4, p. 2437).
