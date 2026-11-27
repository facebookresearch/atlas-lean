# Variance-reduced Q-value iteration

With a generative model whose samples cost constant time, variance-reduced Q-value iteration computes an $\varepsilon$-optimal policy of a discounted MDP with probability $1-\delta$ using time and samples $\tilde O(|S||A|/((1-\gamma)^3\varepsilon^2))$, for $\varepsilon, \delta \in (0, 1)$, and space $O(|S||A|)$.

**Setting.** Let $M = (S, A, P, r, \gamma)$ be a discounted MDP with finite state and action sets, known rewards $r \in [0, 1]^{S \times A}$ and $\gamma \in (0, 1)$, accessed through a generative model that returns a sample of $P(\cdot \mid s, a)$ in $O(1)$ time. A policy $\pi$ is $\varepsilon$-optimal if $\|V^* - V^\pi\|_\infty \le \varepsilon$.

**Algorithm (variance-reduced QVI).** A halving routine takes values $v^{(0)}$ and a policy $\pi^{(0)}$ with $v^{(0)} \le \mathcal T_{\pi^{(0)}}v^{(0)}$ and $V^* - v^{(0)} \le u\mathbf 1$, for $u \in (0, (1-\gamma)^{-1}]$. It estimates $Pv^{(0)}$ and the variances $\mathrm{Var}_P(v^{(0)})$ once, from $m_1$ samples per pair with $m_1$ of order $(1-\gamma)^{-3}u^{-2}\log(|S||A|/\delta)$, and shifts the estimate down by its Bernstein confidence width. For $R$ of order $(1-\gamma)^{-1}\log((1-\gamma)^{-1}u^{-1})$ rounds it then estimates $P(v^{(i)} - v^{(0)})$ from $m_2$ fresh samples per pair, $m_2$ of order $(1-\gamma)^{-2}\log(R|S||A|/\delta)$, shifts this estimate down by $(1-\gamma)u/8$, forms $Q^{(i)} = r + \gamma(w + g^{(i)})$, and takes the greedy values and policy, keeping the previous ones at states where the value would decrease. It outputs $v, \pi$ with $v \le \mathcal T_\pi v$ and $V^* - v \le (u/2)\mathbf 1$ with probability $1-\delta$. The full algorithm starts from $v = 0$ and applies the routine $\Theta(\log(\varepsilon^{-1}(1-\gamma)^{-1}))$ times with $u = 2^{-i+1}(1-\gamma)^{-1}$, drawing fresh samples each time.

**Theorem.** For any $\varepsilon, \delta \in (0, 1)$ there is an algorithm that halts in time

$$T = O\Big(\frac{|S||A|}{(1-\gamma)^3\varepsilon^2}\log\frac{|S||A|}{(1-\gamma)\delta\varepsilon}\log\frac{1}{(1-\gamma)\varepsilon}\Big),$$

uses space $O(|S||A|)$, queries the generative model for at most $O(T)$ fresh samples, and with probability at least $1-\delta$ outputs a policy $\pi$ with $V^* - \varepsilon\mathbf 1 \le V^\pi \le V^*$.

For $\varepsilon \ge 1$ the authors do not claim optimality. Up to logarithmic factors the sample count matches the lower bound, attributed by the authors to the generative-model lower-bound construction, $\Omega(|S||A|\log(|S||A|/\delta)/((1-\gamma)^3\varepsilon^2))$ for finding $\varepsilon$-optimal policies, and the running time is linear in the number of samples.

## Depends on

- [Empirical MDP from a generative model](empirical-mdp-from-a-generative-model.md)
- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md)

## Proof depends on

- [Total-variance bound](total-variance-bound.md)
- [A policy's Bellman operator is monotone](../../../heuristic-search-and-planning/value-iteration/policy-bellman-mono.md)
- [A policy's Bellman operator is a contraction](../../../heuristic-search-and-planning/value-iteration/policy-bellman-contracting.md)
- [Bernstein's inequality for bounded variables, two-sided](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-abs-ge-le-bernstein.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Expansion

Three ideas combine. *Monotonicity:* keeping $v^{(i)} \le \mathcal T_{\pi^{(i)}}v^{(i)}$ gives $v^{(i)} \le V^{\pi^{(i)}}$, so a $u$-accurate value yields a $u$-optimal policy without the usual loss of a factor $1/(1-\gamma)$; the one-sided (downward shifted) estimates preserve it with high probability. *Variance reduction:* $Pv^{(0)}$ is estimated once to high accuracy, while each round only needs $P(v^{(i)} - v^{(0)})$ with $\|v^{(i)} - v^{(0)}\|_\infty = O(u)$, which costs $\tilde O((1-\gamma)^{-2})$ samples per pair independently of $u$. *Total variance:* the per-round errors are of order $\sqrt{\mathrm{Var}_P(V^*)/m_1}$, and their accumulation $(I - \gamma P^{\pi^*})^{-1}\sqrt{\mathrm{Var}_P(V^*)}$ is $O((1-\gamma)^{-3/2})$ rather than $O((1-\gamma)^{-2})$, which removes the last factor $1/(1-\gamma)$. Bernstein and Hoeffding bounds control the empirical means and variances, and each halving round succeeds with probability $1-\delta$ in time $O((u^{-2} + \log(1/((1-\gamma)u)))\,|S||A|\log(|S||A|/\delta)/(1-\gamma)^3)$.

## Sources

- A. Sidford, M. Wang, X. Wu, L. F. Yang and Y. Ye, "Near-Optimal Time and Sample Complexities for Solving Discounted Markov Decision Process with a Generative Model", arXiv:1806.01492v3: Section 4 (technique overview), Algorithm 1 (Variance-Reduced QVI), Proposition 5.4.1, Algorithm 2 and Theorem 5.5 with Remark 5.6 (Section 5). Published as "Near-Optimal Time and Sample Complexities for Solving Markov Decision Processes with a Generative Model", *Advances in Neural Information Processing Systems* 31 (NeurIPS 2018), where the halving guarantee is Proposition 4.5 and the main result is Theorem 4.6, with the same bound.
