# Sample bound for model-based Q-value iteration

With a generative model, $O(N\beta^3\varepsilon^{-2}\log(N/\delta))$ transition samples in total, where $N = |X||A|$ and $\beta = 1/(1-\gamma)$, suffice for model-based Q-value iteration or policy iteration to estimate the optimal action-value function to sup-norm accuracy $\varepsilon \in (0, 1)$ with probability $1-\delta$.

**Setting.** Let the discounted MDP have finite state set $X$, action set $A$, $N = |X||A|$ state-action pairs, deterministic rewards $r(x, a) \in [0, 1]$, discount $\gamma \in (0, 1)$ and $\beta = 1/(1-\gamma)$. The model estimator calls the generative model $n \ge 1$ times at each pair, a total budget of $T = nN$ samples, and forms the empirical MDP, which keeps the rewards and $\gamma$ and has transition probabilities $\hat P(y \mid x, a)$ equal to the fraction of the $n$ samples at $(x, a)$ that landed in $y$; $\hat Q^*$ is its optimal action-value function. Model-based Q-value iteration (QVI) starts from an initial action-value function $Q_0$ with entries in $[0, \beta]$ and iterates $Q_{j+1} = \hat{\mathcal T}Q_j$, where $(\hat{\mathcal T}Q)(x, a) = r(x, a) + \gamma\sum_y\hat P(y \mid x, a)\max_{b}Q(y, b)$ is the empirical Bellman optimality operator. Model-based policy iteration (PI) starts from a policy $\pi_0$ and alternates exact policy evaluation in the empirical model with greedy improvement; $Q_k$ denotes the $k$-th action-value iterate of either algorithm.

**Theorem.** There exist absolute constants $c, c_0, d, d_0$ such that for every such MDP, every $\varepsilon \in (0, 1)$ and $\delta \in (0, 1)$, and QVI started from any $Q_0$ with entries in $[0, \beta]$ or PI started from any policy $\pi_0$, a total sampling budget of

$$T = \Big\lceil \frac{c\beta^3 N}{\varepsilon^2}\log\frac{c_0 N}{\delta}\Big\rceil$$

suffices for $\|Q^* - Q_k\|_\infty \le \varepsilon$ with probability at least $1-\delta$, after $k = \lceil d\log(d_0\beta/\varepsilon)/\log(1/\gamma)\rceil$ iterations of QVI or PI.

The initialization matters: the iteration count rests on the contraction bound $\|Q_k - \hat Q^*\|_\infty \le \gamma^k\beta$, which the source proves for $Q_0$ with entries in $[0, \beta]$ (its Lemma 1); policy iteration meets it automatically, since its first iterate is a value of $\pi_0$ in the empirical model. The source's theorem is stated under its Assumption 1 with constants that do not depend on the MDP, and its iteration count needs $\gamma > 0$. The same paper bounds the sample complexity of the greedy policy $\pi_k$ of $Q_k$ by the same order, but only for $\varepsilon$ below a threshold that decreases with $|X|$ (its Theorem 2).

## Depends on

- [Generative model of an MDP](generative-model-of-an-mdp.md)
- [Q-value of an action](../../../heuristic-search-and-planning/value-iteration/q-value.md)

## Proof depends on

- [Bellman equation for the return variance](bellman-equation-for-the-return-variance.md)
- [Total-variance bound](total-variance-bound.md)
- [Bennett's one-step moment generating function bound](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/bennett-one-step-mgf-bound.md)
- [Bennett's inequality and its Bernstein relaxation](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/bennett-inequality.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)
- [Bellman's operator is a contraction](../../../heuristic-search-and-planning/value-iteration/bellman-contracting.md)
- [Simulation lemma](../simulation-lemma/stoch-value-sub-stoch-value-eq.md)
- [No deterministic policy beats the optimal value](../../../heuristic-search-and-planning/value-iteration/policy-value-le-optimal-value.md)

## Expansion

The error splits as $\|Q^* - Q_k\|_\infty \le \|Q^* - \hat Q^*\|_\infty + \gamma^k\beta$. Componentwise,

$$\gamma(I - \gamma\hat P^{\hat\pi^*})^{-1}(P - \hat P)V^* \le Q^* - \hat Q^* \le \gamma(I - \gamma\hat P^{\pi^*})^{-1}(P - \hat P)V^*,$$

with $\pi^*$ and $\hat\pi^*$ optimal in the true and the empirical model; both sides come from the simulation-lemma identity together with $\hat Q^* \ge \hat Q^{\pi^*}$ and the greediness of $\pi^*$. Bernstein's inequality for the average of $n$ independent bounded samples (Bennett's inequality in its Bernstein form) bounds $|(P - \hat P)V^*|$ by $\sqrt{2\log(N/\delta)\mathrm{Var}_P(V^*)/n}$ plus a term of order $\beta\log(N/\delta)/n$; Hoeffding's inequality shows the empirical variances of the relevant value functions are close to the true ones, and the total-variance bound turns $(I - \gamma P^\pi)^{-1}\sqrt{\sigma_{V^\pi}}$ into $O(\beta^{3/2})$ instead of $O(\beta^2)$. Hence $\|Q^* - \hat Q^*\|_\infty = O(\sqrt{\beta^3\log(N/\delta)/n})$ plus lower-order terms, and solving for $n$ gives the budget. The crude bound via Hoeffding alone loses a factor $\beta$ in the budget. A matching lower bound shows the rate is minimax for estimating $Q^*$.

## Sources

- M. G. Azar, R. Munos and H. J. Kappen, "Minimax PAC bounds on the sample complexity of reinforcement learning with a generative model", *Machine Learning* 91 (2013), 325–349, doi:10.1007/s10994-013-5368-1: Assumption 1 (p. 328), Algorithms 1–3 (pp. 329–330), Theorem 1 with footnote 5 (pp. 330–331), Theorem 2 (p. 331), and the proof of Theorem 1 through Lemmas 1, 3–9 (Section 4.1, pp. 332–339).
