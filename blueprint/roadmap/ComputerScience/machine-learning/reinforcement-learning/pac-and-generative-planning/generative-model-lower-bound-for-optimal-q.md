# Lower bound for estimating optimal action values

For discount factors $\gamma \in [0.4, 1)$, every algorithm that estimates the optimal action-value function to sup-norm accuracy $\varepsilon$ with probability $1-\delta$ on a suitable class of MDPs with $N$ state-action pairs needs at least of order $N(1-\gamma)^{-3}\varepsilon^{-2}\log(N/\delta)$ transition samples, matching model-based Q-value iteration.

**Setting.** Discounted MDPs with finite state and action sets, $N$ state-action pairs, deterministic rewards in $[0, 1]$, discount $\gamma$ with $0.4 \le \gamma < 1$, and $\beta = 1/(1-\gamma)$. An algorithm $\mathcal A$ observes state-transition samples and outputs $Q^{\mathcal A} : S \times A \to \mathbb R$; it is $(\varepsilon, \delta)$-correct on a class $\mathcal M$ of MDPs if $\|Q^* - Q^{\mathcal A}\|_\infty \le \varepsilon$ with probability at least $1-\delta$ for every $M \in \mathcal M$.

**Theorem.** There exist absolute constants $\varepsilon_0, \delta_0, c_1, c_2 > 0$ such that for every $\gamma \in [0.4, 1)$ and every number of state-action pairs $N$ of the form $3KL$ there is a class $\mathcal M_\gamma$ of MDPs with discount $\gamma$ and $N$ state-action pairs for which, for all $\varepsilon \in (0, \varepsilon_0)$ and $\delta \in (0, \delta_0)$, every $(\varepsilon, \delta)$-correct algorithm on $\mathcal M_\gamma$ uses a total number of state-transition samples of at least

$$T = \frac{\beta^3 N}{c_1\varepsilon^2}\log\frac{N}{c_2\delta}.$$

The authors note that the argument does not depend on how samples are collected, so it also bounds online algorithms. The range $0.4 \le \gamma < 1$ is the one for which the source's proof establishes the bound (its Section 4.2 fixes $\gamma_0 = 0.4 \le \gamma < 1$); the statement of its Theorem 3 leaves this restriction implicit. The source's constants are numerical ($c_1 = 8100$ and $c_2 = 72$ in its proof), which is what makes the bound informative about $\beta^3$. Its proof also needs $\varepsilon$ small enough that the perturbed transition probability $p + \alpha$ below stays a probability, a condition that holds uniformly for $\gamma \ge 0.4$ once $\varepsilon$ is below an absolute constant; the source's printed range $\varepsilon \in (0, 3]$ is not used here.

## Depends on

- [Generative model of an MDP](generative-model-of-an-mdp.md)
- [Q-value of an action](../../../heuristic-search-and-planning/value-iteration/q-value.md)

## Proof depends on

None.

## Expansion

The hard MDPs have $K$ decision states with $L$ actions each; action $a$ at state $x$ leads deterministically to a single-action state $y(x, a)$ paying reward $1$ that returns to itself with probability $p_M$ and otherwise moves to an absorbing state paying $0$, so $Q^*_M(x, a) = \gamma/(1 - \gamma p_M)$. Two models with $p_M = p$ and $p + \alpha$, where $\alpha = 2(1-\gamma p)^2\varepsilon/\gamma^2$ and $p = (4\gamma - 1)/(3\gamma)$, have optimal values more than $2\varepsilon$ apart, while a likelihood-ratio (change-of-measure) argument with a Chernoff bound for Bernoulli sums shows that $t$ samples from $y(x, a)$ cannot tell them apart with probability $1-\delta$ unless $t$ is of order $\beta^3\varepsilon^{-2}\log(1/\delta)$; the self-loop with probability close to $1$ amplifies the effect of estimation errors through the factor $\beta^3$. Since samples at different pairs carry independent information, an algorithm with fewer than $(N/6)$ times this many samples leaves at least $N/6$ pairs under-sampled; running the two-point argument at each of them with per-pair confidence $12\delta/N$ makes the overall failure probability exceed $\delta$. Later work observed that the argument extends to accuracies up to order $1/(1-\gamma)$.

## Sources

- M. G. Azar, R. Munos and H. J. Kappen, "Minimax PAC bounds on the sample complexity of reinforcement learning with a generative model", *Machine Learning* 91 (2013), 325–349, doi:10.1007/s10994-013-5368-1: Definition 1 and Theorem 3 (p. 331), proof in Section 4.2 including Lemmas 16–18 (pp. 342–347).
- G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, "Breaking the Sample Size Barrier in Model-Based Reinforcement Learning with a Generative Model", *Advances in Neural Information Processing Systems* 33 (NeurIPS 2020), [proceedings.neurips.cc](https://proceedings.neurips.cc/paper/2020/hash/96ea64f3a1aa2fd00c72faacf0cb8ac9-Abstract.html): the remark after Theorem 1 (Section 3) on the accuracy range of this lower bound.
