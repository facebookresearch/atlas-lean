# Regret against the optimal average reward

For learning in an unknown communicating MDP without episodes, the regret of an algorithm after $T$ steps from a start state $s$ is $T\rho^\star(M)$ minus the total reward it collected, where $\rho^\star(M)$ is the optimal long-run average reward. Rewards are random with means in $[0,1]$, and the regret is a random variable.

Let $M$ be a finite [MDP](../../../heuristic-search-and-planning/value-iteration/mdp.md) with $S$ states and $A$ actions in which taking action $a$ in state $s$ yields a reward drawn independently from a distribution on $[0, 1]$ with mean $\bar r(s, a)$ and a next state drawn from $p(\cdot \mid s, a)$. A learning algorithm $\mathfrak{A}$, started in state $s$, chooses each action, possibly at random, from the history of states, actions and rewards so far; only $\mathcal{S}$ and $\mathcal{A}$ are known to it. Let $r_t$ be the reward at step $t$ and

$$
R(M, \mathfrak{A}, s, T) = \sum_{t=1}^{T} r_t, \qquad \rho(M, \mathfrak{A}, s) = \lim_{T \to \infty} \frac{1}{T}\, \mathbb{E}\big[R(M, \mathfrak{A}, s, T)\big]
$$

when the limit exists. If $M$ is communicating, that is, its [diameter](diameter-of-an-mdp.md) is finite, the optimal average reward $\rho^\star(M) = \max_\pi \rho(M, \pi, s)$ over stationary policies $\pi : \mathcal{S} \to \mathcal{A}$ does not depend on $s$, and the total regret of $\mathfrak{A}$ after $T$ steps is

$$
\Delta(M, \mathfrak{A}, s, T) = T\rho^\star(M) - R(M, \mathfrak{A}, s, T).
$$

## Depends on

- [Diameter of a Markov decision process](diameter-of-an-mdp.md)
- [Average-reward optimality equation](../../../heuristic-search-and-planning/markov-decision-processes/average-reward-optimality-equation.md)

## Proof depends on

None.

## Expansion

This regret is undiscounted and non-episodic: there are no resets, and a mistake can strand the learner far from the good states, which is what the diameter measures. Unlike the [episodic regret](online-episodic-learning-and-regret.md), it compares realized rewards with $T\rho^\star$ rather than values of the policies played, so it carries the reward noise; Jaksch, Ortner and Auer bound it with high probability and their lower bound is for its expectation. For a communicating MDP the average-reward optimality equation gives $\rho^\star$ together with a bias vector whose span, for an optimal policy, is at most the diameter. An episodic MDP with stage-dependent transitions is a special case after augmenting the state with the stage, with $SH$ states and diameter at least $H$; Jin, Allen-Zhu, Bubeck and Jordan use this to compare the two settings. Rewards in an interval $[r_{\min}, r_{\max}]$ rescale all bounds by $r_{\max} - r_{\min}$.

## Sources

- T. Jaksch, R. Ortner and P. Auer, "Near-optimal Regret Bounds for Reinforcement Learning", *Journal of Machine Learning Research* 11 (2010), 1563–1600: Section 1 (the accumulated reward, the average reward and the total regret), Section 2 (rescaling of rewards) and Remark 8 (span of the bias). [PDF](https://www.jmlr.org/papers/volume11/jaksch10a/jaksch10a.pdf)
- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", NeurIPS 2018, footnote 1 (episodic MDPs as communicating MDPs with $SH$ states and diameter at least $H$). [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
