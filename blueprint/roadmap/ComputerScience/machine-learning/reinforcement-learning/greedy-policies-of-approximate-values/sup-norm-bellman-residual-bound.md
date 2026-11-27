# Sup-norm Bellman residual bound for a greedy policy

Let $S$ and $A$ be finite nonempty sets of states and actions. Consider a
Markov decision process with real one-step expected rewards $r(s,a)$ and
transition probabilities $P(s,a,s')\ge 0$ such that
$\sum_{s'\in S}P(s,a,s')=1$ for every $(s,a)$. Fix $0\le\gamma<1$. Write
$T$ for the Bellman optimality operator, $T_\pi$ for the Bellman operator
of a deterministic stationary policy $\pi:S\to A$, $V^*$ for the optimal
value, and $V^\pi$ for the value of $\pi$. Use
$\|U\|_\infty=\max_{s\in S}|U(s)|$ for $U:S\to\mathbb R$.

For every $W:S\to\mathbb R$ and every deterministic stationary policy
$\pi$ greedy with respect to $W$, meaning $T_\pi W=TW$, one has

$$
\|V^*-V^\pi\|_\infty \le \frac{2}{1-\gamma}\,\|TW-W\|_\infty.
$$

Unlike a bound in terms of $\|V^*-W\|_\infty$, this estimate uses the
Bellman residual of $W$ and does not require knowing $V^*$ to compute it.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic Markov decision process](../../../heuristic-search-and-planning/value-iteration/stochastic.md)
- [Bellman optimality operator](../../../heuristic-search-and-planning/value-iteration/bellman.md)
- [Bellman operator of a policy](../../../heuristic-search-and-planning/value-iteration/policy-bellman.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)
- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md)

## Proof depends on

- [Componentwise Bellman residual bound for a greedy policy](componentwise-bellman-residual-bound.md)
- [A greedy policy for the optimal value is optimal](../../../heuristic-search-and-planning/value-iteration/policy-value-greedy.md)
- [Absolute value bound for a Markov reward process](../stochastic-policies-and-discounted-occupancy/abs-mrp-value-le.md)

## Proof

Choose a policy $\pi^*$ greedy for $V^*$, which exists because the action
set is finite and nonempty. It is optimal. Put $e=TW-W$ and let
$R_\sigma(c)$ be the value of the Markov reward process with the transition
matrix of $\sigma$ and reward $c$, at discount $\gamma$. The componentwise
bound puts $V^*-V^\pi$ between zero and
$R_{\pi^*}(|e|)+R_\pi(|e|)$.
For each of the two terms, the absolute value bound for a Markov reward
process with reward $|e|$ gives a bound of $\|e\|_\infty/(1-\gamma)$ at
every state. Taking the maximum gives (4.5).

The coefficient $2/(1-\gamma)$ is the one in (4.5); no sharpness claim
is made here. For $\gamma=0$, greediness maximizes the immediate expected
reward, so the loss is zero.

## Sources

- R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007), [DOI 10.1137/040614384](https://doi.org/10.1137/040614384). [Author manuscript, HAL inria-00124685 v1](https://inria.hal.science/inria-00124685v1/document), §4.2, equation (4.5) and its derivation from Lemma 4.3.
