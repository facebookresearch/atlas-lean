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
- [Value of a Markov reward process](../stochastic-policies-and-discounted-occupancy/mrp-value.md)
- [A constant reward has constant value](../stochastic-policies-and-discounted-occupancy/mrp-value-const.md)
- [A nonnegative reward has a nonnegative value](../stochastic-policies-and-discounted-occupancy/mrp-value-nonneg.md)

## Proof

For any row-stochastic policy matrix $P_\sigma$, write
$R_\sigma=(I-\gamma P_\sigma)^{-1}$. As a Markov reward process value
operator it is entrywise nonnegative (apply it to indicator rewards), and
it sends the all-ones vector $\mathbf 1$ to $(1-\gamma)^{-1}\mathbf 1$.
Thus its row sums and its induced sup operator norm are exactly
$1/(1-\gamma)$: the row sums bound its action on any vector in the unit
ball, and $\mathbf 1$ attains the bound. Apply the componentwise bound
with any deterministic stationary optimal policy $\pi^*$. Each resolvent
term acting on $|TW-W|$ is at most
$\|TW-W\|_\infty\mathbf 1/(1-\gamma)$, and the loss is nonnegative in each
state. Taking the maximum gives (4.5).

The coefficient $2/(1-\gamma)$ is the one in (4.5); no sharpness claim
is made here. For $\gamma=0$, greediness maximizes the immediate expected
reward, so the loss is zero.

## Sources

- R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007), [DOI 10.1137/040614384](https://doi.org/10.1137/040614384). [Author manuscript, HAL inria-00124685 v1](https://inria.hal.science/inria-00124685v1/document), §4.2, equation (4.5) and its derivation from Lemma 4.3.
