# LP formulation and occupancy-measure duality

Let $(S, A, P, r, \gamma)$ be a finite discounted MDP with $S$ and $A$ nonempty and $0 \le \gamma < 1$, and let $w : S \to \mathbb{R}$
be a weighting with $w(s) > 0$ for every $s$. Consider the linear program

$$\text{minimize } \sum_s w(s) V(s) \quad \text{subject to} \quad V(s) \ge r(s,a) + \gamma \sum_{s'} P(s, a, s')\, V(s') \text{ for all } s, a,$$

and its dual

$$\text{maximize } \sum_{s,a} d(s,a)\, r(s,a) \quad \text{subject to} \quad d \ge 0, \quad \sum_a d(s',a) - \gamma \sum_{s,a} P(s, a, s')\, d(s,a) = w(s') \text{ for all } s'.$$

Then:

1. the optimal value $V^*$ is the unique optimal solution of the primal;
2. the dual feasible set is exactly the set of functions $d^\pi_w/(1-\gamma)$, where $d^\pi_w$ is the discounted
   state-action occupancy of a stationary randomized policy $\pi$ from the initial weighting $w$, and
   $\pi \mapsto d^\pi_w/(1-\gamma)$ is a bijection onto it, with inverse $\pi(s, a) = d(s,a) / \sum_{a'} d(s,a')$ (the
   denominator is at least $w(s) > 0$);
3. strong duality holds with the same scaling on both sides:
   $\max_d \sum_{s,a} d(s,a) r(s,a) = \sum_s w(s) V^*(s)$.

Every dual feasible $d$ has total mass $\sum_s w(s)/(1-\gamma)$. For a probability distribution $\mu = w/\sum_s w(s)$, the
dual solutions for $w$ are $\sum_s w(s)$ times those for $\mu$, and both objectives scale by the same factor. Mixing
scalings is wrong: with one state, one action, $r = 1$, $\gamma = 1/2$ and $w = 1$, the primal value is $2$, the dual
value is $2$, and the normalized occupancy $(1-\gamma)d$ has value $1$.

## Depends on

- [Optimal value of a discounted Markov decision process](../value-iteration/optimal-value.md)
- [Stochastic policy](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/stochastic-policy.md)
- [Discounted state-action occupancy of a row-stochastic policy](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/occupancy.md)

## Proof depends on

- [Bellman's operator is a contraction](../value-iteration/bellman-contracting.md)
- [No stochastic policy beats the optimal value](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/stoch-value-le-optimal-value.md)
- [A greedy policy for the optimal value is optimal](../value-iteration/policy-value-greedy.md)
- [Total mass of the state-action occupancy of a row-stochastic policy](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/sum-occupancy.md)

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and Algorithms*,
  working draft. <https://rltheorybook.github.io/rltheorybook_ABJKS.pdf> Background reference.
- J. Huang, *Recent progress on the complexity of solving Markov decision processes*, Cornell ORIE
  survey write-up, Section 1.3.5 (the primal and dual linear programs, with all-ones weights).
  <https://people.orie.cornell.edu/jh2543/prelimWriteup.pdf>
