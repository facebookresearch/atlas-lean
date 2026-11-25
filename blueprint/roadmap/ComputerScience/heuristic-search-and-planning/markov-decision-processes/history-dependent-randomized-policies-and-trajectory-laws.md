# History-dependent randomized policies and trajectory laws

Let a finite MDP have states $S$, actions $A$ with nonempty sets $A(s)$ of available actions, transition
probabilities $P$ and bounded rewards $r$. A history of length $t$ is $h_t = (s_0, a_0, \dots, s_t)$ with
$a_j \in A(s_j)$. A history-dependent randomized policy assigns to every history $h_t$ a probability
distribution $\pi(\cdot \mid h_t)$ on $A(s_t)$. Together with an initial state $s_0$ it determines, for each
$t$, a probability mass function on histories of length $t$, by the finite product of the policy and
transition kernels. For $0 \le \gamma < 1$ the discounted value $V^\pi(s_0) = \sum_{t \ge 0} \gamma^t
\mathbb{E}[r(s_t, a_t)]$ converges absolutely.

## Depends on

- [Markov decision process](../value-iteration/mdp.md)

## Related topics

- [Value of a Markov policy](../optimality-of-stationary-policies/markov-value.md)

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and Algorithms*, monograph draft, Section 1.1.1 (histories, general policies, trajectory distributions and the discounted value). <https://rltheorybook.github.io/rltheorybook_ABJKS.pdf>
