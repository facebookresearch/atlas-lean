# Verification theorem for average-cost Markov decision processes

Let $M$ be a Markov decision process with finitely many states and actions, costs $c(s, a)$ and transition probabilities $P(s' \mid s, a)$. Suppose that a real number $g$ and a function $h$ on states satisfy

$$g + h(s) \le c(s, a) + \sum_{s'} P(s' \mid s, a) \, h(s')$$

for all states $s$ and actions $a$. Then for every initial state $s_0$ and every history-dependent, possibly randomized, policy $\pi$,

$$\liminf_{N \to \infty} \frac{1}{N} \, \mathbb{E}\Big[\sum_{t < N} c(S_t, A_t)\Big] \ge g,$$

where $S_t$ and $A_t$ are the state and action at stage $t$ under $\pi$ from $s_0$. If moreover a deterministic stationary policy $\sigma$ attains equality, $g + h(s) = c(s, \sigma(s)) + \sum_{s'} P(s' \mid s, \sigma(s)) \, h(s')$ for every state $s$, then under $\sigma$ (the policy that plays $\sigma(s)$ in the current state $s$ after every history) $\frac{1}{N} \, \mathbb{E}\big[\sum_{t < N} c(S_t, A_t)\big] \to g$ from every initial state; so $\sigma$ attains the least long-run average cost.

## Proof sketch

Summing the inequality along the trajectory gives $Ng + h(s_0) \le \mathbb{E}[\sum_{t<N}c(S_t, A_t)] + \mathbb{E}[h(S_N)]$, with equality under $\sigma$, and $h$ is bounded. Dividing by $N$ and letting $N \to \infty$ gives both assertions.

## Remarks

The existence of such a pair $(g, h)$ under a unichain or communicating condition, and the occupation-measure linear program, are separate statements. With $c = -r$, $g = -\rho$ and $h = -v$, this result gives the second assertion of the [average-reward optimality equation](../../heuristic-search-and-planning/markov-decision-processes/average-reward-optimality-equation.md): for any solution $(\rho, v)$ of that equation, $\rho$ is the optimal long-run average reward and every deterministic stationary policy greedy with respect to $v$ is optimal.

## Comparison with the source

The source proves the special case in which $g$ and $h$ satisfy Bellman's equation $g + h(s) = \min_a \big(c(s, a) + \sum_{s'}P(s' \mid s, a)h(s')\big)$ for all $s$, $\sigma$ is greedy with respect to $h$, the competing policies are deterministic Markov policies $u = (u_1, u_2, \dots)$, and the long-run average cost of a policy is $\limsup_N N^{-1}\mathbb{E}[\sum_{t<N}c(S_t, A_t)]$. It concludes that $\sigma$ has average cost $g$ from every initial state and that no such policy has a smaller one. The inequality hypothesis, history-dependent randomized policies, the bound on the $\liminf$ and the convergence of the averages under $\sigma$ follow by the same telescoping argument.

## Sources

- *2.997 Decision-Making in Large-Scale Systems*, Lecture Note 4 (Handout #6), MIT, Spring 2004, §2, Theorem 1, with the average cost defined as a lim sup in equation (1) of §1, <https://ocw.mit.edu/courses/2-997-decision-making-in-large-scale-systems-spring-2004/42e1a355d7a74c79abb0bf9c959068e5_lec_4_v1.pdf>.
