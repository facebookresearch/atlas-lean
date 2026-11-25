# Verification theorem for average-cost Markov decision processes

Let a Markov decision process have finite state and action sets, costs $c(s, a)$ and transition probabilities $P(s' \mid s, a)$. Suppose a real $g$ and a function $h$ on states satisfy $g + h(s) \le c(s, a) + \sum_{s'}P(s' \mid s, a)h(s')$ for all $s, a$. Then for every initial state and every history-dependent, possibly randomized, policy, $\liminf_N N^{-1}E[\sum_{t<N}c(S_t, A_t)] \ge g$. If a stationary policy $\pi$ attains equality, $g + h(s) = c(s, \pi(s)) + \sum_{s'}P(s' \mid s, \pi(s))h(s')$ for all $s$, then $N^{-1}E[\sum_{t<N}c(S_t, A_t)] \to g$ under $\pi$ from every initial state, so $\pi$ attains the least long-run average cost. Proof: summing the inequality along the trajectory gives $Ng + E[h(S_0)] \le E[\sum_{t<N}c(S_t, A_t)] + E[h(S_N)]$, and $h$ is bounded. Existence of such $(g, h)$ under a unichain or communicating condition, and the occupation-measure linear program, are separate statements.

## Sources

- *2.997 Decision-Making in Large-Scale Systems*, Lecture Note 4 (Handout #6), MIT, Spring 2004, §1, Theorem 1, <https://ocw.mit.edu/courses/2-997-decision-making-in-large-scale-systems-spring-2004/42e1a355d7a74c79abb0bf9c959068e5_lec_4_v1.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
