# Bellman values are expected discounted returns

Let a Markov decision process have finite state and action sets, bounded costs $c(s, a)$, transition kernel $P$ and a deterministic stationary policy $\pi$, and let $(S_t, A_t)$ be the state–action process with $S_0 = s$, $A_t = \pi(S_t)$ and $S_{t+1} \sim P(\cdot \mid S_t, A_t)$. For $0 \le \gamma < 1$, the unique bounded solution $V^\pi$ of $V(s) = c(s, \pi(s)) + \gamma\sum_{s'}P(s' \mid s, \pi(s))V(s')$ satisfies $V^\pi(s) = E_s[\sum_{t \ge 0}\gamma^tc(S_t, A_t)]$, the series converging absolutely. For a finite horizon $N$ with terminal cost $g$ and a policy indexed by the number of steps remaining, the action at time $t < N$ is $\pi(N - t, S_t)$, and the backward recursion $V_0 = g$, $V_k(s) = c(s, \pi(k, s)) + \gamma\sum_{s'}P(s' \mid s, \pi(k, s))V_{k-1}(s')$ gives $V_N(s) = E_s[\sum_{t<N}\gamma^tc(S_t, A_t) + \gamma^Ng(S_N)]$; the terminal cost is counted once, with exponent $N$. Randomized history-dependent policies and rewards correlated with the next state need a separately specified trajectory law. With rewards $r = -c$ and terminal reward $-g$ the same statements hold with every value negated.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- The policy kernel, time augmentation and reindexing that turn the Markov chain construction into the state–action process of a deterministic (possibly time-indexed) policy on a finite Markov decision process.
- Identification of the policy Bellman solution and of the finite-horizon backward recursion with the expected discounted cost, and with the expected cost including the terminal cost, under that trajectory law.

## Background

- [Value of a stochastic policy](stochastic-policies-and-discounted-occupancy/stoch-value.md): the value of a stochastic policy defined as the solution of the policy Bellman equation.
- [Markov chain construction theorem](../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-construction.md): the trajectory law of a Markov chain with given initial law and transition kernel.

## Sources

- R. S. Sutton and A. G. Barto, *Reinforcement Learning: An Introduction*, 2nd ed., MIT Press, 2018, <http://incompleteideas.net/book/RLbook2020.pdf>, §3.5, equations (3.12)–(3.14)
