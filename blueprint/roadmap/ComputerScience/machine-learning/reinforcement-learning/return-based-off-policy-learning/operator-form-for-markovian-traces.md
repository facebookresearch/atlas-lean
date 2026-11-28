# Operator form of the return-based operator for Markovian traces

For a Markovian admissible trace $c(a,x)$, the return-based operator is $\mathcal{R}Q = Q + (I - \gamma P^{c\mu})^{-1}(T^\pi Q - Q)$, where $P^{c\mu}$ is the substochastic matrix that moves by the transition probabilities and weights the behaviour action by the trace.

Let $M$ be a Markov decision process with a finite nonempty set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $\pi$ (target) and $\mu$ (behaviour) be stochastic policies and let $c : A \times X \to [0,\infty)$ define a Markovian trace $c_s = c(a_s, x_s)$, the same function at every time, admissible for $(\pi,\mu)$: $\mu(b \mid y)\, c(b,y) \le \pi(b \mid y)$ for all $y, b$. Define the operator on Q-functions

$$(P^{c\mu}Q)(x,a) = \sum_{x' \in X} \sum_{a' \in A} P(x' \mid x,a)\, \mu(a' \mid x')\, c(a',x')\, Q(x',a') .$$

As a matrix it has nonnegative entries and row sums at most $1$. Then the matrix $I - \gamma P^{c\mu}$ is invertible, its inverse $\sum_{t \ge 0} \gamma^t (P^{c\mu})^t$ has nonnegative entries, and the return-based operator $\mathcal{R}$ of $(\pi, \mu, c)$ is, for every Q-function $Q$,

$$\mathcal{R}Q = Q + \sum_{t \ge 0} \gamma^t (P^{c\mu})^t (T^\pi Q - Q) = Q + (I - \gamma P^{c\mu})^{-1}(T^\pi Q - Q) .$$

The identity uses that the trace is Markovian and time-homogeneous; for history-dependent traces no such form is claimed.

## Depends on

- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Causal trace](causal-trace.md)
- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)

## Proof depends on

- [History-dependent randomized policies and trajectory laws](../../../heuristic-search-and-planning/markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)
- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)
- [Neumann series for the Leontief inverse when row sums are below one](../../../../Economics/general-equilibrium/leontief-input-output-model/has-sum-pow-of-row-sum-lt-one.md)
- [Causal trace](causal-trace.md)
- [Conditional expectation given a σ-field](../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)

## Expansion

Row sums: $\sum_{x'} P(x' \mid x,a) \sum_{a'} \mu(a' \mid x')\, c(a',x') \le \sum_{x'} P(x' \mid x,a) \sum_{a'} \pi(a' \mid x') = 1$, so $\gamma P^{c\mu}$ is a nonnegative matrix with row sums at most $\gamma < 1$, and its power series converges to $(I - \gamma P^{c\mu})^{-1}$, which therefore has nonnegative entries. Under the trajectory law from the forced pair $(x,a)$, induction on $t$ with the product form of the law gives $\mathbb{E}^\mu_{x,a}[\prod_{s=1}^t c(a_s,x_s)\, f(x_t,a_t)] = ((P^{c\mu})^t f)(x,a)$ for every function $f$ on pairs. The finite sum over $x_{t+1}$ gives the version $\mathbb{E}[\delta_t \mid h_t, a_t] = (T^\pi Q - Q)(x_t,a_t)$: on each of the finitely many events $\{(h_t,a_t) = (h,b)\}$, where the trace product is constant, $\delta_t$ and $(T^\pi Q - Q)(x_t,a_t)$ have the same integral. Summing over these events, the $t$-th term of the series defining $\mathcal{R}Q$ is $\gamma^t ((P^{c\mu})^t (T^\pi Q - Q))(x,a)$.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.2 (definition of $P^{c\mu}$ and the rewriting of $\mathcal{R}_k$ in the proof sketch of Theorem 2), Appendix C (the same rewriting at its start).
