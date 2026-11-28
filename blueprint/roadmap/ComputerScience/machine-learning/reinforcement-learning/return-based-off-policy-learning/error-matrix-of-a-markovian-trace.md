# Error matrix of a Markovian trace

For a Markovian admissible trace, $P^\pi - P^{c\mu}$ has nonnegative entries, and $E = \gamma(I - \gamma P^{c\mu})^{-1}(P^\pi - P^{c\mu})$ is a nonnegative matrix whose rows sum to at most $\gamma$.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $\pi$ (target) and $\mu$ (behaviour) be stochastic policies and $c : A \times X \to [0,\infty)$ a Markovian trace with $\mu(b \mid y)\, c(b,y) \le \pi(b \mid y)$ for all $y, b$; let $P^\pi$ and $P^{c\mu}$ be the corresponding operators on Q-functions and $e$ the Q-function equal to $1$. Then $P^\pi - P^{c\mu}$ has nonnegative entries, and the matrix

$$E = \gamma (I - \gamma P^{c\mu})^{-1} (P^\pi - P^{c\mu})$$

has nonnegative entries and satisfies

$$E e = e - (1-\gamma) \sum_{t \ge 0} \gamma^t (P^{c\mu})^t e \le \gamma e .$$

Hence $\|EQ\| \le \gamma\|Q\|$ and $Q \le Q'$ implies $EQ \le EQ'$ for all Q-functions.

## Depends on

- [Operator form of the return-based operator for Markovian traces](operator-form-for-markovian-traces.md)
- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)
- [Causal trace](causal-trace.md)

## Proof depends on

- [Operator form of the return-based operator for Markovian traces](operator-form-for-markovian-traces.md)
- [Q-function Bellman operator of a stochastic policy](q-function-bellman-operator.md)

## Expansion

The entry of $P^\pi - P^{c\mu}$ at $((x,a),(x',a'))$ is $P(x' \mid x,a)(\pi(a' \mid x') - \mu(a' \mid x')\, c(a',x')) \ge 0$, and the Neumann series of $(I - \gamma P^{c\mu})^{-1}$ has nonnegative terms, so $E \ge 0$. Since $P^\pi e = e$,

$$E e = \gamma \sum_{t \ge 0} \gamma^t (P^{c\mu})^t e - \sum_{t \ge 0} \gamma^{t+1} (P^{c\mu})^{t+1} e = e - (1-\gamma)\sum_{t \ge 0} \gamma^t (P^{c\mu})^t e,$$

and the last series is at least its $t = 0$ term $e$. A nonnegative matrix with row sums at most $\gamma$ has sup-norm operator norm at most $\gamma$ and preserves order.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.2 (the matrix written $A_k$ in the proof sketch of Theorem 2), Appendix C, equations (10)–(12).
