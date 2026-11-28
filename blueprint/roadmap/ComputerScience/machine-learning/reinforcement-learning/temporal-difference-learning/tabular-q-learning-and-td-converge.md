# Tabular Q-learning and TD(0) converge

This node collects the convergence theorems for tabular Q-learning and tabular TD(0).

## Expansion

A sound expansion has separate pages for:

1. **Q-learning, discounted.** In a finite MDP with discount $0 \le \gamma < 1$ and bounded rewards, if
   the learning rates satisfy $0 \le \alpha_t < 1$, are determined by the past (not by the sample used
   in the update), and for every state-action pair the rates used at its updates sum to infinity with
   finite sum of squares, then the Q-values converge to $Q^*$ with probability one (Watkins–Dayan; also
   as an instance of the asynchronous stochastic-approximation theorem).
2. **Q-learning, undiscounted with absorbing state.** For a finite cost-minimization MDP with $\gamma = 1$, a
   cost-free absorbing state and $Q$-values of that state initialized to $0$, under the same step-size
   conditions, $Q$-learning converges to $Q^*$ with probability one if every stationary policy is proper,
   and also if there is a proper stationary policy, every improper one has infinite expected cost from some
   state, and the iterates are bounded with probability one (Tsitsiklis, Theorem 4).
3. **TD(0) policy evaluation, discounted.** For a fixed stationary policy $\pi$ in a finite MDP with
   $0 \le \gamma < 1$ and bounded rewards, tabular TD(0) with per-state step sizes determined by the past, summing
   to infinity with finite sum of squares at each state, converges to $V^\pi$ with probability one: it is the
   asynchronous iteration with $F = T^\pi$, a maximum-norm contraction, so the weighted-pseudocontraction
   theorem applies.
4. **TD($\lambda$) for absorbing Markov chains.** For an absorbing Markov chain with no inaccessible states,
   outcomes with finite expected values, linearly independent state representations (one-hot vectors
   included), weight updates after each sequence, step sizes with infinite sum and finite sum of squares,
   and iterates projected onto a box $[-B, B]^c$ that contains the ideal predictions, linear TD($\lambda$)
   converges with probability one to the ideal predictions (Dayan and Sejnowski); the projection is part of
   their hypotheses.

## Proof depends on

- [Asynchronous stochastic approximation: convergence by box shrinking](asynchronous-stochastic-approximation-convergence-by-box-shr.md)
- [Bellman's operator is a contraction](../../../heuristic-search-and-planning/value-iteration/bellman-contracting.md)

## Sources

- C. J. C. H. Watkins and P. Dayan, *Technical note: Q-learning*, Machine Learning 8 (1992) 279–292, the Theorem of Section 2 (p. 282), proved in Section 3. <http://www.gatsby.ucl.ac.uk/~dayan/papers/cjch.pdf>
- J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Machine Learning 16 (1994) 185–202, Section 7: Assumption 7 and Theorem 4. <https://www.mit.edu/~jnt/Papers/J052-94-jnt-q.pdf>
- P. Dayan and T. J. Sejnowski, *TD($\lambda$) converges with probability 1*, Machine Learning 14 (1994) 295–301, Section 3 (convergence via Kushner and Clark, with the projection onto a box). <https://papers.cnl.salk.edu/PDFs/TD_lambda_%20Converges%20With%20Probability%201%201994-3747.pdf>
