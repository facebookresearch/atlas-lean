# Deterministic stationary policies suffice

Let a finite discounted MDP have bounded rewards and discount $0 \le \gamma < 1$, and let $V^*$ be the unique
fixed point of the Bellman optimality operator. For every state $s$, the supremum of $V^\pi(s)$ over all
history-dependent randomized policies $\pi$ equals $V^*(s)$, and it is attained simultaneously for all
states by any deterministic stationary policy that is greedy with respect to $V^*$.

## Depends on

- [History-dependent randomized policies and trajectory laws](history-dependent-randomized-policies-and-trajectory-laws.md)
- [Bellman's operator is a contraction](../value-iteration/bellman-contracting.md)

## Proof depends on

- [Optimality of stationary policies](../optimality-of-stationary-policies/is-greatest-markov-value.md)
- [Policy improvement theorem](../policy-iteration/policy-value-le-policy-value-improve.md)

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and Algorithms*, monograph draft, Theorem 1.7 (Section 1.1.3), for rewards in $[0,1]$; bounded rewards follow by an affine change of reward. <https://rltheorybook.github.io/rltheorybook_ABJKS.pdf>
- Cs. Szepesvári, *Algorithms for Reinforcement Learning*, Morgan & Claypool, 2010 (author copy), Section 1.2 (behaviors
  as history-dependent action rules) and Appendix A.2 (the optimal values over stationary policies and over all policies
  coincide for the discounted MDPs considered; the proof is omitted there). <https://sites.ualberta.ca/~szepesva/papers/RLAlgsInMDPs.pdf>
