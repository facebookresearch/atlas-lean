# Stateful oracle handlers that are identical until bad

Let $\Sigma$ be a state space with a distinguished set $\mathrm{Bad} \subseteq \Sigma$ of *bad* states, and let $H_1, H_2$ be stateful probabilistic oracle handlers: on query $q$ in state $\sigma$, $H_j$ returns a distribution $H_j(q, \sigma)$ on pairs (answer, next state). The handlers are *identical until bad* if

1. for every good state $\sigma \notin \mathrm{Bad}$, every query $q$, every answer $a$ and every good next state $\sigma' \notin \mathrm{Bad}$, $\Pr[H_1(q,\sigma) = (a, \sigma')] = \Pr[H_2(q,\sigma) = (a, \sigma')]$; and
2. bad states are absorbing for both handlers: from a bad state every transition leads to a bad state.

The usual instance augments a base state with a sticky Boolean *bad flag* that a handler raises when it deviates from the other.

## Depends on

- [Adaptive oracle algorithms](../oracle-algorithms/oracle-comp.md)
- [Running against a stateful randomized oracle](../lazy-sampling-and-the-prp-prf-switching-lemma/run-state.md)

## Sources

- M. Bellare and P. Rogaway, "The Security of Triple Encryption and a Framework for Code-Based Game-Playing Proofs", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, 2006.
- V. Shoup, "Sequences of Games: A Tool for Taming Complexity in Security Proofs", IACR Cryptology ePrint Archive, Report 2004/332, 2004.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
