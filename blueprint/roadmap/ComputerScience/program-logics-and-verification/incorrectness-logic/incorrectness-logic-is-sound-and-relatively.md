# Incorrectness logic is sound and relatively complete

Use the commands, relational semantics, truth of triples $[p]\, C\, [\epsilon : q]$ and proof rules of
[soundness of incorrectness logic](soundness-of-incorrectness-logic.md), with assertions arbitrary subsets of
$\Sigma = \mathrm{Var} \to \mathrm{Val}$ and the rule of consequence using set inclusion. Assume $\mathrm{Var}$ is countably infinite and
$\mathrm{Val} \supseteq \mathbb{N}$. Call an assertion *finitely supported* if it is invariant under changing all but finitely many
variables. Then:

- every derivable triple is true (soundness);
- every true triple $[p]\, C\, [\epsilon : q]$ with $p$ and $q$ finitely supported is derivable (completeness relative to
  semantic assertions and an oracle for their inclusions).

Completeness uses semantic assertions; it does not assume an expressive syntactic assertion language and does not
contradict undecidability of the underlying implications.

## Depends on

- [Soundness of incorrectness logic](soundness-of-incorrectness-logic.md)

## Proof depends on

- [Soundness of incorrectness logic](soundness-of-incorrectness-logic.md)

## Sources

- P. W. O'Hearn, "Incorrectness logic", *Proceedings of the ACM on Programming Languages* 4(POPL), Article 10, 2020: Theorem 5 (soundness), Section 5.1 and Theorem 6 (completeness for finitely supported predicates).
