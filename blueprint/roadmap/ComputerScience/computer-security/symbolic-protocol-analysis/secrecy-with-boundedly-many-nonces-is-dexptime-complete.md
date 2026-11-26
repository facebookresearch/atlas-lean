# Secrecy with boundedly many nonces is DEXPTIME-complete

**Theorem (Durgin, Lincoln, Mitchell and Scedrov).** For [protocol theories](protocol-theories-in-multiset-rewriting.md) with no disequality tests, the secrecy problem
$S_{\mathrm{nonce}b}$, in which the number $n$ of protocol nonces and the fact size $k$ are given while the number of role instances is unbounded, is complete for
deterministic exponential time (DEXPTIME).

## Expansion

This node states a precise result. A good expansion adds a page for the following prerequisite and links it under the dependency sections below:

- Statement prerequisite: the complexity class DEXPTIME and completeness for it under polynomial-time reductions.

## Depends on

- [Protocol theories in multiset rewriting](protocol-theories-in-multiset-rewriting.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 5, Theorem 2, Proposition 5.2 (upper bound, Section 5.4.2) and Proposition 5.6 (lower bound, Section 5.5.3).
