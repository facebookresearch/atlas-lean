# Secrecy with boundedly many nonces is DEXPTIME-complete

**Theorem (Durgin, Lincoln, Mitchell and Scedrov).** For [protocol theories in restricted form](protocol-theories-in-multiset-rewriting.md), with the bounds holding throughout the run, with no disequality tests, the secrecy problem
$S_{\mathrm{nonce}b}$, in which the number $n$ of protocol nonces and the fact size $k$ are given while the number of role instances is unbounded, is complete for
deterministic exponential time: it belongs to [EXP](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md) (DEXPTIME), and every decision problem in EXP reduces to it by a
polynomial-time many-one reduction.

## Depends on

- [Protocol theories in multiset rewriting](protocol-theories-in-multiset-rewriting.md)
- [The class EXP](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 5, Theorem 2, Proposition 5.2 (upper bound, Section 5.4.2) and Proposition 5.6 (lower bound, Section 5.5.3).
