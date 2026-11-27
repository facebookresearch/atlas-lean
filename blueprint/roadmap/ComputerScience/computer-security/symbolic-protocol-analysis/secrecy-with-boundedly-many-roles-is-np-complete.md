# Secrecy with boundedly many role instances is NP-complete

**Theorem (Durgin, Lincoln, Mitchell and Scedrov).** For [restricted protocol theories](restricted-protocol-theories-and-secrecy-problems.md), the secrecy problem $S_{\mathrm{role}b}$, in which the
number $r$ of role instances and the fact size $k$ are given in unary while the number of nonces is unbounded, is [NP-complete](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md).

## Depends on

- [Restricted protocol theories and their secrecy problems](restricted-protocol-theories-and-secrecy-problems.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [3SAT is NP-hard](../../../TheoryOfComputation/np-completeness/satisfiability/3-satisfiability/sat3-dec-np-hard.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 5, Theorem 3, Proposition 5.3 (upper bound, Section 5.4.3, whose witness has at most $rR$ protocol steps and $B = krR$ relevant values, polynomial when $r$ and $k$ are given in unary) and Proposition 5.7 (lower bound, Section 5.5.4).
