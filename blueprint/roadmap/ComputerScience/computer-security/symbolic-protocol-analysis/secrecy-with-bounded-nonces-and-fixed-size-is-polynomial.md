# Secrecy with boundedly many nonces and fixed fact size is polynomial

**Theorem (Durgin, Lincoln, Mitchell and Scedrov).** For every fixed $k$, the secrecy problem $S_{\mathrm{nonce}b, \mathrm{size}=k}$ for
[restricted protocol theories](restricted-protocol-theories-and-secrecy-problems.md) without disequality tests, in which the number of nonces is given and the fact size
is fixed while the number of role instances is unbounded, is decidable in polynomial time: it is in [P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md).

## Depends on

- [Restricted protocol theories and their secrecy problems](restricted-protocol-theories-and-secrecy-problems.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 5, Theorem 4, and Section 5.4.4, Proposition 5.4 and its proof.
