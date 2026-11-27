# Secrecy with boundedly many nonces: exponential-time upper and lower bounds

**Theorem (Durgin, Lincoln, Mitchell and Scedrov).** For [restricted protocol theories](restricted-protocol-theories-and-secrecy-problems.md) with no disequality tests, consider the secrecy
problem $S_{\mathrm{nonce}b}$, in which the number $n$ of protocol nonces and the fact size $k$ are given while the number of role instances is unbounded.

1. With $k$ given in unary, it belongs to [EXP](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md) (DEXPTIME): it is decided in time $O((\lVert T\rVert + \lVert \mathcal M\rVert + n)^k)$.
2. With $k$ given in binary, it is EXP-hard: every decision problem in EXP reduces to it by a
   [polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md), whose output instances have a
   fact-size bound $k$ exponential in the size of the original input.

The source states the two parts together as DEXPTIME-completeness; they hold for different encodings of $k$.

## Depends on

- [Restricted protocol theories and their secrecy problems](restricted-protocol-theories-and-secrecy-problems.md)
- [The class EXP](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 5, Theorem 2, Proposition 5.2 (upper bound, Section 5.4.2, with running time $O((\lVert T\rVert + \lVert \mathcal M\rVert + n)^k)$) and Proposition 5.6 (lower bound, Section 5.5.3) with the remark after it that the reduction needs fact sizes $k \ge k_w$ exponential in the input.
