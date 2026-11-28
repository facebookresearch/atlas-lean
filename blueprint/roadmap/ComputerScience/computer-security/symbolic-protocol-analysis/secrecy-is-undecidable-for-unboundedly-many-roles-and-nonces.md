# Secrecy is undecidable for unboundedly many roles and nonces

**Theorem (Durgin, Lincoln, Mitchell and Scedrov).** For every fact size $k$ greater than some small constant, the secrecy problem $S_{\mathrm{size}=k}$ for
[restricted protocol theories](restricted-protocol-theories-and-secrecy-problems.md) is undecidable: given a protocol theory $T$ with the standard intruder and a secret $S$, it is undecidable
whether some run with any number of role instances and nonces, and facts of size at most $k$, reveals $S$. Undecidability holds even when data constructors,
message depth, message width, the number of distinct roles and role length are bounded.

The problem is recursively enumerable; the lower bound encodes derivability in Horn theories with existential quantification, which the proof shows undecidable
by encoding Turing-machine computations in such clauses (Lemma A.2, Appendix A.1); the source also credits a two-counter-machine reduction to earlier work.

## Depends on

- [Restricted protocol theories and their secrecy problems](restricted-protocol-theories-and-secrecy-problems.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 5, Theorem 1, Proposition 5.1 (upper bound, Section 5.4.1) and Proposition 5.5 (lower bound, Section 5.5.2, via the undecidability of existential Horn theories, Lemma A.2 and the Turing-machine encoding of Appendix A.1), and the summary in the introduction.
