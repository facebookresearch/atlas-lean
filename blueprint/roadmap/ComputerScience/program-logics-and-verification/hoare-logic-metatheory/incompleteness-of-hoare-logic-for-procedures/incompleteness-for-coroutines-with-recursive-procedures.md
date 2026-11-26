# Incompleteness for coroutines with recursive procedures

No Hoare axiom system is sound and complete in the sense of Cook for Clarke's language $L_{c,r}$, which has coroutines and parameterless recursive procedures that may be local to the coroutine routines. The proof follows that of [Clarke's incompleteness theorem](clarke-s-incompleteness-theorem.md): over a finite interpretation, a coroutine with two routines, each holding the activations of its own local recursive procedure, simulates a two-stack machine, so its halting problem is undecidable.

## Expansion

This page becomes ready once these prerequisites are stated:

- The coroutine language $L_{c,r}$ with its semantics (statement prerequisite)
- Undecidability of halting for two-stack machines and its simulation in $L_{c,r}$ over a finite interpretation (proof prerequisite)

## Depends on

- [Algol-like programs with procedure parameters](algol-like-programs-with-procedure-parameters.md)

## Related topics

- [Clarke's incompleteness theorem](clarke-s-incompleteness-theorem.md)

## Sources

- E. M. Clarke, "Programming language constructs for which it is impossible to obtain good Hoare axiom systems", *Journal of the ACM* 26(1):129–147, 1979, <http://www.cs.cmu.edu/afs/cs.cmu.edu/user/emc/www/papers/Papers%20In%20Refereed%20Journals/79_impossible_hoareaxiom.pdf>, Section 8, Theorem 8.1.
