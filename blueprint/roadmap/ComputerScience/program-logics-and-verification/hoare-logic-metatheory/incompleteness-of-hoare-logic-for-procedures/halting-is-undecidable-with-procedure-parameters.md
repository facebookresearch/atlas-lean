# Halting is undecidable with procedure parameters

For every finite interpretation $I$ whose domain has at least two elements, the halting problem is undecidable for programs of an [Algol-like language](algol-like-programs-with-procedure-parameters.md) with procedures as parameters of calls, recursion, static scope, global variables and internal procedures. This contrasts with flowchart and while schemes, which over a finite domain are finite-state machines and whose halting problem is therefore decidable. The proof simulates a queue machine, with instructions to enqueue the value of a variable, to dequeue into a variable and to branch on an equality: the queue is stored in the local variables of the successive activations of a recursive procedure, and static scope lets a procedure passed as a parameter return control to earlier activations.

## Expansion

This page becomes ready once these prerequisites are stated:

- Queue machines and the undecidability of their halting problem (proof prerequisite)

## Depends on

- [Algol-like programs with procedure parameters](algol-like-programs-with-procedure-parameters.md)

## Sources

- E. M. Clarke, "Programming language constructs for which it is impossible to obtain good Hoare axiom systems", *Journal of the ACM* 26(1):129–147, 1979, <http://www.cs.cmu.edu/afs/cs.cmu.edu/user/emc/www/papers/Papers%20In%20Refereed%20Journals/79_impossible_hoareaxiom.pdf>, Section 3, Lemma 3.1 and the simulation that follows it.
