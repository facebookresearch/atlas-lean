# Protocol insecurity with finitely many sessions is NP-complete

**Theorem (Rusinowitch and Turuani).** For protocols with a fixed finite number of sessions, deciding whether there is an
[attack](protocol-insecurity-with-finitely-many-sessions.md), that is, whether the Dolev–Yao intruder can derive the secret, is
[NP-complete](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md). This holds with no bound on the size of messages and with composed, not only atomic, symmetric keys.

The input size is the DAG size $n$ of the protocol steps together with the intruder's initial knowledge $S_0$. Membership in
[NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md) rests on a small-witness bound: some attack substitutes for each variable a message of DAG size polynomial in $n$, so an attack
can be guessed and checked in polynomial time. The original proof of that bound for normal attacks has a gap; Liang and Verma identify it and prove a corrected
bound, so the membership argument is theirs. Hardness is by reduction from [3-SAT](../../../TheoryOfComputation/np-completeness/satisfiability/3-satisfiability/sat3-dec-np-hard.md).

## Depends on

- [Protocol insecurity with finitely many sessions](protocol-insecurity-with-finitely-many-sessions.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [3SAT is NP-hard](../../../TheoryOfComputation/np-completeness/satisfiability/3-satisfiability/sat3-dec-np-hard.md)

## Sources

- M. Rusinowitch and M. Turuani, "Protocol insecurity with a finite number of sessions, composed keys is NP-complete", *Theoretical Computer Science* 299(1–3), 2003; preprint of 12 March 2002 at <http://www-verimag.imag.fr/~ene/m2p/p4.pdf>: Section 3.1 (the input size: the DAG size of the protocol with the initial knowledge $S_0$), Section 3 (the NP procedure, Theorem 1, Corollary 3 and Theorem 2) and Section 4 (Theorem 3, NP-hardness by reduction from 3-SAT).
- Z. Liang and R. M. Verma, "Correcting and improving the NP proof for cryptographic protocol insecurity", *Information Systems Security (ICISS 2009)*, Lecture Notes in Computer Science, Springer, 2009, doi:10.1007/978-3-642-10772-6_9: the abstract and Section 1 (the error in the original proof that the substitution of a normal attack is polynomially bounded, and its correction).
