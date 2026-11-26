# Protocol insecurity with finitely many sessions is NP-complete

**Theorem (Rusinowitch and Turuani).** For protocols with a fixed finite number of sessions, deciding whether there is an
[attack](protocol-insecurity-with-finitely-many-sessions.md), that is, whether the Dolev–Yao intruder can derive the secret, is
[NP-complete](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md). This holds with no bound on the size of messages and with composed, not only atomic, symmetric keys.

Membership in [NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md) follows because a normal attack substitutes for each variable a message whose DAG size is at most that of the protocol, so an attack can be
guessed and checked in polynomial time; hardness is by reduction from 3-SAT.

## Depends on

- [Protocol insecurity with finitely many sessions](protocol-insecurity-with-finitely-many-sessions.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Sources

- M. Rusinowitch and M. Turuani, "Protocol insecurity with a finite number of sessions, composed keys is NP-complete", *Theoretical Computer Science* 299(1–3), 2003; preprint of 12 March 2002 at <http://www-verimag.imag.fr/~ene/m2p/p4.pdf>: Section 3 (Theorem 1, Corollary 3 and Theorem 2) and Section 4 (Theorem 3).
