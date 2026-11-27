# Size-change termination is PSPACE-complete

Deciding whether a program, given with a safe size-change graph for each of its calls, is [size-change terminating](size-change-graphs.md) is PSPACE-complete. The closure set of the [closure characterization](closure-characterization-of-size-change-termination.md) can be exponentially large, so the algorithm that computes it explicitly takes exponential time.

## Expansion

This page becomes ready once these prerequisites are stated and checked:

- Membership in PSPACE and PSPACE-hardness, checked against the proofs in C. S. Lee, N. D. Jones and A. M. Ben-Amram, "The size-change principle for program termination", *POPL 2001* (source check)

## Depends on

- [Size-change graphs and size-change termination](size-change-graphs.md)
- [Polynomial space for decision problems](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Closure characterization of size-change termination](closure-characterization-of-size-change-termination.md)

## Sources

- P. M. Neergaard, *The Size-Change Principle of Termination*, lecture notes, Brandeis University, <https://www.cs.brandeis.edu/~cs117a/size-change-termination.pdf>, Section 5 (statement that testing size-change termination is PSPACE-complete, with the proof referred to Lee, Jones and Ben-Amram).
