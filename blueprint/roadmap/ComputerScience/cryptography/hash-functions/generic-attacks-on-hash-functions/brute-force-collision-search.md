# Brute-force collision search

Let $f : M \to T$ take values in a finite set $D$, and let $m_1, \dots, m_s$ be distinct messages with $s > |D|$. Evaluating $f$ on all of them and returning two messages with equal digests finds a collision with probability $1$, using $s$ evaluations of $f$; every non-failing output is a collision. For $\ell$-bit digests, $2^\ell + 1$ distinct messages suffice.

## Proof sketch

Pigeonhole principle on the $s$ digests in a set of size less than $s$.

## Depends on

- [Collision resistance and target collision resistance](../collision-resistance-and-target-collision-resistance.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
