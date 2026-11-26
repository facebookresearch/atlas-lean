# CycleFold: delegating non-native scalar multiplications to a secondary folded instance

In folding-based IVC over a 2-cycle $(E_1,E_2)$, the only non-native operations of the primary augmented circuit are the scalar multiplications $\overline{W}_1+r\overline{W}_2$ and $\overline{E}_1+r\overline{T}+r^{2}\overline{E}_2$ in $E_1$. CycleFold replaces them by a minimal circuit over the other field that performs one such scalar multiplication and is itself expressed as a committed relaxed R1CS instance; these instances are folded into a separate running instance at each step. The primary circuit then only checks hashes and native field arithmetic, and soundness of the resulting IVC follows from knowledge soundness of both folding schemes.

## Proof sketch

Each step produces a secondary instance certifying one scalar multiplication; the primary circuit takes its public output as the claimed result and folds the secondary instance into a running secondary accumulator, whose final validity is checked by the decider. Extraction proceeds as for Nova on both chains simultaneously, using that each folded secondary instance certifies the group operation used by the primary step.

## Depends on

- [Two-cycles of elliptic curves for recursive arguments](cycle-of-curves.md)
- [Nova: IVC with constant recursion overhead from folding](nova-ivc.md)

## Proof depends on

- [Nova's folding scheme for committed relaxed R1CS](nova-folding-theorem.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "CycleFold: Folding-scheme-based Recursive Arguments over a Cycle of Elliptic Curves", IACR ePrint 2023/1192 (2023).
- Wilson Nguyen, Dan Boneh, Srinath Setty, "Revisiting the Nova Proof System on a Cycle of Curves", AFT (2023).
