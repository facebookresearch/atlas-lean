# Pseudorandom words reduced modulo m are pseudorandom residues

Let $X$ be an ensemble computationally indistinguishable from uniform $L(n)$-bit words, and let $m(n) \ge 1$ be computable in polynomial time from $1^n$ with $m(n)/2^{L(n)}$ negligible. Then the residue of $X_n$ (read as a binary number) modulo $m(n)$ is computationally indistinguishable from a uniform element of $\{0, \dots, m(n) - 1\}$. In particular this holds for the output of a secure pseudorandom generator.

## Proof sketch

A distinguisher for the residues composes with reduction modulo $m$ into a distinguisher for the words. Reducing a truly uniform $L$-bit word gives a residue within statistical distance $m/2^L$ of uniform, which is negligible.

## Depends on

- [Computational indistinguishability of distribution ensembles](../../security-games/computational-indistinguishability-of-ensembles/computational-indistinguishability-of-ensembles.md)
- [Asymptotic PRG security relative to a class of distinguishers](../pseudorandom-generators/prgsecure.md)

## Proof depends on

- [Sampling residues by reducing uniform bit strings](../../security-games/probabilistic-oracle-programs/sampling-residues-from-fair-bits.md)
- [Statistically indistinguishable ensembles are computationally indistinguishable](../../security-games/computational-indistinguishability-of-ensembles/statistical-implies-computational-indistinguishability.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
