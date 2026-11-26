# No relativizing construction of key agreement from one-way permutations

Let $\pi$ be a uniformly random oracle consisting of a permutation $\pi_n$ of $\{0,1\}^n$ for every $n$; with probability one over $\pi$, it is one-way against every oracle algorithm making polynomially many queries. Impagliazzo and Rudich prove that if $\mathsf{P} = \mathsf{NP}$, then for every secret-key agreement protocol whose parties make polynomially many queries to $\pi$, there is an eavesdropper, efficient relative to $\pi$, that outputs the agreed key with probability close to the protocol's agreement probability. Relativizing to $\pi$ together with a $\mathsf{PSPACE}$-complete oracle, under which $\mathsf{P} = \mathsf{NP}$ holds while $\pi$ remains one-way, gives such an eavesdropper unconditionally; consequently no fully black-box (relativizing) construction bases secret-key agreement on one-way permutations.

## Depends on

- [Black-box constructions and oracle separations](black-box-constructions-and-oracle-separations.md)
- [One-way function families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Expansion

This page becomes ready once:

- The query bound and success probability of the eavesdropper must be read from the cited paper

## Sources

- R. Impagliazzo and S. Rudich, "Limits on the provable consequences of one-way permutations", *Proceedings of the 21st ACM STOC*, 1989
