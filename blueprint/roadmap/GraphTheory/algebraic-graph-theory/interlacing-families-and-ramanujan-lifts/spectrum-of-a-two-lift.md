# Spectrum of a two-lift: old and new eigenvalues

For every graph $G$ and signing $s$, the adjacency spectrum of the $2$-lift $\hat G_s$ is the multiset union of the spectrum of $A$ (the *old* eigenvalues) and the spectrum of $A_s$ (the *new* eigenvalues).

## Proof sketch

In the basis $\{(v,0) + (v,1)\} \cup \{(v,0) - (v,1)\}$ the adjacency matrix of $\hat G_s$ is block diagonal: on symmetric vectors it acts as $A$ and on antisymmetric vectors as $A_s$, since a crossing edge flips the sign of the antisymmetric part.

## Depends on

- [Two-lifts and signings of a graph](two-lifts-and-signings-of-graphs.md)

## Sources

- Yonatan Bilu, Nathan Linial, "Lifts, discrepancy and nearly optimal spectral gap", Combinatorica 26(5) (2006).
