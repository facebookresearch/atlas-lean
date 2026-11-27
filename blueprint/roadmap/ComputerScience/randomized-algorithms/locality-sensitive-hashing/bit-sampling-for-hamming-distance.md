# Bit sampling is locality sensitive for Hamming distance

For words $x, y$ of length $n$ over any alphabet, hashing by a uniformly random coordinate $i \mapsto x_i$ makes $x$ and $y$ collide with probability exactly $1 - d_H(x, y)/n$. Hence bit sampling is $(r_1, r_2, 1 - r_1/n, 1 - r_2/n)$-sensitive for the Hamming distance whenever $r_1 < r_2$.

## Proof sketch

The hashes collide exactly when the sampled coordinate is one of the $n - d_H(x,y)$ positions where the words agree.

## Depends on

- [Locality-sensitive hash families](locality-sensitive-hash-families.md)

## Sources

- P. Indyk and R. Motwani, "Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality", Proceedings of the 30th ACM Symposium on Theory of Computing, 1998.
- J. Leskovec, A. Rajaraman and J. D. Ullman, "Mining of Massive Datasets", Cambridge University Press, 2020.
