# Probability that a random permutation extends a partial assignment

Let $\alpha$ be a finite set with $N$ elements, let $x_1, \dots, x_k$ be distinct elements of $\alpha$ and $y_1, \dots, y_k$ arbitrary elements. The number of permutations $\pi$ of $\alpha$ with $\pi(x_i) = y_i$ for all $i$ is at most $N!/(N)_k$, where $(N)_k = N(N-1)\cdots(N-k+1)$ is the falling factorial, with equality when the $y_i$ are distinct. Hence a uniformly random permutation takes $k$ prescribed values at $k$ distinct points with probability at most $1/(N)_k$.

## Proof sketch

If the $y_i$ are distinct, the permutations extending the assignment correspond to permutations of the remaining $N-k$ elements, giving $(N-k)! = N!/(N)_k$; otherwise there are none.

## Depends on

- [Lazy random permutation](../lazy-sampling-and-the-prp-prf-switching-lemma/lazy-rp.md)

## Sources

- S. Chen and J. Steinberger, "Tight Security Bounds for Key-Alternating Ciphers", Advances in Cryptology, EUROCRYPT 2014, LNCS 8441, Springer, 2014, pp. 327-350 (the fraction of permutations of an $N$-element set extending a partial permutation with $k$ pairs is $(N-k)!/N!$).
