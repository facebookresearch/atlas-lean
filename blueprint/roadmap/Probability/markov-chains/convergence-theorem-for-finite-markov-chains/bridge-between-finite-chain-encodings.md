# Bridge between finite-chain encodings

This node covers the equivalence of three encodings of a time-homogeneous Markov chain on a finite state space $S=\{0,\dots,M\}$ with the discrete $\sigma$-algebra:

- a [stochastic matrix](../kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md) $P$ on $S$, with its [underlying real matrix](to-matrix.md);
- a real $S\times S$ matrix with nonnegative entries and unit row sums;
- a Markov kernel $\kappa$ on $S$, with $\kappa(i,\{j\})=P(i,j)$.

The maps between them are mutually inverse: the underlying matrix of the stochastic matrix built from a row-stochastic matrix is that matrix, and the kernel of $P$ determines $P$ through its values on singletons. Powers correspond: the [underlying matrix of $P^n$ is the $n$-th matrix power](to-matrix-pow.md), and the $n$-fold composite kernel satisfies $\kappa^n(i,\{j\})=(P^n)_{ij}$ for all $n\ge0$ and $i,j\in S$. Under these identifications, [ergodicity is primitivity](is-ergodic-iff-is-primitive.md) of the underlying matrix.

## Depends on

- [Underlying matrix of a stochastic matrix](to-matrix.md)
- [Underlying matrix of a stochastic matrix power](to-matrix-pow.md)
- [Ergodicity is primitivity of the transition matrix](is-ergodic-iff-is-primitive.md)

## Expansion

An expansion states as pages of their own:

- the round trip between stochastic matrices and nonnegative matrices with unit row sums;
- the correspondence between stochastic matrices and Markov kernels on the discrete finite space, with kernel composition corresponding to matrix multiplication, by induction giving $\kappa^n(i,\{j\})=(P^n)_{ij}$;
- the transfer of ergodicity and primitivity across the three encodings.

Prerequisites:

- [Underlying matrix of a stochastic matrix power](to-matrix-pow.md)

## Sources

- J. R. Norris, *Markov Chains*, Cambridge University Press (1997), <https://www.statslab.cam.ac.uk/~jrn10//Markov/> (matrix form of chains).
