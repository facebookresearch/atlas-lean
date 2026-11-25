# Crosscut theorem

Let $L$ be a finite lattice with least element $\hat 0$ and greatest element $\hat 1$, and let
$X \subseteq L$ satisfy (a) $\hat 1 \notin X$ and (b) every $s \ne \hat 1$ in $L$ lies below some
$t \in X$. Then

$$\mu(\hat 0, \hat 1) = \sum_k (-1)^k N_k,$$

where $N_k$ is the number of $k$-element subsets of $X$ whose meet is $\hat 0$ (the meet of the empty
subset is $\hat 1$). Typical choices of $X$ are the coatoms of $L$, or dually, for the dual
statement, the atoms.

## Informally uses

- [Möbius algebra product](../../../Combinatorics/partially-ordered-sets/m-bius-algebras-and-flag-vectors/moebius-algebra-mul.md):
  Stanley's proof expands $\prod_{t \in X} (\hat 1 - t)$ in the Möbius algebra $A(L, K)$ by
  Theorem 3.9.2.

## Sources

- R. P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Corollary 3.9.4.
