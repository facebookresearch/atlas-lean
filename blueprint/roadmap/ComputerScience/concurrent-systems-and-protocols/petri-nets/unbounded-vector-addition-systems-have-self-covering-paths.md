# Unbounded vector addition systems have self-covering paths

A finite sequence $w_1, \dots, w_m$ of vectors in $\mathbb{Z}^k$, $m > 1$, is *self-covering* if $w_j \le w_m$ and $w_j \ne w_m$ for some $j < m$, the order being placewise. For a [vector addition system](vector-addition-systems.md) $(v, A)$ of dimension $k$, the set $R(v, A)$ of reachable vectors is infinite if and only if $(v, A)$ has a self-covering path all of whose vectors lie in $\mathbb{N}^k$.

## Depends on

- [Vector addition systems](vector-addition-systems.md)

## Proof depends on

- [Kőnig's lemma for inverse systems](../../process-calculi/csp-semantic-models/konig-s-lemma-for-inverse-systems.md)

## Expansion

This page becomes ready once its remaining proof prerequisite is linked:

- Dickson's lemma: every infinite sequence of vectors in $\mathbb{N}^k$ has two terms $A_m \le A_n$ with $m < n$ (proof prerequisite of the forward direction, applied to an infinite path, given by Kőnig's lemma, in the tree of paths from $v$ in $\mathbb{N}^k$ with no repeated vector)

## Sources

- C. Rackoff, "The covering and boundedness problems for vector addition systems", *Theoretical Computer Science* 6:223–231, 1978, Section 4: Definition 4.1 (self-covering sequences) and Lemma 4.2, credited to R. M. Karp and R. E. Miller, "Parallel program schemata", *Journal of Computer and System Sciences* 3(2):147–195, 1969; a path is $k$-bounded when all its vectors lie in $\mathbb{N}^k$.
