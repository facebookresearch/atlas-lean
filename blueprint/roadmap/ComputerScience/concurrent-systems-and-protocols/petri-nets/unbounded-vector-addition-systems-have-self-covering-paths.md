# Unbounded vector addition systems have self-covering paths

A finite sequence $w_1, \dots, w_m$ of vectors in $\mathbb{Z}^k$, $m > 1$, is *self-covering* if $w_j \le w_m$ and $w_j \ne w_m$ for some $j < m$, the order being placewise. For a [vector addition system](vector-addition-systems.md) $(v, A)$ of dimension $k$, the set $R(v, A)$ of reachable vectors is infinite if and only if $(v, A)$ has a self-covering path all of whose vectors lie in $\mathbb{N}^k$.

## Depends on

- [Vector addition systems](vector-addition-systems.md)

## Proof depends on

- [Kőnig's lemma for inverse systems](../../process-calculi/csp-semantic-models/konig-s-lemma-for-inverse-systems.md)
- [Dickson's lemma for finite products of well-quasi-orders](decision-procedures/dickson-s-lemma.md)

## Sources

- C. Rackoff, "The covering and boundedness problems for vector addition systems", *Theoretical Computer Science* 6:223–231, 1978, Section 4: Definition 4.1 (self-covering sequences) and Lemma 4.2, credited to R. M. Karp and R. E. Miller, "Parallel program schemata", *Journal of Computer and System Sciences* 3(2):147–195, 1969; a path is $k$-bounded when all its vectors lie in $\mathbb{N}^k$.
