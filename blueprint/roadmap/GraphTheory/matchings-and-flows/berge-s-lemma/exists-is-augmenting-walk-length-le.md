# A short augmenting path exists (Hopcroft–Karp, Corollary 2)

Let $M$ and $N$ be matchings of a simple graph $G$ on a finite vertex set with $r = |M| < |N|$. Then some [$M$-augmenting walk](is-augmenting-walk.md) has length at most $2 \lfloor r / (|N| - r) \rfloor + 1$.

Hopcroft and Karp state it with $|N| = s$ the maximum size of a matching; taking $N$ maximum recovers their statement, and their proof works for any larger matching $N$: the $|N| - r$ disjoint augmenting paths of Theorem 1 contain at most $r$ edges of $M$ altogether, so one of them contains at most $\lfloor r / (|N| - r) \rfloor$.

## Informally uses

- [Disjoint augmenting paths in a symmetric difference (Hopcroft–Karp, Theorem 1)](exists-disjoint-augmenting-walks.md)

## Sources

- J. E. Hopcroft and R. M. Karp, "An $n^{5/2}$ algorithm for maximum matchings in bipartite graphs", *SIAM Journal on Computing* 2(4) (1973), 225–231, §2. Corollary 2.
