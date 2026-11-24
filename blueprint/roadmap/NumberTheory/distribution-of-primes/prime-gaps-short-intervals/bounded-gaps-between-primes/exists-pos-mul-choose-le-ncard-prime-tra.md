# A positive proportion of $m$-subsets satisfy the prime $m$-tuples conjecture

For every natural number $m \ge 1$ there are $c > 0$ and $r_0$ such that for every set $A$ of $r \ge r_0$ distinct integers, at least $c \binom{r}{m}$ of the $m$-element subsets $B \subseteq A$ have infinitely many integers $n$ with $n + b$ prime for every $b \in B$ (Maynard (2015), Theorem 1.2). Primality of $n + b$ is that of the natural number $\max(n + b, 0)$, so negative values do not count as prime.

In this sense a positive proportion of admissible $m$-tuples satisfy the prime $m$-tuples conjecture.

Proof outline in the source: remove from $A$, for each prime $p \le k$, the least populated residue class modulo $p$; every $k$-subset of what remains is admissible, so contains an $m$-subset with infinitely many prime translates by the Maynard–Tao theorem in tuple form, and a double count gives $\gg_m r^m$ such $m$-subsets.

## Informally uses

- [Maynard–Tao theorem in tuple form](../smooth-gaps-between-primes/maynard-tao-admissible-tuples.md): applied to every $k$-subset of the thinned set.
- [Admissibility needs only the primes up to the size of the set](../../prime-patterns/hardy-littlewood-prime-tuples-conjecture/is-admissible-finset-iff-forall-prime-le.md): the thinned set's $k$-subsets miss a class modulo every $p \le k$, hence are admissible.

## Sources

- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
