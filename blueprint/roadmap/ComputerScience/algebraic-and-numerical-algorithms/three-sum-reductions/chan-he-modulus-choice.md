# Choosing a hashing modulus with few heavy elements

For a finite set $S$ of integers and a modulus $M \ge 1$, let $\mathrm{coll}(S, M)$ be the number of ordered pairs of distinct elements of $S$ congruent modulo $M$, and call $s \in S$ **heavy** for $M$ if some other element of $S$ is congruent to $s$ modulo $M$. Let $Q$ be a set of primes, all at most $m$, with $|Q| \ge \sqrt{18 n}\,\Lambda$, where $\Lambda$ bounds the number of prime divisors in $Q$ of any nonzero difference of elements. Then exhaustive search finds primes $p, q \in Q$ such that for $M = pq$ each of three given sets $S$ of size at most $n$ has at most $9\Lambda^2 |S|^2/|Q|^2$ colliding pairs and at most $|S|^2/(2n)$ heavy elements.

## Proof sketch

Summing over $p \in Q$, each colliding pair of distinct integers is counted by at most $\Lambda$ primes, so some $p$ has at most $\Lambda |S|^2/|Q|$ collisions; repeating for $q$ among the residue classes mod $p$ squares the saving.

## Depends on

- [Distinct-position 3SUM](distinct-position-three-sum.md)

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
