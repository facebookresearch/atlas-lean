# Two-level perfect hashing uses linear expected space

Store a static set $S$ of $n$ keys in a [two-level perfect hash table](../perfect-hashing/perfect-hashing.md), as follows.
1. Choose a primary function $h$ from a near-universal family into $m = n$ slots. Let $n_j$ be the number of keys with $h(x) = j$.
2. For each slot $j$, store its $n_j$ keys in a secondary table of size $2n_j^2$, using a function $h_j$ drawn from a near-universal family. If $h_j$ has a collision on these keys, redraw it.

**Theorem.**
1. For each slot, a random secondary function is collision-free with probability more than $1/2$. So the expected number of draws per slot is less than $2$, and once built, every lookup probes exactly one primary and one secondary cell. Lookups take worst-case $O(1)$ time.
2. $\mathbb{E}\bigl[\sum_j n_j^2\bigr] < 3n$. Hence the expected total size of the table is $O(n)$.

**Proof.**
1. With $n_j$ keys in a table of size $2n_j^2$, the expected number of colliding pairs is at most $\binom{n_j}{2} \cdot 2/(2n_j^2) < 1/2$. Markov's inequality bounds the probability of any collision by $1/2$.
2. $\sum_j n_j^2 = n + 2 \sum_{x < y} [h(x) = h(y)]$. Its expectation is at most $n + 2\binom{n}{2} \cdot 2/n = 3n - 2$.

## Depends on

- [Two-level perfect hash table](../perfect-hashing/perfect-hashing.md)
- [Universal hash family](../universal-hashing/is-universal.md)

## Background

- [Quadratic space bound under square sizing](../perfect-hashing/total-secondary-space-le-total-keys-sq.md)

## Sources

- J. Erickson, *Algorithms*, lecture notes, Lecture 5 "Hash Tables" (Spring 2017), University of Illinois, <https://jeffe.cs.illinois.edu/teaching/algorithms/notes/05-hashing.pdf>: Section 5.6 (with near-universal hashing, the expected number of collisions among $n$ items in $m$ slots is at most $n(n-1)/m$, so $m = 2n^2$ gives fewer than $1/2$), and Section 5.7 (the two-level table with secondary tables of size $2n_j^2$, Lemma 7: $\mathbb{E}[\sum_i n_i^2] < 3n$, linear expected size, and constant worst-case search time).
