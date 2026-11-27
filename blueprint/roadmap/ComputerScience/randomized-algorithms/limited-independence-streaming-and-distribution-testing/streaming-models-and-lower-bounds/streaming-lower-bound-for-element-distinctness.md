# Streaming lower bound for element distinctness

Every randomized one-pass streaming algorithm that decides, with error at most $1/3$, whether all items of a stream of length at most $n$ over the universe $[n]$ are distinct uses $\Omega(n)$ bits of memory. The same holds for deciding whether the largest frequency is at least $2$ (the same problem), which strengthens the linear lower bound for approximating the largest frequency.

## Proof sketch

Encode Alice's set $x \subseteq [n]$ as a list of its elements and Bob's $y$ likewise; the concatenated stream has distinct items iff the sets are disjoint. Randomized disjointness needs $\Omega(n)$ bits even for sets of size $\lfloor n/4 \rfloor$ (Razborov), so the streams have length at most $n/2$. A distinctness algorithm thus gives a public-coin protocol for disjointness with $b + 1$ bits.

## Depends on

- [Randomized streaming algorithm with $s$ bits of memory](../../frequency-moments-of-data-streams/streaming-algorithm.md)

## Proof depends on

- [Streaming algorithms give one-way communication protocols](streaming-algorithms-give-one-way-protocols.md)
- [Randomized communication complexity of disjointness](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-disj-fn-ge.md)

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The Space Complexity of Approximating the Frequency Moments", Journal of Computer and System Sciences 58(1), 1999.
- B. Kalyanasundaram and G. Schnitger, "The Probabilistic Communication Complexity of Set Intersection", SIAM Journal on Discrete Mathematics 5(4), 1992.
- A. A. Razborov, "On the Distributional Complexity of Disjointness", Theoretical Computer Science 106(2), 1992.
