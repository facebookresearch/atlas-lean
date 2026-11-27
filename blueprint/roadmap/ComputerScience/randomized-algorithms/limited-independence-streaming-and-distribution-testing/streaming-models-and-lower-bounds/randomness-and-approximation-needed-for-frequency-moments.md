# Both randomness and approximation are needed for F_k in sublinear space

For every integer $k \ge 2$: (1) every deterministic streaming algorithm that approximates $F_k$ within a factor $1 \pm 0.1$ on all streams of length $O(n)$ over a universe of size $O(n)$ uses $\Omega(n)$ bits; (2) every randomized streaming algorithm that computes $F_k$ exactly with error at most $1/3$ uses $\Omega(n)$ bits.

## Proof sketch

Use graph streams: for a word $a \in \Gamma^n$ list the pairs $(i, a_i)$. For two words, $F_k$ of the concatenation is $2^k \#\{i : a_i = b_i\} + 2\, d_H(a, b)$. (1) Take a code over a 16-letter alphabet with $2^{\Omega(n)}$ words pairwise disagreeing in at least half the positions; equal codewords give $F_k = 2^k n$ and distinct ones $F_k \le 2^{k-1} n + n$, which a $1 \pm 0.1$ approximation separates when $k \ge 2$, so distinct codewords must leave distinct memory states. (2) Since $2^k \ne 2$, exact $F_k$ determines the number of agreements; with $a_i = 1$ if $x_i = 1$ (else $0$) and $b_i = 1$ if $y_i = 1$ (else $2$) the words agree somewhere iff $x$ and $y$ intersect, so randomized disjointness gives $\Omega(n)$.

## Depends on

- [Randomized streaming algorithm with $s$ bits of memory](../../frequency-moments-of-data-streams/streaming-algorithm.md)
- [Frequency moment of a stream](../../frequency-moments-of-data-streams/freq-moment.md)

## Proof depends on

- [Streaming algorithms give one-way communication protocols](streaming-algorithms-give-one-way-protocols.md)
- [Randomized communication complexity of disjointness](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-disj-fn-ge.md)

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The Space Complexity of Approximating the Frequency Moments", Journal of Computer and System Sciences 58(1), 1999, Propositions 3.7 (deterministic, relative error $0.1$, via a family of $n/4$-sets with small pairwise intersections) and 3.8 (randomized exact computation, via disjointness).
