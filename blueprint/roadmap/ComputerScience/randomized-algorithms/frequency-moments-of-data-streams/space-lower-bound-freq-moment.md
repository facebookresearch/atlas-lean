# Polynomial space for approximating $F_k$, $k \ge 6$

For every fixed integer $k > 5$ and every $0 < \gamma < 1/2$ there is $c > 0$ such that every
randomized streaming algorithm over $\{0, \dots, n - 1\}$ with $s$ bits of memory that, on every stream
of at most $n$ elements, outputs $Z$ with $|Z - F_k| > 0.1\,F_k$ with probability less than
$\gamma$ uses $s \ge c\, n^{1 - 5/k}$ bits.

The source's proof uses a multiparty version of disjointness (Proposition 3.3): among $s$ players,
distinguishing pairwise disjoint $t$-sets from sets with a unique common element costs
$\Omega(t/s^3)$ bits when $t \ge s^4$. It is proved by extending Razborov's distributional
argument.

The statement is in the [public-randomness model](streaming-algorithm.md), where the random seed is
not charged to the memory. This is harmless because Proposition 3.3 is proved against a fixed input
distribution. After amplifying the algorithm by independent copies (still an algorithm of this
model) and averaging its error over that distribution, one seed can be fixed. That yields a
deterministic state-passing protocol with small distributional error, to which the bound applies
whatever the size of the seed space.

## Background

- [Randomized communication complexity of disjointness](../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-disj-fn-ge.md): the two-party special case of the communication bound behind this theorem.
- [Frequency moment of a stream](freq-moment.md): the quantity being approximated; for $k \ge 1$ it agrees with the source's $F_k$.

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments", *J. Comput. System Sci.* 58 (1999) 137–147, Theorem 3.2 and Proposition 3.3.
