# The k-minimum-values sketch for distinct elements

Hash the items of a stream by a pairwise independent family $h : U \to [M]$ and keep the $t$ smallest distinct hash values seen. If $d \ge t$ distinct items have occurred and $v_t$ is the $t$-th smallest hash value, the estimate $\hat d = t M / v_t$ (and $\hat d$ equal to the number of stored values if fewer than $t$ are stored) satisfies $(1 - \varepsilon) d \le \hat d \le (1 + \varepsilon) d$ with probability at least $2/3$ when $t = \lceil c/\varepsilon^2 \rceil$ for a suitable constant $c$, $0 < \varepsilon < 1$, and $n^3 \le M \le n^{c'}$ for a universe of size $n \ge 2$ and a constant $c' \ge 3$ (so hash collisions among the $d \le n$ items are unlikely and each hash value takes $O(\log n)$ bits); for $0 < \delta \le 1/3$, the median of $O(\log(1/\delta))$ independent copies boosts the success probability to $1 - \delta$, with $O(\varepsilon^{-2}\log(1/\delta)\log n)$ bits of memory.

## Proof sketch

$\hat d > (1 + \varepsilon) d$ requires at least $t$ of the $d$ hash values to fall below $tM/((1+\varepsilon)d)$, an event whose count has mean about $t/(1 + \varepsilon)$ and variance at most the mean by pairwise independence; Chebyshev bounds its probability, and similarly for the lower tail.

## Depends on

- [Randomized streaming algorithm with $s$ bits of memory](../../frequency-moments-of-data-streams/streaming-algorithm.md)
- [Frequency moment of a stream](../../frequency-moments-of-data-streams/freq-moment.md)
- [k-wise independent hash family](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/word-ram-hash-families/k-wise-independent-hash-family.md)

## Proof depends on

- [Multiplicative Chernoff bounds for independent [0,1]-valued scores](../../../../Probability/concentration-inequalities/chernoff-and-bernoulli-comparison-bounds/multiplicative-chernoff-bounds.md)

## Sources

- Z. Bar-Yossef, T. S. Jayram, R. Kumar, D. Sivakumar and L. Trevisan, "Counting Distinct Elements in a Data Stream", RANDOM 2002, LNCS 2483, 2002.
- A. Chakrabarti, "Data Stream Algorithms: Lecture Notes", Dartmouth College, 2020.
