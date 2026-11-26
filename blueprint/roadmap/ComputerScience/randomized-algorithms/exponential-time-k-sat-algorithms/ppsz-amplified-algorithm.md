# The PPSZ algorithm on the randomized word RAM

Let $k \ge 3$ and $h \ge 1$, let $\bar q_{k,h} = \int_0^1 Q_{k,h}(r)\,dr$ be the depth-$h$ critical-clause-tree estimate of the probability that a variable is forced (where $Q_{k,h}$ is the depth-$h$ iterate of the PPSZ survival recursion for $(k-1)$-ary critical-clause trees), and let $a, b$ be positive integers with $1 - \bar q_{k,h} \le a/b$. Let $s \ge \sum_{i < h}(k-1)^i$ and $c \in \mathbb{N}$.

There is a randomized word-RAM program that on input $(s, a, b, c, \varphi)$ runs up to $R = 2^{\lceil an/b \rceil} \cdot c$ independent PPSZ rounds with bound $s$, stops at the first satisfying assignment, halts on every run within $R \cdot \mathrm{poly}(n, L) \cdot |\varphi|^{O(s)}$ instructions, and on every satisfiable formula with clauses of at most $k$ literals outputs $0$ with probability at most $e^{-c}$; output $1$ is always accompanied by a satisfying assignment.

## Proof sketch

A PPSZ round succeeds with probability at least $2^{-(1 - \bar q_{k,h})n}$: with $s$ large enough to cover every critical-clause tree of depth $h$, each variable is $s$-implied with probability at least $\bar q_{k,h}$ (Hertli's argument removes the unique-solution assumption). Independent repetition gives the $e^{-c}$ bound.

## Depends on

- [The PPSZ round](ppsz-round.md)
- [Randomized word RAM](../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)
- [Multiword counters on the word RAM](../../sorting-and-searching/word-ram-integer-algorithms/multiword-counter.md)

## Proof depends on

- [Satisfiability coding lemma: PPZ round success probability](ppz-round-success-probability.md)
- [Multiword counters on the word RAM](../../sorting-and-searching/word-ram-integer-algorithms/multiword-counter.md)

## Sources

- R. Paturi, P. Pudlák, M. E. Saks and F. Zane, "An Improved Exponential-Time Algorithm for k-SAT", Journal of the ACM 52(3), 2005.
- T. Hertli, "3-SAT Faster and Simpler: Unique-SAT Bounds for PPSZ Hold in General", 52nd IEEE Symposium on Foundations of Computer Science (FOCS), 2011.
