# The PPSZ algorithm on the randomized word RAM

Let $k \ge 3$. Let $s_k$ be the probability that, in the infinite rooted $(k-1)$-ary tree with independent uniform labels $\pi_v \in [0, 1]$ in which every vertex $v$ with $\pi_v < \pi_{\mathrm{root}}$ is deleted, the root lies in an infinite connected component. Let $a, b$ be positive integers with $a/b > s_k$ and $a/b \ge p^* = (2 - \log_2 e)/2 \approx 0.279$, and let $c \in \mathbb{N}$. Then there is $s_0 = s_0(k, a, b)$ such that for every bound $s \ge s_0$ the following holds.

There is a randomized word-RAM program that on input $(s, a, b, c, \varphi)$ runs up to $R = 2^{\lceil an/b \rceil} \cdot c$ independent PPSZ rounds with bound $s$, stops at the first satisfying assignment, halts on every run within $R \cdot \mathrm{poly}(n, L) \cdot |\varphi|^{O(s)}$ instructions, and on every satisfiable formula with clauses of at most $k$ literals outputs $0$ with probability at most $e^{-c}$; output $1$ is always accompanied by a satisfying assignment.

## Proof sketch

The PPSZ round with bound $s$ is the random decoding procedure with the proof heuristic that sets a variable when some set of at most $s$ clauses implies its value. Against $k$-CNF formulas this heuristic has error at most $s_k + \varepsilon_{s,k}$ with $\varepsilon_{s,k} \to 0$ as $s \to \infty$; choose $s_0$ so that $s_k + \varepsilon_{s,k} \le a/b$ for all $s \ge s_0$. Since the error bound $a/b$ is at least $p^*$, Hertli's theorem gives that every round succeeds on a satisfiable $k$-CNF formula with probability at least $2^{-(a/b)n} \ge 2^{-\lceil an/b \rceil}$, without assuming a unique satisfying assignment. Then $R$ independent rounds all fail with probability at most $(1 - 2^{-\lceil an/b\rceil})^R \le e^{-c}$. Each round decides $s$-implication by exhaustive search over at most $|\varphi|^{O(s)}$ clause sets, and the round counter fits in multiword counters.

The following quantitative variant is not stated in the cited sources and is not claimed here: a bound $q$ on the probability that a variable is forced, computed from the depth-$h$ critical clause trees, together with the explicit threshold $s \ge \sum_{i < h}(k-1)^i$ for the bound. The sources state the error bound only for $s$ large enough.

## Depends on

- [The PPSZ round](ppsz-round.md)
- [Randomized word RAM](../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)
- [Multiword counters on the word RAM](../../sorting-and-searching/word-ram-integer-algorithms/multiword-counter.md)

## Proof depends on

- [Satisfiability coding lemma: PPZ round success probability](ppz-round-success-probability.md)
- [Bounded-width implication (s-implication)](bounded-width-implication.md)

## Sources

- D. Scheder and J. P. Steinberger, "PPSZ for General k-SAT: Making Hertli's Analysis Simpler and 3-SAT Faster", 32nd Computational Complexity Conference (CCC), LIPIcs 79, 2017, Section 1.1 (the heuristic $P_d$ and RandomDecode), Section 1.2, Definition 2 and Theorem 4, and Section 1.3, Theorem 6 (Hertli).
- R. Paturi, P. Pudlák, M. E. Saks and F. Zane, "An Improved Exponential-Time Algorithm for k-SAT", Journal of the ACM 52(3), 2005.
- T. Hertli, "3-SAT Faster and Simpler: Unique-SAT Bounds for PPSZ Hold in General", 52nd IEEE Symposium on Foundations of Computer Science (FOCS), 2011.
