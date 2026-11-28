# Moran-Yehudayoff: every class of finite VC dimension has a finite compression scheme

Let $C$ be a class of functions $X \to \{0,1\}$ on an arbitrary set $X$ with VC dimension $d$. Then $C$ has a sample compression scheme of size $2^{O(d)}$ (Moran and Yehudayoff, Theorem 1.3). If $d > 0$ and the dual class $C^*$ has VC dimension $d^* > 0$, then $C$ has a sample compression scheme of size $k \log k$ with $k = O(d^* \cdot d)$, where the size counts the side information as well as the kept examples (Theorem 1.4); Theorem 1.3 follows through Assouad's bound $d^* < 2^{d+1}$ (Claim 1.5). The reconstruction is a majority vote of the hypotheses that a proper learning map for $C$ produces on subsets of the compressed sample (Section 3).

## Proof sketch

By the PAC sample complexity bound there are $s = O(d)$ and a proper learning map that, for every distribution $q$ on the sample, is correct on $q$-probability at least $2/3$ from some subset of at most $s$ examples. The minimax theorem gives a distribution $p$ on the resulting hypotheses that is correct at every position with probability at least $2/3$, and the epsilon-approximation theorem applied to the dual class, of VC dimension $d^*$, gives $T = O(d^*)$ hypotheses whose majority vote is correct at every position (proof of Theorem 1.4 and Claim 3.1).

Derived (not stated in the cited source, which gives only $O(\cdot)$ bounds): under the ordered-list definition of a compression scheme, in which the order of the kept examples can carry the side information, $C$ has a scheme of size at most $(5184\, d^* + 1440)(120\, d + 60) = O(d^* d)$, and with $d^* \le 2^{d+1} - 1$ of size at most $(5184 \cdot 2^{d+1} + 1440)(120\,d + 60) = O(d\,2^d)$. Combined with the counting bound of compression schemes on the VC dimension, a binary class has a sample compression scheme of finite size if and only if it has finite VC dimension, and on a countable domain with measurable singletons finite-size compressibility is equivalent to each of the six conditions of the fundamental theorem of statistical learning.

## Depends on

- [Labelled sample compression scheme](labelled-sample-compression-scheme.md)
- [The VC dimension is at most the size of the ground set](../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)
- [Fundamental theorem of statistical learning (binary, 0-1 loss)](../../generalization-bounds-and-concentration/vc-and-natarajan-classes/fundamental-theorem-of-statistical-learning.md)

## Proof depends on

- [Moran-Yehudayoff weak learning on subsamples via the minimax theorem](weak-learning-on-subsamples.md)
- [Existence of epsilon-approximations for classes of finite VC dimension](../sample-complexity-and-combinatorial-dimensions/vc-sample-complexity-and-epsilon-nets/epsilon-approximations-of-vc-classes.md)
- [Assouad's dual VC dimension bound](../sample-complexity-and-combinatorial-dimensions/vc-sample-complexity-and-epsilon-nets/assouad-dual-vc-dimension-bound.md)
- [Sample compression schemes bound the VC dimension](compression-schemes-bound-vc-dimension.md)

## Sources

- S. Moran and A. Yehudayoff, "Sample Compression Schemes for VC Classes", Journal of the ACM, 2016, Theorems 1.3 and 1.4, Claim 1.5 and Section 3; open copy: <https://arxiv.org/abs/1503.06960>.
- N. Littlestone and M. K. Warmuth, "Relating Data Compression and Learnability", unpublished manuscript, 1986.
