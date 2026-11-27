# Moran-Yehudayoff: every class of finite VC dimension has a finite compression scheme

Let $C$ be a class of functions $X \to \{0,1\}$ on an arbitrary set $X$, all of whose finite shattered sets have at most $d$ points, and whose dual class shatters no finite family of more than $d^*$ concepts. Then $C$ has a sample compression scheme of size at most

$$
(5184\, d^* + 1440)(120\, d + 60) = O(d^* d),
$$

which reconstructs by a strict majority vote of a consistent learner over consecutive subsamples. Using Assouad's bound $d^* \le 2^{d+1} - 1$, $C$ has a scheme of size at most $(5184 \cdot 2^{d+1} + 1440)(120\,d + 60) = O(d\,2^d)$. Hence a binary class has a sample compression scheme of finite size if and only if it has finite VC dimension, and on a countable domain with measurable singletons finite-size compressibility is equivalent to each of the six conditions of the fundamental theorem of statistical learning.

## Proof sketch

By the subsample lemma at accuracy $1/3$ and confidence $1/2$ there is a distribution $\mu$ on subsamples of size $s = O(d)$ that is correct at every position with probability at least $2/3$. Apply the epsilon-approximation theorem to the dual class, of VC dimension at most $d^*$, under $\mu$: some $t = O(d^*)$ subsamples form a $1/6$-approximation, so their strict majority vote is correct at every position. The kept examples are the $t \cdot s$ examples of these subsamples. The converse is the counting bound, and the equivalences follow from the fundamental theorem.

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

- S. Moran and A. Yehudayoff, "Sample Compression Schemes for VC Classes", Journal of the ACM, 2016.
- N. Littlestone and M. K. Warmuth, "Relating Data Compression and Learnability", unpublished manuscript, 1986.
