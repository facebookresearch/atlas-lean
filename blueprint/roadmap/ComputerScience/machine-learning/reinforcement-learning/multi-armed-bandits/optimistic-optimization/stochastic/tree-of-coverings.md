# Tree of coverings

Let $(\mathcal X, \mathcal A)$ be a measurable space. A *tree of coverings* of $\mathcal X$ gives, for every depth
$h \ge 0$ and every index $i$ with $1 \le i \le 2^h$, a measurable set $P_{h,i} \subseteq \mathcal X$, the *region* of
the *node* $(h, i)$, such that

- $P_{0,1} = \mathcal X$;
- $P_{h,i} = P_{h+1, 2i-1} \cup P_{h+1, 2i}$ for every node $(h, i)$.

The nodes $(h + 1, 2i - 1)$ and $(h + 1, 2i)$ are the *children* of $(h, i)$, and the nodes form an infinite binary
tree with root $(0, 1)$. The *descendants* of a node are the node itself and the descendants of its children; the
region of every descendant of $(h, i)$ is contained in $P_{h,i}$, and, by induction on $h$, the $2^h$ regions of depth
$h$ cover $\mathcal X$. The regions need not be disjoint, and they may be empty;
[HOO](hoo.md) needs nonempty regions, which [geometrically shrinking regions](geometrically-shrinking-regions.md)
ensure. The source's condition (2) reads $P_{h,i} = P_{h+1, 2i-1} \cup P_{h, 2i}$, a misprint for the second child
$P_{h+1, 2i}$, which is the relation used here and in its analysis.

A [hierarchical partition](../hierarchical-partition.md) with branching factor $2$ gives a tree of coverings,
$P_{h,i+1} = X_{h,i}$ for $0 \le i \le 2^h - 1$, when its cells are measurable.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 3, conditions (1) and (2), and Section 4.1
  (trees of coverings whose regions at each depth are disjoint and nonempty, and Example 1).
