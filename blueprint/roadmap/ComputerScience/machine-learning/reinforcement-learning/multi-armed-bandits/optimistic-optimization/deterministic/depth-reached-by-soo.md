# Depth reached by SOO along an optimal branch

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](../hierarchical-partition.md) of a set $\mathcal X$ with
branching factor $K$, let $\ell$ be a [semi-metric](../semi-metric.md) on $\mathcal X$, let
$f \colon \mathcal X \to \mathbb{R}$ be [locally smooth around a maximizer](../local-smoothness-around-a-maximizer.md)
$x^*$ with respect to $\ell$, with maximum $f^* = f(x^*)$, and let $\delta$
[bound the diameters of the cells](../bounded-diameters.md). For $l \ge 0$ let
$I_l = \{i : 0 \le i \le K^l - 1, \ f(x_{l,i}) + \delta(l) \ge f^*\}$. Let $H \ge 1$ and $t \ge 1$ be integers, and
consider a run of [SOO](soo.md) with budget $n \ge t$ and the constant depth function equal to $H$. Let $h^*_t$ be the
largest depth of a node whose cell contains $x^*$ among the first $t$ nodes that the run expands (the first is the
root). Then, for every integer $h$ with $0 \le h \le H$,

$$
t \ge H \sum_{l=0}^{h} |I_l| \quad \text{implies} \quad h^*_t \ge h.
$$

The sources state this for any depth function, with $h_{\max}(t)$ in place of $H$. For a depth function that is not
constant along the run, that statement can fail, as can the loss bound deduced from it: see the example on the page of
the [loss of SOO](loss-of-soo.md). The proof below follows the monograph's, with the count of expansions per sweep made
exact; the depth function enters only through its constant value $H$.

## Proof

For every $l$, let $o_l$ be the node of depth $l$ whose cell contains $x^*$ (the cells of depth $l$ partition
$\mathcal X$). Local smoothness and the bound on the diameters give $f(x_{o_l}) \ge f^* - \ell(x_{o_l}, x^*) \ge
f^* - \delta(l)$, writing $x_{o_l}$ for the center of $o_l$, so $o_l$ lies in $I_l$.

Suppose $h^*_t < h \le H$; we show $t < H \sum_{l=0}^{h} |I_l|$. Number the sweeps $1, \dots, m$, the $t$-th expansion
taking place in sweep $m$. For $l \ge 0$ let $U_l = \{(l, i) : i \in I_l\}$, let
$U = U_0 \cup \dots \cup U_{h^*_t + 1}$ and $M = \sum_{l=0}^{h^*_t + 1} |I_l|$. As $(l, i) \mapsto i$ maps $U_l$
injectively into $I_l$, $|U_l| \le |I_l|$, and by induction on $k$, from $|A \cup B| \le |A| + |B|$ and the values of a
sum over $\{0, \dots, k\}$ for $k = 0$ and from $k$ to $k + 1$ (splitting off the last term),
$|U_0 \cup \dots \cup U_k| \le \sum_{l=0}^{k} |I_l|$; so $|U| \le M$. Also $M \ge |I_0| + |I_1| \ge 2$.

1. Sweep 1 expands only the root. Every later sweep expands at most $H$ nodes, at distinct depths among
   $1, \dots, H$: the root is no longer a leaf, and $h_{\mathrm{top}} \le H$.
2. Let $2 \le j \le m$ and let $g$ be the largest depth of an expanded node containing $x^*$ when sweep $j$ starts;
   $g \le h^*_t < H$. Then $o_{g+1}$ is a leaf of the tree, the tree has depth at least $g + 1$, and sweep $j$
   visits depth $g + 1$. Suppose that it does so before the $t$-th expansion has taken place, or with that expansion.
   When it does, $o_{g+1}$ is still a leaf, so the leaf $(g + 1, i)$ that the sweep chooses has
   $f(x_{g+1,i}) \ge f(x_{o_{g+1}}) \ge f^* - \delta(g + 1)$. Either it is expanded, and $i \in I_{g+1}$; or
   $v_{\max} > f(x_{g+1,i})$, and $v_{\max}$ is the value of a node $(l, i')$ expanded earlier in the sweep, at a
   depth $1 \le l \le g$, with $f(x_{l,i'}) \ge f^* - \delta(g + 1) \ge f^* - \delta(l)$ as $\delta$ is nonincreasing,
   so $i' \in I_l$. In both cases, among the first $t$ expansions, sweep $j$ expands a node of $U$ other than the root
   and $o_{h^*_t + 1}$, which is not expanded within the first $t$ expansions.
3. If $m = 1$, then $t = 1 \le (M - 1) H$. Let $m \ge 2$. Each sweep $2 \le j \le m - 1$ is over before the $t$-th
   expansion, so it expands such a node. These nodes, one for each such sweep, the root and $o_{h^*_t + 1}$ are pairwise
   distinct elements of $U$, as distinct sweeps expand distinct nodes; counting them through an injective map,
   $(m - 2) + 2 \le |U| \le M$. If sweep $m$ also expands such a node among the first $t$ expansions, then
   $m + 1 \le M$ in the same way, and $t \le 1 + (m - 1) H \le 1 + (M - 2) H \le (M - 1) H$. Otherwise, by 2, its
   expansions among the first $t$ all take place before it visits depth $g + 1$, at distinct depths among
   $1, \dots, g$ with $g \le h^*_t \le H - 1$, so $t \le 1 + (m - 2) H + H - 1 = (m - 1) H \le (M - 1) H$.

In all cases, as $H \ge 1$, $h^*_t + 1 \le h$ and the partial sums of the nonnegative numbers $|I_l|$ are
nondecreasing (splitting off the last term),

$$
t \le (M - 1) H < M H = H \sum_{l=0}^{h^*_t + 1} |I_l| \le H \sum_{l=0}^{h} |I_l|.
$$

## Sources

- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 4.1.1, Lemma 4.1 and its proof, a correction of the proof of the 2011
  paper.
- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Lemma 2.

## Depends on

- [Hierarchical partition](../hierarchical-partition.md)
- [Semi-metric](../semi-metric.md)
- [Local smoothness around a maximizer](../local-smoothness-around-a-maximizer.md)
- [Bounded diameters of the cells](../bounded-diameters.md)
- [Simultaneous optimistic optimization (SOO)](soo.md)
- [Cardinality of a finite set](../../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)

## Proof depends on

- [Counting through a map that is injective on a finite set](../../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card-le-card-of-inj-on.md)
- [Cardinality of a union of two finite sets](../../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card-union-le.md)
- [Sum over the empty range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-zero.md)
- [Last term of a sum over a range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-succ.md)
