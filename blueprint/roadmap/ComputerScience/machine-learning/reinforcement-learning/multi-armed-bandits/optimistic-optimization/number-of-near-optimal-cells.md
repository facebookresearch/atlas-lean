# Number of near-optimal cells at a given depth

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](hierarchical-partition.md) of a set $\mathcal X$ with branching
factor $K$, let $\ell$ be a [semi-metric](semi-metric.md) on $\mathcal X$, and let
$f \colon \mathcal X \to \mathbb{R}$ attain its maximum $f^*$. Let $\delta \colon \mathbb{N} \to \mathbb{R}$ satisfy
$\delta(h) > 0$ and $\delta(h + 1) \le \delta(h)$ for every $h$, let the cells be [well shaped](well-shaped-cells.md)
for $\ell$ and $\delta$ with constant $\nu > 0$, and let $d \ge 0$ and $C > 0$ satisfy the
[$\nu$-near-optimality condition up to $\delta(0)$](near-optimality-dimension.md) for $f$. For $h \ge 0$ let

$$
I_h = \{i : 0 \le i \le K^h - 1, \ f(x_{h,i}) + \delta(h) \ge f^*\}.
$$

Then, for every $h \ge 0$,

$$
|I_h| \le C \delta(h)^{-d}.
$$

The nodes $(h, i)$ with $i \in I_h$ are those whose b-value $f(x_{h,i}) + \delta(h)$, as
[DOO](deterministic/doo.md) computes it, is at least $f^*$; the proof of the
[loss of DOO](deterministic/loss-of-doo.md) shows that DOO expands only such nodes.

## Proof

By induction on $h$, the cells of depth $h$ are pairwise disjoint: the cells of the children of a node are pairwise
disjoint subsets of its cell. Each cell contains its center, so the map $i \mapsto x_{h,i}$ is injective on the finite
set $I_h$; let $S$ be its image. For $i \in I_h$, $f(x_{h,i}) \ge f^* - \delta(h)$, so $S \subseteq \mathcal X_{\delta(h)}$,
and the balls $B_\ell(x_{h,i}, \nu \delta(h)) \subseteq X_{h,i}$, $i \in I_h$, are pairwise disjoint. As
$0 < \delta(h) \le \delta(0)$, the $\nu$-near-optimality condition with $\varepsilon = \delta(h)$ gives
$|S| \le C \delta(h)^{-d}$, and $|I_h| \le |S|$ as $i \mapsto x_{h,i}$ maps $I_h$ into $S$ and is injective on $I_h$.
Here $|I_h|$ is a natural number, compared as a real number with $C \delta(h)^{-d}$.

## Sources

- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.3.1, Lemma 3.1 and its proof.
- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Lemma 1.

## Depends on

- [Hierarchical partition](hierarchical-partition.md)
- [Semi-metric](semi-metric.md)
- [Well-shaped cells](well-shaped-cells.md)
- [Near-optimality dimension](near-optimality-dimension.md)
- [Cardinality of a finite set](../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card.md)
- [Real power of a real number](../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)

## Proof depends on

- [Counting through a map that is injective on a finite set](../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card-le-card-of-inj-on.md)
