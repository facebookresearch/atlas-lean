# Regret of HOO

Let $(P_{h,i})$ be a [tree of coverings](tree-of-coverings.md) of a measurable space $\mathcal X$, $\nu_1 > 0$ and
$0 < \rho < 1$, and let $\ell$ be a [dissimilarity](dissimilarity.md) on $\mathcal X$ such that the regions
[shrink geometrically](geometrically-shrinking-regions.md) with constants $\nu_1$, $\rho$ and some $\nu_2 > 0$. Let
$\nu$ be a Markov kernel from $\mathcal X$ to $[0, 1]$ whose mean-payoff function $f$ is
[weakly Lipschitz](weakly-lipschitz-function.md) with respect to $\ell$, and let $d$ be the
[$4\nu_1/\nu_2$-near-optimality dimension](near-optimality-dimension-through-packing-numbers.md) of $f$ with respect to
$\ell$, assumed defined: under these hypotheses the packing numbers it uses are defined (see the proof), and the
assumption is that $N(\mathcal X_{(4\nu_1/\nu_2)\varepsilon}, \ell, \varepsilon) \ge 1$ for every small enough
$\varepsilon > 0$. Then for every real $d' > d$ there is a constant $\gamma$ such that every run of
[HOO](hoo.md) with parameters $\nu_1$ and $\rho$ satisfies, for every $n \ge 2$,

$$
\mathbb E[R_n] \le \gamma \, n^{(d'+1)/(d'+2)} (\log n)^{1/(d'+2)},
$$

where $R_n$ is the [cumulative pseudo-regret](cumulative-pseudo-regret.md) and the powers are real powers. The constant
$\gamma$ depends on $d'$, on the parameters $\nu_1$, $\rho$, $\nu_2$, $\ell$ and the tree, and on $\nu$; it does not
depend on $n$, on the tie-breaking rule or on the choice of the points. If $d = \infty$ there is no such $d'$.

The source states the bound for $n \ge 1$; for $n = 1$ its right side is $0$, while
$\mathbb E[R_1] = f^* - \mathbb E[f(X_1)]$ can be positive, and the proof needs $\log n \ge \log 2$ to absorb the terms
that do not grow with $n$.

## Proof

For $h \ge 0$ let $\Delta_{h,i} = f^* - \sup_{P_{h,i}} f$, let $I_h$ be the set of nodes $(h, i)$ with
$\Delta_{h,i} \le 2\nu_1\rho^h$, and, for $h \ge 1$, let $J_h$ be the set of nodes of depth $h$ not in $I_h$ whose
parent is in $I_{h-1}$; so $\lvert J_h \rvert \le 2\lvert I_{h-1} \rvert$, as $J_h$ lies in the union over the nodes of
$I_{h-1}$ of their two children (the cardinality of a union of two finite sets, by induction on $I_{h-1}$).

1. *Size of $I_h$.* By the bound on [regions of small suboptimality](regions-of-small-suboptimality.md) with $c = 2$,
   $P_{h,i} \subseteq \mathcal X_{4\nu_1\rho^h}$ for $(h, i) \in I_h$, and the balls $B_{h,i}$ of these nodes are
   pairwise disjoint and contained in their regions, so
   $\lvert I_h \rvert \le N(\mathcal X_{4\nu_1\rho^h}, \ell, \nu_2\rho^h)$. Here every packing number
   $N(A, \ell, \varepsilon)$, $A \subseteq \mathcal X$, is defined: if $\nu_1\rho^g < \varepsilon$, two centers of
   disjoint balls of radius $\varepsilon$ cannot lie in one region of depth $g$ (the second would lie in the ball of the
   first), so there are at most $2^g$ of them. There is $C \ge 1$ with
   $N(\mathcal X_{(4\nu_1/\nu_2)\varepsilon}, \ell, \varepsilon) \le C\varepsilon^{-d'}$ for
   $0 < \varepsilon \le \nu_2$: for $\varepsilon \le \varepsilon_{d'}$ by the definition of $d$; for
   $\varepsilon_{d'} < \varepsilon \le \nu_2$ the count is at most $N(\mathcal X, \ell, \varepsilon_{d'})$. Hence
   $\lvert I_h \rvert \le C(\nu_2\rho^h)^{-d'}$ for every $h \ge 0$, with
   $C = \max\{1, N(\mathcal X, \ell, \varepsilon_{d'}) \nu_2^{d'}\}$.
2. *Splitting the regret.* Let $H \ge 1$. Every node is a descendant of a node of $I_H$, belongs to $I_h$ for some
   $h < H$, or is a descendant of a node of $J_h$ for some $1 \le h \le H$ (take the first ancestor outside the sets
   $I$). Each node is played at most once. Points played below a node of $I_H$ cost at most $4\nu_1\rho^H$ each, points
   played at a node of $I_h$ cost at most $4\nu_1\rho^h$, and points played below a node of $J_h$ cost at most
   $4\nu_1\rho^{h-1}$, as its parent is in $I_{h-1}$. A node of $J_h$ has $\Delta_{h,i} > 2\nu_1\rho^h$, so the bound on
   [plays below a suboptimal node](plays-below-a-suboptimal-node-by-hoo.md) gives
   $\mathbb E[T_{h,i}(n)] \le 8\log n/(\nu_1\rho^h)^2 + 4$. Hence

    $$
    \mathbb E[R_n] \le 4\nu_1\rho^H n + \sum_{h=0}^{H-1} 4\nu_1\rho^h \lvert I_h \rvert
      + \sum_{h=1}^{H} 4\nu_1\rho^{h-1} \cdot 2\lvert I_{h-1} \rvert
        \Big(\frac{8\log n}{\nu_1^2\rho^{2h}} + 4\Big).
    $$

3. *Choice of $H$.* With step 1 and $\rho^{h(1-d')} \le \rho^{-h(1+d')}$, the last two sums are at most
   $A \rho^{-H(1+d')}(1 + \log n)$ for a constant $A$, by summing geometric series of ratio $\rho^{-(1+d')} > 1$, and
   $1 + \log n \le (1 + 1/\log 2)\log n$ for $n \ge 2$; the sums over $h$ are bounded termwise, the constants factored
out of them, and the geometric sums computed by induction on $H$. Take $H \ge 1$ the smallest integer with
   $\rho^H \le (\log n / n)^{1/(d'+2)}$, which is less than $1$. Then
   $n\rho^H \le n^{(d'+1)/(d'+2)}(\log n)^{1/(d'+2)}$ and $\rho^{H-1} > (\log n/n)^{1/(d'+2)}$, so
   $\rho^{-H(1+d')}\log n \le \rho^{-(1+d')} n^{(d'+1)/(d'+2)} (\log n)^{1/(d'+2)}$.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 4.2, Theorem 6, and Appendix A.1, its proof,
  which the proof above follows; the argument that the packing numbers are defined is added.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.4.2, Theorem 3.9, which restates the bound for the loss of the point
  returned by (3.13).

## Depends on

- [Tree of coverings](tree-of-coverings.md)
- [Dissimilarity](dissimilarity.md)
- [Geometrically shrinking regions](geometrically-shrinking-regions.md)
- [Noisy evaluations](noisy-evaluations.md)
- [Weakly Lipschitz function](weakly-lipschitz-function.md)
- [Near-optimality dimension through packing numbers](near-optimality-dimension-through-packing-numbers.md)
- [Cumulative pseudo-regret](cumulative-pseudo-regret.md)
- [Hierarchical optimistic optimization (HOO)](hoo.md)
- [Real power of a real number](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)
- [Real logarithm](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-logarithm/log.md)

## Proof depends on

- [Regions of small suboptimality](regions-of-small-suboptimality.md)
- [Plays below a suboptimal node by HOO](plays-below-a-suboptimal-node-by-hoo.md)
- [Packing number](packing-number.md)
- [Counting through a map that is injective on a finite set](../../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card-le-card-of-inj-on.md)
- [Cardinality of a union of two finite sets](../../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card-union-le.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)
- [Last term of a sum over a range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-succ.md)
- [Termwise comparison of finite sums](../../../../../../Algebra/big-operators/inequalities-for-finite-sums-and-products-in-ord/sum-le-sum.md)
- [Multiplying a finite sum by a constant](../../../../../../Algebra/big-operators/finite-sums-and-products-in-rings/mul-sum.md)
- [Every nonempty set of natural numbers has a least element](../../../../../../Order/ordered-sets/well-ordering-naturals.md)
