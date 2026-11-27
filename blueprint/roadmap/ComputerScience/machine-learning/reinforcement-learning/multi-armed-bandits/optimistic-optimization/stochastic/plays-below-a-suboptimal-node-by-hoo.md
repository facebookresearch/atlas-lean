# Plays below a suboptimal node by HOO

Let $(P_{h,i})$ be a [tree of coverings](tree-of-coverings.md) of a measurable space $\mathcal X$ and $\ell$ a
[dissimilarity](dissimilarity.md) such that the regions [shrink geometrically](geometrically-shrinking-regions.md) with
constants $\nu_1$, $\rho$, $\nu_2$, and let the mean-payoff function $f$ of a Markov kernel from $\mathcal X$ to
$[0, 1]$ be [weakly Lipschitz](weakly-lipschitz-function.md) with respect to $\ell$, with $f^* = \sup_{\mathcal X} f$.
Consider a run of [HOO](hoo.md) with parameters $\nu_1$ and $\rho$, and let
$\Delta_{h,i} = f^* - \sup_{P_{h,i}} f$. For every node $(h, i)$ with $\Delta_{h,i} > \nu_1 \rho^h$ and every
$n \ge 1$, the expected number of rounds $t \le n$ in which HOO plays a descendant of $(h, i)$ satisfies

$$
\mathbb E[T_{h,i}(n)] \le \frac{8 \log n}{(\Delta_{h,i} - \nu_1 \rho^h)^2} + 4.
$$

## Proof

If $n = 1$ the bound holds as $T_{h,i}(1) \le 1$. Let $n \ge 2$. Fix a path $(0, 1) = (0, i^*_0), (1, i^*_1), \dots$ of
nodes with $\Delta_{s, i^*_s} = 0$, each a child of the previous one; it exists, since the region of a node is the union
of those of its children. Let $k < h$ be the largest depth with $(k, i^*_k)$ an ancestor of $(h, i)$; then
$(h, i)$ is not on the path.

*Concentration below a node.* For a node $(g, j)$ and $u \ge 1$, let $\tau_1 < \tau_2 < \dots$ be the rounds in which
HOO plays a descendant of $(g, j)$ ($\tau_m = \infty$ if there are fewer than $m$). Whether round $s$ is one of them is
determined by the past, as the node played is. Let $c_s$ be the indicator that round $s$ is one of
$\tau_1, \dots, \tau_u$ and $D_s = c_s (Y_s - f(X_s))$. Hoeffding's lemma in centred exponential form, applied to the
probability measure $\nu_{X_s}$, the conditional law of $Y_s$ given the past and $X_s$, and the reward $y \in [0, 1]$
(so $C = 1$ and $\int y \, d\nu_{X_s}(y) = f(X_s)$), with its real parameter equal to $-\lambda$, gives
$\mathbb E[e^{\lambda D_s} \mid H_{s-1}, X_s] \le e^{\lambda^2 c_s/8}$ for every real $\lambda$. By induction on the
rounds, $\mathbb E[\exp(\sum_{s \le t} (\lambda D_s - \lambda^2 c_s/8))] \le 1$; as $\sum_s c_s \le u$, Markov's
inequality with $\lambda = 4a/u$ gives, for $a \ge 0$ and $t \le n$,
$\mathbb P\big(\tau_u \le t, \ \sum_{m \le u} (Y_{\tau_m} - f(X_{\tau_m})) \ge a\big) \le e^{-2a^2/u}$, and the same
with $f(X_{\tau_m}) - Y_{\tau_m}$; this is the argument of the source (optional skipping and the Hoeffding–Azuma
inequality).

1. *Optimal nodes are rarely underestimated.* For $s \ge 0$ and $t \ge 1$,
   $\mathbb P(U_{s, i^*_s}(t) \le f^*) \le t^{-3}$. Indeed, $f(x) \ge f^* - \nu_1\rho^s$ on $P_{s, i^*_s}$ by the bound
   on [regions of small suboptimality](regions-of-small-suboptimality.md) with $c = 0$, so $U_{s,i^*_s}(t) \le f^*$ and
   $T_{s,i^*_s}(t) = u \ge 1$ imply that the rounds in which a descendant of $(s, i^*_s)$ is played have
   $\sum_{m \le u} (f(X_{\tau_m}) - Y_{\tau_m}) \ge (2u \log t)^{1/2}$. The concentration below $(s, i^*_s)$ with
   $a = (2u\log t)^{1/2}$, so that $e^{-2a^2/u} = t^{-4}$, summed over $1 \le u \le t$, gives $t \cdot t^{-4}$.
2. *Poor nodes are rarely overestimated once played often.* For $1 \le t \le n$ and an integer
   $u \ge 8\log n/(\Delta_{h,i} - \nu_1\rho^h)^2$,
   $\mathbb P(U_{h,i}(t) > f^* \text{ and } T_{h,i}(t) \ge u) \le t n^{-4}$. Indeed,
   $(2\log t/T_{h,i}(t))^{1/2} + \nu_1\rho^h \le (\Delta_{h,i} + \nu_1\rho^h)/2$ when $T_{h,i}(t) \ge u$, and every
   point played below $(h, i)$ lies in $P_{h,i}$, where $f \le f^* - \Delta_{h,i}$; so the event implies that the first
   $u' = T_{h,i}(t) \ge u$ rewards below $(h, i)$ exceed their means by at least $u'(\Delta_{h,i} - \nu_1\rho^h)/2$ in
   sum. The concentration below $(h, i)$ with $a = u'(\Delta_{h,i} - \nu_1\rho^h)/2$ bounds each of these events by
   $\exp(-u'(\Delta_{h,i} - \nu_1\rho^h)^2/2) \le n^{-4}$, as $u' \ge u$, and summing over $u \le u' \le t$ gives at
   most $t n^{-4}$.
3. *A play below $(h, i)$ needs one of these two events.* If round $t$ plays a descendant of $(h, i)$ and
   $T_{h,i}(t - 1) \ge 1$, the path of round $t$ passes through the child $(k + 1, i')$ of $(k, i^*_k)$ above $(h, i)$
   instead of $(k + 1, i^*_{k+1})$, and the B-values do not decrease along the path, so
   $B_{k+1, i^*_{k+1}}(t - 1) \le B_{h,i}(t - 1) \le U_{h,i}(t - 1)$. As
   $B_{s, i^*_s}(t-1) \le f^*$ implies $U_{s, i^*_s}(t - 1) \le f^*$ or $B_{s+1, i^*_{s+1}}(t - 1) \le f^*$, and the
   node $(t, i^*_t)$ is outside $\mathcal T_{t-1}$, either $U_{h,i}(t-1) > f^*$ or $U_{s, i^*_s}(t - 1) \le f^*$ for
   some $k + 1 \le s \le t - 1$.

Let $u$ be the least integer with $u \ge 8\log n/(\Delta_{h,i} - \nu_1\rho^h)^2$; then $u \ge 1$ and
$u \le 8\log n/(\Delta_{h,i} - \nu_1\rho^h)^2 + 1$. At most $u$ of the rounds playing below $(h, i)$
have $T_{h,i}(t - 1) < u$, so, by 3, 2 and 1 applied at time $t - 1 \ge u$,

$$
\mathbb E[T_{h,i}(n)] \le u + \sum_{t = u + 1}^{n} \Big((t - 1) n^{-4} + (t - 1)(t - 1)^{-3}\Big)
  \le \frac{8\log n}{(\Delta_{h,i} - \nu_1\rho^h)^2} + 1 + \frac{1}{n^2} + 2,
$$

using $\sum_{m=1}^{N} m^{-2} \le 2 - 1/N < 2$, by induction on $N$ (as $1/(N+1)^2 \le 1/N - 1/(N + 1)$). This is at
most the stated bound. The powers $1/2$ and $\rho^h$ are read as real powers.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Appendix A.1, Lemmas 14–17. The B- and U-values
  used to choose the node of round $t$ are those at the end of round $t - 1$; the lemmas write them at time $t$.

## Depends on

- [Tree of coverings](tree-of-coverings.md)
- [Dissimilarity](dissimilarity.md)
- [Geometrically shrinking regions](geometrically-shrinking-regions.md)
- [Weakly Lipschitz function](weakly-lipschitz-function.md)
- [Noisy evaluations](noisy-evaluations.md)
- [Hierarchical optimistic optimization (HOO)](hoo.md)
- [Real power of a real number](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)
- [Real logarithm](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-logarithm/log.md)

## Proof depends on

- [Regions of small suboptimality](regions-of-small-suboptimality.md)
- [Hoeffding's lemma in centred exponential form](../../../../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/pac-bayes-bounds/integral-exp-mul-sub-le.md)
- [Countable subadditivity of a measure](../../../../../../MeasureTheory/measures/measures-and-countable-additivity/measures/measure-i-union-le.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)
- [Sum over the empty range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-zero.md)
- [Last term of a sum over a range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-succ.md)
- [Termwise comparison of finite sums](../../../../../../Algebra/big-operators/inequalities-for-finite-sums-and-products-in-ord/sum-le-sum.md)
- [Every nonempty set of natural numbers has a least element](../../../../../../Order/ordered-sets/well-ordering-naturals.md)
