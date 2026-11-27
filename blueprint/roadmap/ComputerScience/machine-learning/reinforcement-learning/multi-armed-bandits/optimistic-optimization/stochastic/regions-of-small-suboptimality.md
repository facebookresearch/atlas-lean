# Regions of small suboptimality

Let $(P_{h,i})$ be a [tree of coverings](tree-of-coverings.md) of $\mathcal X$ and $\ell$ a
[dissimilarity](dissimilarity.md) such that the regions [shrink geometrically](geometrically-shrinking-regions.md) with
constants $\nu_1$, $\rho$, $\nu_2$, and let the mean-payoff function $f$ of a Markov kernel from $\mathcal X$ to
$[0, 1]$ (see [noisy evaluations](noisy-evaluations.md)) be [weakly Lipschitz](weakly-lipschitz-function.md) with
respect to $\ell$, with $f^* = \sup_{\mathcal X} f$. The *suboptimality* of a node $(h, i)$ is
$\Delta_{h,i} = f^* - \sup_{P_{h,i}} f \ge 0$. If $\Delta_{h,i} \le c \nu_1 \rho^h$ for some $c \ge 0$, then

$$
f(y) \ge f^* - \max\{2c, c + 1\} \nu_1 \rho^h \quad \text{for every } y \in P_{h,i}.
$$

In particular ($c = 0$), $f(y) \ge f^* - \nu_1\rho^h$ on the region of a node with $\Delta_{h,i} = 0$, and ($c = 2$)
$f(y) \ge f^* - 4\nu_1\rho^h$ on the region of a node with $\Delta_{h,i} \le 2\nu_1\rho^h$. The powers $\rho^h$ are read
as real powers.

## Proof

The region is nonempty. Let $\eta > 0$ and choose $x \in P_{h,i}$ with $f(x) \ge \sup_{P_{h,i}} f - \eta$, so that $f^*
- f(x) \le \Delta_{h,i} + \eta$. For $y \in P_{h,i}$, $\ell(x, y) \le \operatorname{diam}(P_{h,i}) \le \nu_1 \rho^h$,
and the weak Lipschitz condition gives $f^* - f(y) \le \Delta_{h,i} + \eta + \max\{\Delta_{h,i} + \eta, \nu_1\rho^h\}
\le c\nu_1\rho^h + \eta + \max\{c\nu_1\rho^h + \eta, \nu_1\rho^h\}$. Letting $\eta \to 0$ gives the bound.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 4.1, Lemma 3.

## Depends on

- [Tree of coverings](tree-of-coverings.md)
- [Noisy evaluations](noisy-evaluations.md)
- [Dissimilarity](dissimilarity.md)
- [Geometrically shrinking regions](geometrically-shrinking-regions.md)
- [Weakly Lipschitz function](weakly-lipschitz-function.md)
- [Real power of a real number](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)
