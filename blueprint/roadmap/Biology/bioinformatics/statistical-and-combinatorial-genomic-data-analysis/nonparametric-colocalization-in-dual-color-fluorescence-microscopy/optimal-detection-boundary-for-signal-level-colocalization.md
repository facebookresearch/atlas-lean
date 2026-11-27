# Optimal detection boundary for signal-level colocalization

Let $(X_i,Y_i)$, $i = 1,\dots,n$, be i.i.d. pixel intensity pairs from a joint distribution $F$ with marginals $F_X, F_Y$. **No colocalization** is $H_0: F(x,y) = F_X(x)F_Y(y)$ for all $x,y$. **Colocalization** is $H_1$: there exist signal thresholds $\eta_X,\eta_Y$ such that the conditional law $F_{\eta_X,\eta_Y}$ of $(X,Y)$ given $X>\eta_X$, $Y>\eta_Y$ is positively quadrant dependent, i.e. $F_{\eta_X,\eta_Y}(x,y)\ge F_{\eta_X}(x)F_{\eta_Y}(y)$ for all $x,y$, with strict inequality somewhere.

For independent copies $(X,Y), (\tilde X,\tilde Y)\sim F$ define the conditional Kendall concordance

$$T(\eta_X,\eta_Y) = \mathbb{P}\{(X-\tilde X)(Y-\tilde Y)>0\mid \cdot\} - \mathbb{P}\{(X-\tilde X)(Y-\tilde Y)<0\mid\cdot\},$$

conditioning on $X,\tilde X>\eta_X$ and $Y,\tilde Y>\eta_Y$, and the signal mass $V(\eta_X,\eta_Y) = 1 + F(\eta_X,\eta_Y) - F_X(\eta_X) - F_Y(\eta_Y) = \mathbb{P}(X>\eta_X, Y>\eta_Y)$. Under $H_0$, $T\equiv0$; under $H_1$, $\sup T>0$.

**Theorem.** Let $\Delta$ reject $H_0$ when the [maximal thresholded Kendall tau statistic](maximal-thresholded-kendall-tau-colocalization-statistic.md) $\tau^*$ exceeds its null $(1-\alpha)$-quantile.

1. *(Consistency.)* If $\displaystyle\sup_{\eta_X,\eta_Y} V(\eta_X,\eta_Y)\,T^2(\eta_X,\eta_Y) \gg \frac{\log\log n}{n}$, then $\Delta$ rejects $H_0$ with probability tending to one.
2. *(Optimality.)* There is a constant $c>0$ such that every level-$\alpha$ test has an alternative $F$ with $\sup V\,T^2\ge c\,\frac{\log\log n}{n}$ under which it accepts $H_0$ with probability tending to $1-\alpha$.

So the detection boundary for signal-level colocalization is of order $\log\log n/n$ in the product of signal mass and squared concordance, and $\tau^*$ (and its geometric-grid approximation $\tau^*_{\rm app}$) attains it.

## Depends on

- [Maximal thresholded Kendall tau colocalization statistic](maximal-thresholded-kendall-tau-colocalization-statistic.md)

## Proof sketch

At the right thresholds roughly $nV$ pixels are in the signal region, and the standardized Kendall tau there is about $\sqrt{nV}\,T$ up to a constant, so detection needs $nVT^2$ to dominate the null maximum of the scanned statistic. Under $H_0$ that maximum is $O_P(\sqrt{\log\log n})$. The proof splits the threshold pairs by expected signal count $n(1-t)(1-s)$: pairs with at most order $\log\log n$ expected points cannot produce a large standardized value; for pairs with more than $\log^2 n$ expected points a nearly geometric grid of thresholds captures the maximum; and the intermediate range is handled with weighted empirical-process bounds of law-of-the-iterated-logarithm type for the marginal and joint tail counts. This gives the consistency half. A matching construction of weak positive dependence at an unknown signal threshold shows that no level-$\alpha$ test detects below $c\log\log n/n$.

## Sources

- Shulei Wang, Ellen T. Arena, Kevin W. Eliceiri and Ming Yuan, "Automated and Robust Quantification of Colocalization in Dual-Color Fluorescence Microscopy: A Nonparametric Statistical Approach", *IEEE Transactions on Image Processing* 27 (2018), 622–636, <https://doi.org/10.1109/tip.2017.2763821>. Preprint version: arXiv:1710.00965 (2017), Section 3, Theorem 1 (proof via Lemmas 1–2 in the appendix), <https://doi.org/10.48550/arXiv.1710.00965>.
