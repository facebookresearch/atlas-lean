# Packing number

Let $\ell$ be a [dissimilarity](dissimilarity.md) on a set $\mathcal X$, let $A \subseteq \mathcal X$ and
$\varepsilon > 0$. When there is a largest integer $m \ge 0$ for which there are points $x_1, \dots, x_m \in \mathcal X$
whose balls $B(x_j, \varepsilon)$ are pairwise disjoint and contained in $A$, the *$\varepsilon$-packing number*
$N(A, \ell, \varepsilon)$ is that integer, the size of a largest packing of $A$ with disjoint open balls of radius
$\varepsilon$; otherwise it is not defined. Each ball contains its center, so the points are distinct and lie in $A$.

If $A \subseteq \mathcal X$, $0 < \varepsilon' \le \varepsilon$ and $N(\mathcal X, \ell, \varepsilon')$ is defined, then
$N(A, \ell, \varepsilon)$ is defined and at most $N(\mathcal X, \ell, \varepsilon')$: the balls
$B(x_j, \varepsilon') \subseteq B(x_j, \varepsilon)$ of a packing of $A$ form a packing of $\mathcal X$.

The source defines $N(\mathcal X, \ell, \varepsilon)$ as the largest number of disjoint open balls of radius
$\varepsilon$ contained in $\mathcal X$ and applies it to subsets $A$ of $\mathcal X$; "contained in $A$" is read as
$B(x_j, \varepsilon) \subseteq A$, as in the proof of its Theorem 6.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 4.2, Definition 4, and the second step of
  the proof of Theorem 6 (Appendix A.1).

## Depends on

- [Dissimilarity](dissimilarity.md)
