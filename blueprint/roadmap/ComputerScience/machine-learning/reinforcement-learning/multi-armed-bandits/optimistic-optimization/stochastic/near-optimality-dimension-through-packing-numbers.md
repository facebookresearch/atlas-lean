# Near-optimality dimension through packing numbers

Let $\ell$ be a [dissimilarity](dissimilarity.md) on a measurable space $\mathcal X$ and $f$ the mean-payoff function of
a Markov kernel from $\mathcal X$ to $[0, 1]$ (see [noisy evaluations](noisy-evaluations.md)), with
$f^* = \sup_{\mathcal X} f$ and, for $\varepsilon > 0$,
$\mathcal X_\varepsilon = \{x \in \mathcal X : f(x) \ge f^* - \varepsilon\}$. Let $c > 0$, and assume that there is
$\varepsilon_1 \in (0, 1)$ such that, for every $\varepsilon$ with $0 < \varepsilon < \varepsilon_1$, the
[packing number](packing-number.md) $N(\mathcal X_{c\varepsilon}, \ell, \varepsilon)$ is defined and at least $1$. The
*$c$-near-optimality dimension* of $f$ with respect to $\ell$ is

$$
d = \max\Big\{0, \
  \limsup_{\varepsilon \to 0^+} \frac{\log N(\mathcal X_{c\varepsilon}, \ell, \varepsilon)}{\log(1/\varepsilon)}\Big\}
  \in [0, \infty],
$$

the lim sup of a nonnegative function of $\varepsilon \in (0, \varepsilon_1)$, which may be $+\infty$. The source
leaves the assumption on the packing numbers implicit; it makes the logarithms real.

If $d < \infty$, then for every real $d' > d$ there is $\varepsilon_{d'} \in (0, 1)$ such that
$N(\mathcal X_{c\varepsilon}, \ell, \varepsilon) \le \varepsilon^{-d'}$ for every
$0 < \varepsilon \le \varepsilon_{d'}$; this is the form in which the dimension is used.

This dimension differs from the [near-optimality dimension](../near-optimality-dimension.md) of the deterministic case:
it counts balls contained in $\mathcal X_{c\varepsilon}$ rather than centered in it, and it takes the growth rate of
that count instead of a pair $(d, C)$.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 4.2, Definition 5 and Example 3, and the
  second step of the proof of Theorem 6 (Appendix A.1).

## Depends on

- [Dissimilarity](dissimilarity.md)
- [Noisy evaluations](noisy-evaluations.md)
- [Packing number](packing-number.md)
- [Real logarithm](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-logarithm/log.md)
