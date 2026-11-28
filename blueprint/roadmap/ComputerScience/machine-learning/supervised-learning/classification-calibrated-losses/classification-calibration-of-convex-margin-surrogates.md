# Classification calibration of convex margin surrogates

A convex loss $\varphi : \mathbb{R} \to [0, \infty)$ is classification-calibrated if and only if it is differentiable at $0$ and $\varphi'(0) < 0$.

## Remarks

For $\eta \in [0, 1]$ let $C_\eta(\alpha) = \eta \varphi(\alpha) + (1 - \eta)\varphi(-\alpha)$, $H(\eta) = \inf_{\alpha \in \mathbb{R}} C_\eta(\alpha)$ and $H^-(\eta) = \inf\{C_\eta(\alpha) : \alpha(2\eta - 1) \le 0\}$. The loss $\varphi$ is [classification-calibrated](is-classification-calibrated.md) if $H^-(\eta) > H(\eta)$ for every $\eta \in [0, 1]$ with $\eta \ne 1/2$. Both infima lie in $[0, \varphi(0)]$, since $\varphi \ge 0$ and $\alpha = 0$ is admissible in both, and the definition does not ask $C_\eta$ to attain them.

Bach states the equivalence (his Proposition 4.1) for convex $\varphi : \mathbb{R} \to \mathbb{R}$ with classification calibration defined through minimizers by his (4.4) and (4.5), which he assumes to exist: for $\eta > 1/2$ every minimizer of $C_\eta$ is positive, and for $\eta < 1/2$ every minimizer is negative. His proof compares the one-sided derivatives of $C_\eta$ at $0$, $C_\eta'(0^+) = \eta \varphi'(0^+) - (1 - \eta)\varphi'(0^-)$ and $C_\eta'(0^-) = \eta \varphi'(0^-) - (1 - \eta)\varphi'(0^+)$, with $0$.

## Related topics

- [Convex losses with negative slope at 0 are classification-calibrated](is-classification-calibrated-of-has-deri.md)

## Sources

- P. L. Bartlett, M. I. Jordan and J. D. McAuliffe, *Convexity, classification, and risk bounds*, Journal of the American Statistical Association 101 (2006) 138–156; numbering of the technical report version of July 1, 2005, <https://www.stat.berkeley.edu/~bartlett/papers/bjm-ccrb-05.pdf>, Definition 1 and Theorem 4, part 1.
- F. Bach, *Learning Theory from First Principles*, MIT Press, 2024; online version of May 26, 2025, <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 4.1.3, pp. 77–78: Definition 4.1 (the conditional risks), (4.4) and (4.5) (classification calibration, with the minimizers assumed to exist) and Proposition 4.1.
