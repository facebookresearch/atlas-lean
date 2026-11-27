# Classification calibration of convex margin surrogates

Let $\Phi : \mathbb{R} \to [0, \infty)$ be convex. For $\eta \in [0, 1]$ let
$C_\eta(\alpha) = \eta \Phi(\alpha) + (1 - \eta)\Phi(-\alpha)$, $H(\eta) = \inf_{\alpha \in \mathbb{R}} C_\eta(\alpha)$ and
$H^-(\eta) = \inf\{C_\eta(\alpha) : \alpha(2\eta - 1) \le 0\}$. Then $\Phi$ is classification-calibrated, that is,
$H^-(\eta) > H(\eta)$ for every $\eta \in [0, 1]$ with $\eta \ne 1/2$, if and only if $\Phi$ is differentiable at $0$
and $\Phi'(0) < 0$.

## Remarks

Both infima lie in $[0, \Phi(0)]$, since $\Phi \ge 0$ and $\alpha = 0$ is admissible in both, and the definition
does not ask $C_\eta$ to attain them. Bach states the equivalence for convex $\Phi : \mathbb{R} \to \mathbb{R}$
with classification calibration defined through minimizers, assumed to exist: for $\eta > 1/2$ every minimizer of
$C_\eta$ is positive, and for $\eta < 1/2$ every minimizer is negative. His proof compares the one-sided
derivatives of $C_\eta$ at $0$, $C_\eta'(0^+) = \eta \Phi'(0^+) - (1 - \eta)\Phi'(0^-)$ and
$C_\eta'(0^-) = \eta \Phi'(0^-) - (1 - \eta)\Phi'(0^+)$, with $0$.

## Related topics

- [Convex losses with negative slope at 0 are classification-calibrated](is-classification-calibrated-of-has-deri.md)
- [Classification-calibrated convex losses have negative slope at 0](differentiable-at-and-deriv-neg-of-is-cl.md)

## Sources

- P. L. Bartlett, M. I. Jordan and J. D. McAuliffe, *Convexity, classification, and risk bounds*, Journal of the American Statistical Association 101 (2006) 138–156; numbering of the technical report version <https://www.stat.berkeley.edu/~bartlett/papers/bjm-ccrb-05.pdf>, Definition 1 and Theorem 4, part 1.
- F. Bach, *Learning Theory from First Principles*, MIT Press, 2024; online version of May 26, 2025 <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 4.1.3, Definition 4.1 and Proposition 4.1.
