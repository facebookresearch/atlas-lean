# Classification calibration of convex margin surrogates

Consider binary labels in $\{-1, +1\}$ and a convex loss $\Phi : \mathbb{R} \to [0, \infty)$. For $\eta \in [0,1]$ let
$C_\eta(\alpha) = \eta \Phi(\alpha) + (1-\eta)\Phi(-\alpha)$, $H(\eta) = \inf_{\alpha \in \mathbb{R}} C_\eta(\alpha)$ and
$H^-(\eta) = \inf\{C_\eta(\alpha) : \alpha(2\eta - 1) \le 0\}$; both lie in $[0, \Phi(0)]$. The loss $\Phi$ is
classification-calibrated if $H^-(\eta) > H(\eta)$ for every $\eta \ne 1/2$; no minimizers need exist. Then
$\Phi$ is classification-calibrated if and only if $\Phi$ is differentiable at $0$ and $\Phi'(0) < 0$ (Bartlett,
Jordan and McAuliffe, Theorem 4, part 1). The formulation that assumes conditional minimizers exist is a separate presentation.

## Depends on

- [The Bayes classifier is optimal](../bayes-classifier/is-bayes-estimator.md)

## Related topics

- [Convex losses with negative slope at 0 are classification-calibrated](is-classification-calibrated-of-has-deri.md)

## Sources

- Bartlett, Jordan, McAuliffe, "Convexity, Classification, and Risk Bounds" (J. Amer. Statist. Assoc. 101, 2006; Berkeley technical-report version) — Bartlett, Jordan, McAuliffe; JASA. <https://www.stat.berkeley.edu/~bartlett/papers/bjm-ccrb-05.pdf>
- Learning Theory from First Principles — Francis Bach (Inria/ENS), Sec 4.1.3, Proposition 4.1. <https://www.di.ens.fr/~fbach/ltfp_book.pdf>
