# Expected counting measure of GEM and Poisson–Dirichlet masses

Let $\theta>0$ and let $P=(P_k)$ have GEM$(\theta)$ law, the
[order-of-appearance limit of a nested Ewens sample](ranked-ewens-frequencies-converge-to-pd-theta.md).
The same claims hold for its ranked PD$(\theta)$ sequence, since they
are unchanged by reordering. For every nonnegative measurable
$f:(0,1]\to[0,\infty]$,

$$\mathbb E\sum_k f(P_k)
 =\int_0^1 f(x)\,\theta x^{-1}(1-x)^{\theta-1}\,dx.$$

This is an equality of nonnegative extended quantities and allows
$+\infty$. For $0<a<b\le1$ the expected number of limiting masses
in $(a,b)$ is the finite integral of that density over $(a,b)$.
Taking $f(x)=x$ gives total mass one; taking $f=1$ gives an infinite
expected count. Signed functions require absolute integrability under
the displayed intensity measure.

## Depends on

- [GEM/PD limits and canonical definitions](ranked-ewens-frequencies-converge-to-pd-theta.md)

## Proof depends on

- [First-gene Beta frequency law](size-biased-allele-frequency-in-an-ewens-sample.md)
- [Exchangeability of the CRP](../../../Probability/bayesian-statistics/blackwell-macqueen-urn/crp-map-comap-perm.md)

## Expansion

For a finite exchangeable CRP sample and bounded continuous $g$ on
$[0,1]$, selecting a uniform customer gives
$\mathbb E\sum_k p^{(n)}_k g(p^{(n)}_k)
=\mathbb E g(J_n/n)$.
The established almost-sure $\ell^1$ convergence and uniform continuity
of $g$ allow passage to the limit; both sides are bounded by
$\|g\|_\infty$. Therefore the expected random probability measure
$\sum_kP_k\delta_{P_k}$ has the Beta$(1,\theta)$ law.
Continuous tests determine these finite Borel measures, so the identity
extends to all nonnegative measurable tests. Use $g(x)=f(x)/x$ on
$(0,1]$ and Tonelli to obtain the formula.

The same finite identity multiplied by a bounded continuous function of
the ranked frequencies, followed by the same limit argument, proves the
conditional size-bias statement. Thus the first mass is a size-biased pick
**conditional on the ranked or unordered masses**. It is not an additional
random pick given
the already ordered GEM sequence, whose first coordinate is fixed once
that full sequence is known. The finite-exchangeability argument above
avoids this conditioning ambiguity.
The convergence theorem is used, not restated as a new
result. No stationary diffusion or gamma-process representation is
required to prove this intensity identity.

## Sources

- N. Berestycki, *Recent progress in coalescent theory* (2009), <https://arxiv.org/abs/0909.3985>, Section 1.3.1, Theorem 1.5, for the CRP/GEM relationship and size-biased order. The intensity identity and integrability qualification are derived above.
- J. F. C. Kingman, *Random discrete distributions* (1975), <https://doi.org/10.1111/j.2517-6161.1975.tb01024.x>, bibliographic background only.
