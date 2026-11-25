# Simulation-based calibration: conditional no-ties and randomized ranks

Let $(\widetilde\theta,Y)$ have the Bayesian joint probability law on
standard Borel spaces, and let $K_y$ be the posterior, a
[regular conditional law](../../../../Probability/foundations/regular-conditional-distributions/is-regular-conditional-distribution.md)
of $\widetilde\theta$ given $Y=y$. Fix integer $L\ge0$.
Conditional on $Y$, draw $\theta_1,\ldots,\theta_L$ independently from
$K_Y$, independently of $\widetilde\theta$ given $Y$.
For a measurable scalar $f$, assume **the posterior pushforward
$f_\#K_y$ is atomless for almost every $y$ under the data marginal**.
Then

$$R=\#\{1\le l\le L:f(\theta_l)<f(\widetilde\theta)\},\qquad
 \mathbb P(R=k\mid Y)=\frac1{L+1}\quad(0\le k\le L)$$

almost surely. In particular the unconditional rank is uniform.

Without any atomlessness assumption the same conclusion holds after
randomized tie breaking: draw independent Uniform$(0,1)$ keys
$U_0,\ldots,U_L$, independent of all parameter/data draws, and rank
$(f(\widetilde\theta),U_0)$ among the pairs $(f(\theta_l),U_l)$ in
lexicographic order.

## Depends on

- [Regular conditional distribution in kernel form](../../../../Probability/foundations/regular-conditional-distributions/is-regular-conditional-distribution.md)

## Background

- [Bayes' rule for discrete observations](posterior-eq-bayes-posterior.md)

## Expansion

Given $Y=y$, all $L+1$ parameter values have the same law $K_y$ and are
independent. In the no-ties case their scores are distinct almost surely.
Exchangeability makes each distinguished draw equally likely to occupy
each of the $L+1$ ranks, proving the conditional formula. Independent
continuous keys make the lexicographic pairs distinct and exchangeable
even when scores tie, proving the randomized version.

**Marginal atomlessness is not sufficient.** Let
$\widetilde\theta\sim\operatorname{Uniform}(0,1)$ and observe
$Y=\widetilde\theta$ without noise. The prior score $f(\theta)=\theta$
is atomless, but $K_Y=\delta_Y$, all exact posterior draws equal the truth,
and the strict rank is always zero for $L\ge1$. Constant $f$ is another
zero-rank example. Also, draws having the correct individual posterior
marginals need not suffice: repeating one continuous posterior draw twice
at $L=2$ yields only ranks zero and two. The independence/exchangeability
hypothesis cannot be replaced by unadjusted correlated MCMC output.

Uniform ranks are necessary under these hypotheses, not a converse test
of conditional correctness. A sampler that ignores $Y$ and returns fresh
independent prior draws gives iid scores jointly with the prior truth
before conditioning on $Y$, hence uniform unconditional ranks when the
prior score is atomless. It is still wrong for informative data, including
the noiseless example. This counterexample concerns a fixed
parameter-only score; richer data-dependent diagnostics are separate.

## Sources

- S. Talts et al., *Validating Bayesian inference algorithms with simulation-based calibration*, <https://arxiv.org/abs/1804.06788>, Section 4.1, Theorem 1 and Appendix B. The strict-rank theorem needs a conditional no-ties qualification; the randomized version and the explicit counterexamples are derived above.
