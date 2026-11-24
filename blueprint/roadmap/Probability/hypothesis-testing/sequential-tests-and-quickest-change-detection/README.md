# Sequential tests and quickest change detection

Observations $X_1, X_2, \dots$ arrive one at a time and the statistician decides after each one whether to stop. To test $P_0$ against $P_1$, two mutually absolutely continuous laws, with i.i.d. observations, Wald's sequential probability ratio test stops when the log-likelihood ratio $\Lambda_n$ leaves an interval $(a, b)$; Wald's inequalities bound its error probabilities by the boundaries, and the Wald–Wolfowitz theorem says that no test with error probabilities no larger than those of the SPRT has a smaller expected sample size under either hypothesis. In quickest change detection the law switches from $P_0$ to $P_1$ at an unknown time: with a geometric prior on the change point, Shiryaev's rule (stop when the posterior probability of a change exceeds a threshold) minimises the expected delay under a false-alarm constraint, and without a prior Page's CUSUM minimises Lorden's worst-case delay for a given mean time to false alarm (Moustakides 1986). Wald's inequalities follow from the likelihood-ratio change of measure on the first $n$ observations. All of these problems reduce to optimal stopping problems (Peskir and Shiryaev, *Optimal Stopping and Free-Boundary Problems*, 2006, Introduction (B) and Chapter VI, where the continuous-time Wiener and Poisson versions are solved).

## Observations and likelihood ratios

- [Filtration of the first $n$ observations](observation-filtration.md)
- [Cumulative log-likelihood ratio](llr-sum.md)
- [The cumulative log-likelihood ratio is adapted](adapted-llr-sum.md)
- [Density of a finite product of absolutely continuous laws](pi-eq-with-density-rn-deriv.md)
- [Likelihood-ratio change of measure on the first $n$ observations](infinite-pi-apply-eq-set-lintegral-prod.md)

## Wald's sequential probability ratio test

- [Wald's sequential probability ratio test](sprt-time.md)
- [The SPRT stopping time is a stopping time](is-stopping-time-sprt-time.md)
- [Event that the SPRT stops and accepts $P_1$](sprt-accept-one.md)
- [Event that the SPRT stops and accepts $P_0$](sprt-accept-zero.md)
- [Wald's inequality on the acceptance of the null hypothesis](sprt-accept-zero-le.md)
- [Wald's inequality on the acceptance of the alternative](sprt-accept-one-ge.md)
- [Wald–Wolfowitz theorem: optimality of the SPRT](sprt-wald-wolfowitz.md)

## Bayesian quickest detection

Shiryaev's formulation: a geometric prior on the change point, the false-alarm probability and the average detection delay.

- [Law of the observations with a change point](change-point-law.md)
- [Probability of false alarm under a geometric prior](false-alarm-prob.md)
- [Average detection delay under a geometric prior](average-detection-delay.md)
- [Shiryaev's posterior probability of a change](shiryaev-posterior.md)
- [Shiryaev's alarm time](shiryaev-time.md)
- [Shiryaev's theorem: Bayesian optimality of the Shiryaev rule](shiryaev-time-optimal.md)

## CUSUM and Lorden's criterion

- [Page's CUSUM statistic](page-cusum.md)
- [Closed form of the CUSUM statistic](page-cusum-eq-sup.md)
- [CUSUM alarm time](cusum-time.md)
- [Lorden's worst-case detection delay](lorden-delay.md)
- [Moustakides' theorem: optimality of CUSUM under Lorden's criterion](cusum-time-lorden-delay-le.md)

## Related topics

- [Optimal stopping and the Snell envelope](../../martingales/optimal-stopping-and-the-snell-envelope/README.md): the general theory to which the Bayesian formulations of sequential testing and change detection reduce.
- [Wald's equations](../../martingales/wald-s-equations/README.md): Wald's identity, which gives the average sample number of the SPRT.
- [Neyman–Pearson lemma](../neyman-pearson-dominated-two-simple.md): the fixed-sample-size counterpart of the SPRT, also based on the likelihood ratio.
- [Score, Wald and likelihood-ratio tests](../score-wald-and-likelihood-ratio-tests/README.md): fixed-sample likelihood-ratio tests.
