# Donsker–Varadhan variational formula

Relative entropy is the Legendre transform of the logarithmic moment generating functional: for probability measures $\mu$ and $\nu$, $\mathrm{KL}(\mu \,\|\, \nu) = \sup_f \left(\int f\,d\mu - \log \int e^f\,d\nu\right)$ over bounded measurable $f$. Dually, the Gibbs variational principle $\log \int e^f\,d\nu = \max_\mu \left(\int f\,d\mu - \mathrm{KL}(\mu \,\|\, \nu)\right)$ is attained at the tilted measure $e^f\nu / \int e^f\,d\nu$. The inequality half is the change-of-measure step behind PAC-Bayes bounds; the formula is the starting point of Sanov's theorem.

- [The clamped logarithm is bounded](abs-clamp-log-le.md)
- [Clamped logarithm](clamp-log.md)
- [Nonnegativity of the Donsker–Varadhan gain](clamp-log-gain-nonneg.md)
- [The Donsker–Varadhan supremum is infinite without absolute continuity](i-sup-eq-top-of-not-absolutely-continuou.md)
- [Integrability of bounded test functions](integrable-of-bounded.md)
- [Donsker–Varadhan inequality, integral form](integral-sub-log-integral-exp-le-integra.md)
- [Donsker–Varadhan inequality for bounded test functions](integral-sub-log-integral-exp-le-to-real.md)
- [Gibbs variational principle](is-greatest-integral-sub-kl-div.md)
- [Donsker–Varadhan variational formula](kl-div-eq-i-sup.md)
- [Donsker–Varadhan lower bound on the supremum](kl-div-le-i-sup-of-absolutely-continuous.md)
- [Measurability of the clamped logarithm](measurable-clamp-log.md)
- [Donsker–Varadhan inequality in extended nonnegative reals](of-real-integral-sub-log-integral-exp-le.md)
- [Convergence of the Donsker–Varadhan gain](tendsto-clamp-log-gain.md)
- [Relative entropy of a tilted measure](to-real-kl-div-tilted.md)

## Related topics

- [Large deviations](../../../Probability/large-deviations/README.md)
- [Data-processing inequality](../data-processing-inequality/README.md)
- [Total variation and Pinsker's inequality](../total-variation-and-pinsker-s-inequality/README.md)
- [PAC-Bayes bounds](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/pac-bayes-bounds/README.md)
- [Exponential families](../../../Probability/statistical-estimation/exponential-families/README.md): on a finite set with a uniform base measure the Gibbs variational principle is the variational representation of the log-partition function of an exponential family.
