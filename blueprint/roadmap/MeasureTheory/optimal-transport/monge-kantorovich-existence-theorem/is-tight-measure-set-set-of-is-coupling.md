# Tightness of transference plans

Let $X$ and $Y$ be Polish spaces and $\mu, \nu$ Borel probability measures on them. The set of
couplings of $\mu$ and $\nu$ is tight: given $\varepsilon > 0$, choose compact sets $K_1 \subseteq X$ and
$K_2 \subseteq Y$ with $\mu(X \setminus K_1) \le \varepsilon / 2$ and $\nu(Y \setminus K_2) \le \varepsilon / 2$; then
every coupling $\pi$ satisfies $\pi((X \times Y) \setminus (K_1 \times K_2)) \le \varepsilon$.

Villani's Lemma 4.4 allows tight sets of marginals; here the marginals are the single measures $\mu$
and $\nu$, which are tight because $X$ and $Y$ are Polish.

## Background

- [Tightness of probability measures](../../../Probability/convergence-of-measures/tightness-of-probability-measures/README.md):
  the notion of tightness used here, and Prokhorov's theorem, which turns tightness into relative
  compactness.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Lemma 4.4.
