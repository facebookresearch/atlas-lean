# Mallows metric of convolution powers, general $p$

For $1 \le p < \infty$, Borel probability measures $\mu, \nu$ on a separable normed abelian group and every $m \ge 0$,

$$d_p(\mu^{*m}, \nu^{*m}) \le m \, d_p(\mu, \nu),$$

where $\mu^{*m}$ is the law of the sum of $m$ independent variables with law $\mu$ ([convolution powers](conv-pow.md)). It is Lemma 8.6 of Bickel and Freedman for $m$ identically distributed pairs, by induction from the two-summand case. In a Hilbert space with $p = 2$ and equal means the factor $m$ improves to $\sqrt m$ ([Mallows metric of convolution powers](transport-cost-two-conv-pow-le.md)), which is what makes normalised sums contract.

## Informally uses

- [Mallows metric of sums of independent variables](wasserstein-conv-le.md): the induction step.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Lemma 8.6.
