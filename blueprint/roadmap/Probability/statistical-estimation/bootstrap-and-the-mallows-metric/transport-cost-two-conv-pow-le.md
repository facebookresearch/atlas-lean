# Mallows metric of convolution powers

Let $\mu, \nu$ be probability measures with finite second moments and equal means on a separable real Hilbert space. For every $m \ge 0$,

$$d_2(\mu^{*m}, \nu^{*m})^2 \le m \, d_2(\mu, \nu)^2,$$

where $\mu^{*m}$ is the law of $Z_1 + \dots + Z_m$ for i.i.d. $Z_j \sim \mu$ ([convolution powers](conv-pow.md)). This is Lemma 8.7 of Bickel and Freedman for $m$ independent pairs, proved by induction on $m$.

## Informally uses

- [Mallows metric of sums in a Hilbert space](transport-cost-two-conv-le.md): the induction step, adding one more independent pair with equal means.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Lemma 8.7.
