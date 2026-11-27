# The bootstrap of the maximum has an atom of mass $1 - e^{-1}$ at $0$

The [bootstrap probability that the maximum is reproduced](bootstrap-prob-max-eq.md) satisfies

$$1 - \Bigl(1 - \frac{1}{n+1}\Bigr)^{n+1} \to 1 - e^{-1} \approx 0.63 .$$

So for a sample from the uniform law on $(0, \theta)$, the conditional law of the bootstrap pivot $n(X_{(n)} - X^*_{(n)})$ keeps an atom of mass about $0.63$ at $0$, while the pivot $n(\theta - X_{(n)})/\theta$ it is meant to imitate converges to the standard exponential law, which has no atom. Bickel and Freedman attribute the failure to the lack of uniformity of the convergence of $F_n$ to $F$ near the end point of the support, and note that the parametric bootstrap from the uniform law on $(0, X_{(n)})$ does work.

## Informally uses

- [Bootstrap probability that the maximum is reproduced](bootstrap-prob-max-eq.md): the exact probability for each $n$.

## Background

- [Bickel–Freedman bootstrap central limit theorem for the mean](bootstrap-mean-tendsto-gaussian-real.md): a case where the bootstrap is asymptotically valid.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Section 6, Counter-example 2.
