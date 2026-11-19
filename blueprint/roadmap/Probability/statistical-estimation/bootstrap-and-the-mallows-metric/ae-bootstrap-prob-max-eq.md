# Bootstrap of the maximum for atomless data

Let $X_0, \dots, X_n$ be i.i.d. real random variables with a law $\nu$ that has no atoms, for instance the uniform law on $(0, \theta)$ of Bickel and Freedman's example. Almost surely the observations are distinct, so almost surely the [bootstrap probability that the maximum is reproduced](bootstrap-prob-max-eq.md) equals $1 - (1 - 1/(n+1))^{n+1}$.

## Informally uses

- [Bootstrap probability that the maximum is reproduced](bootstrap-prob-max-eq.md): the identity for distinct data.
- [Atomless i.i.d. scores are almost surely distinct](../../distributions/discrete/negative-binomial-and-beta-binomial-distribution/ae-injective-pi.md): almost sure distinctness of the observations.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Section 6, Counter-example 2.
