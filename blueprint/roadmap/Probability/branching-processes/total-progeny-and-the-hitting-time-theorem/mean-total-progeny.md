# Mean total progeny of a Galton–Watson process

For a finite measure $\nu$ on $\mathbb{N}$ (the offspring law), the mean total progeny of the
Galton–Watson process started from one individual is

$$\sum_{n \ge 0} E[Z_n] = \sum_{n \ge 0} \int z \, d\mathcal{L}_n(z) \in [0, \infty] ,$$

where $\mathcal{L}_n$ is the [law of the generation size](../galton-watson-process/law.md) $Z_n$.
By Tonelli's theorem this is $E\big[\sum_n Z_n\big]$ for any process with these generation laws.
