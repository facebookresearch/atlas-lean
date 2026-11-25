# Post-processing by a Markov kernel

If $M$ is $(\varepsilon, \delta)$-differentially private and $\kappa$ is a Markov kernel from $\Omega$
to $\Omega'$ (a randomized map applied to the output, using no access to the database), then
$x \mapsto \int \kappa(\omega, \cdot) \, dM(x)(\omega)$ is $(\varepsilon, \delta)$-differentially
private. A data analyst who only sees the output cannot increase the privacy loss.

Dwork and Roth prove the deterministic case and write a randomized map as a convex combination of
deterministic ones. The proof here instead integrates the event bound: for a measurable
$g : \Omega \to [0, 1]$, the layer-cake formula $\int g \, d\mu = \int_0^1 \mu\{g > t\} \, dt$ turns
$\mu\{g > t\} \le e^{\varepsilon} \nu\{g > t\} + \delta$ into
$\int g \, d\mu \le e^{\varepsilon} \int g \, d\nu + \delta$, applied to $g = \kappa(\cdot, S)$.

## Informally uses

- [Post-processing by a measurable map](map.md): the deterministic case, from which the source's proof obtains the randomized one by averaging.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Proposition 2.1.
