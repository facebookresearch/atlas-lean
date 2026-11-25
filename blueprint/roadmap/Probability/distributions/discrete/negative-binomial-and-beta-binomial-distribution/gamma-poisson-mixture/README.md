# Gamma–Poisson mixture (Greenwood–Yule)

For $a, b > 0$, the mixed Poisson law whose rate has the gamma law $\Gamma(a, b)$ with shape $a$ and rate $b$ (density $\frac{b^a}{\Gamma(a)} r^{a-1} e^{-br}$ on $[0, \infty)$) is the negative binomial law with size $a$ and mean $a/b$: for every $k \in \mathbb{N}$,

$$\int e^{-r} \frac{r^k}{k!} \, d\Gamma(a, b)(r) = \mathrm{NB}(k; a, a/b) = \frac{a^{(k)}}{k!} \Bigl(\frac{b}{b+1}\Bigr)^a \Bigl(\frac{1}{b+1}\Bigr)^k,$$

where $a^{(k)} = a(a+1) \cdots (a+k-1)$ is the rising factorial.

## Idea

This explains why the negative binomial law fits overdispersed counts: if each unit has its own Poisson rate and the rates vary across units like a gamma variable, the pooled counts are negative binomial. The proof is one integral. The gamma density times $e^{-r} r^k$ is again a gamma kernel, with shape $a + k$ and rate $b + 1$, so the integral is a ratio of gamma functions, $\Gamma(a+k)/\Gamma(a) = a^{(k)}$, times the stated powers. The same computation shows that the gamma laws are conjugate priors for the Poisson likelihood. Greenwood and Yule introduced the model in 1920 for repeated accidents and attacks of disease.

## Statements

- [Greenwood–Yule](poisson-mixture-real-gamma-measure.md)
- [Greenwood–Yule, mean form](poisson-mixture-real-gamma-measure-mean.md): mean parametrisation

## Background

- [Mixed Poisson distributions](../mixed-poisson/README.md)
- [Negative binomial distribution](../negative-binomial/README.md)

## Sources

- M. Greenwood and G. U. Yule, *An inquiry into the nature of frequency distributions representative of multiple happenings*, Journal of the Royal Statistical Society, 1920.
