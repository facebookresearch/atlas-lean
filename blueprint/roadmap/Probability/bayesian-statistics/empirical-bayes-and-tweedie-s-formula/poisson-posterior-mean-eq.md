# Robbins' formula

For every prior $g$ on the Poisson rate and every count $x \in \mathbb N$,

$$\mathbb E[\theta \mid x] = \frac{(x + 1)\, f(x + 1)}{f(x)},$$

where the left side is the Bayes [posterior mean](poisson-posterior-mean.md) and $f$ is the [marginal mass](poisson-mixture-mass.md). This is Efron (2021), equation (1.7), Robbins' (1956) derivation. Replacing $f(x)$ and $f(x + 1)$ by the observed proportions $y_x/N$ and $y_{x+1}/N$ of counts equal to $x$ and $x + 1$ gives Robbins' empirical Bayes estimate $(x + 1) y_{x+1}/y_x$ (Efron 2021, equation (1.3)), which needs no knowledge of the prior.

The identity holds for any measure $g$, with no moment assumption, because $\theta\, e^{-\theta}\theta^x/x! = (x + 1)\, e^{-\theta}\theta^{x+1}/(x + 1)!$ pointwise. It reads as a statement about $\mathbb E[\theta \mid x]$ when $g$ is a probability measure: then both integrals are finite, since $\theta\, e^{-\theta}\theta^x/x! \le x + 1$, and $f(x) > 0$ for every $x$ as soon as $g$ is not the point mass at $0$. For a measure with infinite mass both integrals may fail to converge; divergent integrals are read as $0$, both sides are then $0$, and the formula says nothing about a posterior mean.

## Background

- [Tweedie's formula](gaussian-posterior-mean-eq-add-mul-deriv.md): the Gaussian counterpart, which also writes the posterior mean through the marginal density.

## Sources

- Bradley Efron, *Empirical Bayes: concepts and methods*, author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf.
- Herbert Robbins, *An empirical Bayes approach to statistics*, Proc. Third Berkeley Symp. Math. Statist. Probab., Vol. 1, Univ. California Press (1956), 157–163 (cited from Efron 2021; not consulted).
