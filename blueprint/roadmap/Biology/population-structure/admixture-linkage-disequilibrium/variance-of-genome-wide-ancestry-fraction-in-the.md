# Variance of a single-chromosome ancestry fraction

In the stationary [Poisson-relabeling model](poisson-switch-markov-model-of-local-ancestry-al.md),
let $T>0$, $0\le\alpha\le1$ and $L>0$ Morgans. The chromosome ancestry
fraction $X=L^{-1}\int_0^L I_x\,dx$ has

$$\mathbb E X=\alpha,\qquad
 \operatorname{Var}X=\alpha(1-\alpha)
 \frac{2(TL-1+e^{-TL})}{(TL)^2}.$$

The normalized factor tends to $1$ as $TL\to0$ and is asymptotic to
$2/(TL)$ as $TL\to\infty$. For $\alpha=0$ or $1$ the variance is zero
identically. This is a single-chromosome, fixed-ancestry-proportion
idealization, not total variance across pedigrees or genomes.

## Depends on

- [Stationary ancestry model and its covariance](poisson-switch-markov-model-of-local-ancestry-al.md)

## Expansion

The bounded, jointly measurable piecewise-constant process permits
Fubini. Integrating its covariance yields
$2\alpha(1-\alpha)L^{-2}\int_0^L(L-d)e^{-Td}\,dd$.
Evaluation gives the formula. Taylor expansion at zero gives the first
limit; division by $TL$ gives the large-exposure behavior. In particular
the normalized factor is in $(0,1]$, also seen by averaging a covariance
kernel bounded above by its value at zero.
Gravel distinguishes genealogical variance, assortment variance and
drift effects. Those additional sources of variation and correlations
between chromosomes are not represented by this fixed-$\alpha$ process.
The exposure convention in the model is not silently identified with a
calendar-generation count.

## Sources

- S. Gravel, *Population genetics models of local ancestry* (2012), <https://doi.org/10.1534/genetics.112.139808>, <https://arxiv.org/abs/1202.4811>, assortment-variance discussion and equation (8), pp. 15–16. The exact covariance integral above belongs to the specified Poisson-relabeling model, not to all terms of equation (8).
