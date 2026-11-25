# A defier model in which the Wald ratio is not the complier effect

With binary potential treatments, integrable potential outcomes, a binary instrument with both values having positive probability, independence of the potential treatments and outcomes from the instrument, exclusion, a nonzero first stage and monotonicity $D(1) \ge D(0)$, the Wald ratio equals the average effect among compliers. Without monotonicity this can fail. Take a binary instrument $Z$ with $P(Z = 1) = 1/2$ and, independently of $Z$, three types: compliers ($D(1) = 1, D(0) = 0$) with probability $1/2$ and $Y(1) = 1$; defiers ($D(1) = 0, D(0) = 1$) with probability $1/4$ and $Y(1) = -1$; never-takers ($D(1) = D(0) = 0$) with probability $1/4$; and $Y(0) = 0$ for every type, with observed $D = D(Z)$ and $Y = Y(D)$. Independence, exclusion and a nonzero first stage $E[D \mid Z=1] - E[D \mid Z=0] = 1/4$ hold, and $E[Y \mid Z = 1] - E[Y \mid Z = 0] = 1/2 + 1/4 = 3/4$, so the Wald ratio is $3$, while the complier effect is $1$.

## Background

- [Local average treatment effect theorem](wald-estimand-eq-late.md): the identity under monotonicity.

## Sources

- J. D. Angrist, "ExtrapoLATE-ing: external validity and overidentification in the LATE framework", lecture slides, LATE theorem of Imbens and Angrist (1994), <https://www.cedlas.econo.unlp.edu.ar/wp/wp-content/uploads/Angrist3.pdf>, slide "LATE Theorem: Imbens and Angrist (1994)"
