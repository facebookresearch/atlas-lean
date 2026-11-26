# Reaction–diffusion model of a gene drive with demographic feedback

Let $n_D(t, x)$ and $n_O(t, x)$ be the densities of drive and wild-type individuals on $x \in \mathbb{R}$, with fitness cost $s \in (0, 1)$ of the drive, constant death rate $1$ and wild-type per-capita birth rate $r(1 - n) + 1$, where $n = n_D + n_O$ and $r > 0$ is the wild-type intrinsic growth rate. The model is

$$\partial_t n_D - \Delta n_D = n_D \Bigl[(1 - s)\Bigl(1 + \frac{n_O}{n_D + n_O}\Bigr)\bigl(r(1 - n_D - n_O) + 1\bigr) - 1\Bigr],$$

$$\partial_t n_O - \Delta n_O = n_O \Bigl[\frac{n_O}{n_D + n_O}\bigl(r(1 - n_D - n_O) + 1\bigr) - 1\Bigr].$$

In the drive frequency $p = n_D / n$ and total density $n$ it reads

$$\partial_t p - \Delta p - 2 \nabla \log n \cdot \nabla p = \bigl(r(1 - n) + 1\bigr)\, s\, p (1 - p) \Bigl(p - \frac{2s - 1}{s}\Bigr),$$

$$\partial_t n - \Delta n = n \Bigl[\bigl(1 - s + s(1 - p)^2\bigr)\bigl(r(1 - n) + 1\bigr) - 1\Bigr].$$

At $p = 1$ the population declines to $\max\{0, 1 - s / (r(1 - s))\}$, so the drive eradicates the population when $r < s / (1 - s)$; the frequency dynamics are bistable with threshold $(2s - 1)/s$ when $s > 1/2$.

## Depends on

None; this page states the reaction-diffusion model directly.

## Expansion

The total per-capita birth factor is $p(1-s)(2 - p) + (1-p)^2 = 1 - s + s(1-p)^2$, which gives the equation for $n$; the equation for $p$ follows from the quotient rule, the gradient term coming from diffusion of the ratio $n_D / n$. The density feedback multiplies the selection term by $r(1 - n) + 1$, which drops as the drive suppresses the population.

## Sources

- L. Girardin and F. Débarre, *Demographic feedbacks can hamper the spatial spread of a gene drive*, J. Math. Biol. 83 (2021). <https://doi.org/10.1007/s00285-021-01702-2> Section 1.6, Systems (9) and (10).
