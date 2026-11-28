# Homogeneous continuous learning with errors (hCLWE)

The homogeneous CLWE distribution has density proportional to $\rho(y)\sum_k\rho_\beta(k-\gamma\langle y,w\rangle)$: the CLWE density sliced at label $z=0$. It is a mixture of parallel Gaussian 'pancakes' along the hidden direction $w$, and hCLWE asks to tell it from the standard Gaussian.

With the notation of the CLWE page, fix a unit vector $w\in\mathbb{R}^n$ and $\beta,\gamma>0$. The **homogeneous CLWE distribution** $H_{w,\beta,\gamma}$ on $\mathbb{R}^n$ has density proportional to

$$
\rho(y)\sum_{k\in\mathbb{Z}}\rho_\beta\bigl(k-\gamma\langle y,w\rangle\bigr),
$$

which is the density of $A_{w,\beta,\gamma}$ restricted to $z=0$ and renormalised (the conditional law given $z=0$ defined through the density, $z=0$ being a null event). Completing squares gives the mixture form

$$
\sum_{k\in\mathbb{Z}}\rho_{\sqrt{\beta^2+\gamma^2}}(k)\cdot\rho(\pi_{w^\perp}(y))\cdot\rho_{\beta/\sqrt{\beta^2+\gamma^2}}\Bigl(\langle y,w\rangle-\frac{\gamma}{\beta^2+\gamma^2}k\Bigr),
$$

with $\pi_{w^\perp}$ the projection orthogonal to $w$: Gaussian components of width $\beta/\sqrt{\beta^2+\gamma^2}$ along $w$ and width $1$ orthogonally, with centres spaced $\gamma/(\beta^2+\gamma^2)$ apart along $w$. For $\beta\ll\gamma$ the width is about $\beta/\gamma$ and the spacing about $1/\gamma$.

**Decision hCLWE.** $\mathrm{hCLWE}_{\beta,\gamma}$ is the problem of distinguishing independent samples of $H_{w,\beta,\gamma}$, for one uniformly random unit vector $w$ fixed for all samples, from independent samples of $D_{\mathbb{R}^n}$.

## Expansion

The mixture form follows from $\rho(y)\rho_\beta(k-\gamma\langle y,w\rangle)=\rho(\pi_{w^\perp}(y))\rho(t)\rho_\beta(k-\gamma t)$ with $t=\langle y,w\rangle$, and completing the square in $t$. Bruna, Regev, Song and Tang also compute the normalising constant of the density.

## Depends on

- [Continuous learning with errors (CLWE)](continuous-lwe.md)

## Proof depends on

None.

## Sources

- Joan Bruna, Oded Regev, Min Jae Song, Yi Tang, "Continuous LWE", ACM STOC 2021; numbers from arXiv:2005.09595v2, Section 2.3: Definitions 2.19 and 2.21 and Equations (1)–(3).
