# Continuous learning with errors (CLWE)

CLWE samples are Gaussian points $y\in\mathbb{R}^n$ labelled by $z=\gamma\langle y,w\rangle+e \bmod 1$, for a hidden unit vector $w$ fixed across samples and independent Gaussian noise $e$ of width $\beta$. Decision CLWE asks to tell them from Gaussian points with independent uniform labels.

Let $\rho_s(x)=\exp(-\pi\|x/s\|^2)$, $\rho=\rho_1$, and let $D_{\mathbb{R}^n}$ be the distribution on $\mathbb{R}^n$ with density $\rho(y)$ (the Gaussian of covariance $\frac1{2\pi}I_n$), $D_{\mathbb{R},\beta}$ the one-dimensional distribution with density $\rho_\beta(x)/\beta$. Fix a unit vector $w\in\mathbb{R}^n$ and $\beta,\gamma>0$.

The **CLWE distribution** $A_{w,\beta,\gamma}$ on $\mathbb{R}^n\times[0,1)$ is the law of $(y,z)$ with $y\sim D_{\mathbb{R}^n}$, $e\sim D_{\mathbb{R},\beta}$ independent of $y$, and $z=(\gamma\langle y,w\rangle+e)\bmod1$; its density at $(y,z)$ is proportional to

$$
\rho(y)\sum_{k\in\mathbb{Z}}\rho_\beta\bigl(z+k-\gamma\langle y,w\rangle\bigr).
$$

**Decision CLWE.** $\mathrm{CLWE}_{\beta,\gamma}$ is the average-case problem of distinguishing independent samples of $A_{w,\beta,\gamma}$, for one uniformly random unit vector $w$ fixed for all samples, from independent samples of $D_{\mathbb{R}^n}\times U([0,1))$.

The worst-case decision problem (distinguish for every fixed $w$) reduces in polynomial time to the average-case one by applying one uniformly random rotation to all samples, since $D_{\mathbb{R}^n}$ is rotation invariant.

## Expansion

The random-rotation reduction maps $(y,z)$ to $(Ry,z)$; then $Ry\sim D_{\mathbb{R}^n}$ and $\langle Ry,Rw\rangle=\langle y,w\rangle$, while $Rw$ is uniform on the sphere and the null distribution is unchanged. CLWE is the continuous analogue of LWE: $y$ plays the role of $a$, $\gamma w$ of $s/q$, and arithmetic modulo $1$ replaces arithmetic modulo $q$. Gupte, Vafa and Vaikuntanathan allow other secret distributions on the sphere and other sample distributions. The homogeneous variant is a separate page.

## Depends on

None.

## Proof depends on

None.

## Sources

- Joan Bruna, Oded Regev, Min Jae Song, Yi Tang, "Continuous LWE", ACM STOC 2021; numbers from arXiv:2005.09595v2, Section 2.3: Definitions 2.18 and 2.20 and Claim 2.22.
- Aparna Gupte, Neekon Vafa, Vinod Vaikuntanathan, "Continuous LWE is as Hard as LWE & Applications to Learning Gaussian Mixtures", IEEE FOCS 2022; numbers from arXiv:2204.02550v3, Section 3, Definition 6.
