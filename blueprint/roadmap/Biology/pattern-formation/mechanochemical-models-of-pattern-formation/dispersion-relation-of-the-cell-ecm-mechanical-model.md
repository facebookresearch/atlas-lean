# Dispersion relation of the cell–ECM mechanical model

In the [cell–ECM mechanical model](cell-ecm-mechanical-model-with-viscoelastic-matrix.md), every non-trivial homogeneous steady state has $\bar n\equiv1$, $\bar u\equiv0$ and arbitrary $\bar\rho\equiv\rho_0>0$. Put $\lambda_1=1/(1+\lambda)$ and $\lambda_2=(1-\lambda)/(1+\lambda)^2$.

**Homogeneous perturbations.** Perturbations proportional to $e^{\psi t}$ with $\psi\ne0$ satisfy $\psi(\psi+r)(a_2\psi^2+a_1\psi+a_0)=0$, so every root has negative real part: the steady state $(1,\rho_0,0)$ is stable to spatially homogeneous perturbations for every constitutive law in the family.

**Inhomogeneous perturbations.** Perturbations proportional to $e^{\psi t+ikx}$ with $\psi\ne0$, $k\ne0$ satisfy

$$\psi\bigl[c_3(k^2)\psi^3+c_2(k^2)\psi^2+c_1(k^2)\psi+c_0(k^2)\bigr]=0,$$

where

$$c_3=a_2\tau\lambda_1\beta k^4+\bigl[b_2-a_2\tau(\lambda_1+\lambda_2\rho_0)\bigr]k^2+a_2s\rho_0,$$

$$c_0=a_0\tau\lambda_1D\beta k^6+\bigl[b_0D-a_0\tau(\lambda_2\rho_0\alpha+D\lambda_1-r\lambda_1\beta)\bigr]k^4+\bigl[b_0r+a_0(Ds\rho_0-r\tau\lambda_1)\bigr]k^2+a_0rs\rho_0,$$

and $c_2$, $c_1$ are the analogous polynomials in $k^2$ obtained with $(a_2,a_1,b_2,b_1)$ and $(a_1,a_0,b_1,b_0)$ (see the source for the full expressions). Patterns require $\operatorname{Re}\psi(k^2)>0$ for some $k^2>0$, hence at least one $c_j(k^2)<0$ for some $k^2>0$. If $\tau=0$ all four coefficients are nonnegative for every $k^2$, so **positive cell traction $\tau>0$ is necessary for pattern formation**. In particular:

- if $c_2=c_3=0$, then $\psi(k^2)=-c_0(k^2)/c_1(k^2)$, which is positive exactly when $c_0$ and $c_1$ have opposite signs;
- if only $c_3=0$, then $\psi=\bigl(-c_1\pm\sqrt{c_1^2-4c_2c_0}\bigr)/(2c_2)$, and $\operatorname{Re}\psi>0$ holds for some root if, for instance, $c_2>0$ and $c_0<0$, or $c_2>0$, $c_1<0$, $c_0>0$, or the same two conditions with all signs reversed.

## Depends on

- [Cell–ECM mechanical model with a linear viscoelastic constitutive law](cell-ecm-mechanical-model-with-viscoelastic-matrix.md)

## Expansion

At $n=1$ the traction factor $n/(1+\lambda n^2)$ has value $\lambda_1$ and derivative $\lambda_2$, which is where these constants enter. Linearizing, eliminating $\tilde n$ and $\tilde\rho$ in favour of $\tilde u$, and applying $\mathcal L_a$ and $\mathcal L_b$ to $e^{\psi t+ikx}$ (which multiply by $a_2\psi^2+a_1\psi+a_0$ and $b_2\psi^2+b_1\psi+b_0$) gives a polynomial in $\psi$ whose coefficients are polynomials in $k^2$. Each $c_j$ is a sum of nonnegative terms plus terms carrying a factor $\tau$ with a minus sign, which is the reason $\tau>0$ is necessary. Which of $c_2,c_3$ vanish depends on the constitutive law: for the purely elastic law $a_1=a_2=b_1=b_2=0$ so $c_2=c_3=0$. The general cubic case is handled by the Routh–Hurwitz criterion.

## Sources

- C. Villa, M. A. J. Chaplain, A. Gerisch, T. Lorenzi, *Mechanical models of pattern and form in biological tissues: the role of stress–strain constitutive equations*, Bulletin of Mathematical Biology 83 (2021), <https://doi.org/10.1007/s11538-021-00912-5> (PMCID: PMC8154836). Section 4.1, equations (18)–(24) and the stability argument for spatially homogeneous perturbations.
