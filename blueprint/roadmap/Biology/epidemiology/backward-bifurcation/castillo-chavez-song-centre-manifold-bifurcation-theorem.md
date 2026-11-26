# Castillo-Chavez–Song centre-manifold bifurcation theorem

**Setting.** Consider a parametrized system

$$\frac{dx}{dt} = f(x, \phi), \qquad x \in \mathbb{R}^n,\ \phi \in \mathbb{R},$$

with $f$ of class $C^2$ in $(x, \phi)$ near $(0, 0)$ and $f(0, \phi) = 0$ for all $\phi$, so $x = 0$ is
an equilibrium for every parameter value (in epidemic models: the disease-free equilibrium after
translation, with $\phi = \beta - \beta^*$ the deviation of a transmission rate from its value at
$\mathcal{R}_0 = 1$). Assume:

1. $A = D_x f(0, 0)$ has a simple eigenvalue $0$ and all other eigenvalues have negative real parts;
2. $A$ has a nonnegative right null vector $w$ and a left null vector $v$, normalized by $v \cdot w = 1$.

Let $f_k$ be the $k$-th component of $f$ and define the bifurcation coefficients

$$a = \sum_{k,i,j=1}^{n} v_k w_i w_j \frac{\partial^2 f_k}{\partial x_i \partial x_j}(0, 0), \qquad
b = \sum_{k,i=1}^{n} v_k w_i \frac{\partial^2 f_k}{\partial x_i \partial \phi}(0, 0).$$

**Theorem.** The local dynamics near $x = 0$ are determined by the signs of $a$ and $b$:

1. $a > 0$, $b > 0$: for $\phi < 0$ with $|\phi| \ll 1$, $0$ is locally asymptotically stable and there
   is a positive unstable equilibrium; for $0 < \phi \ll 1$, $0$ is unstable and there is a negative,
   locally asymptotically stable equilibrium;
2. $a < 0$, $b < 0$: for $\phi < 0$, $0$ is unstable; for $0 < \phi \ll 1$, $0$ is locally asymptotically
   stable and there is a positive unstable equilibrium;
3. $a > 0$, $b < 0$: for $\phi < 0$, $0$ is unstable and there is a locally asymptotically stable
   negative equilibrium; for $0 < \phi \ll 1$, $0$ is stable and a positive unstable equilibrium
   appears;
4. $a < 0$, $b > 0$: as $\phi$ crosses $0$ from negative to positive, $0$ changes from stable to
   unstable, and a negative unstable equilibrium becomes positive and locally asymptotically stable.

**Backward bifurcation.** With $b > 0$ (the usual case when $\phi$ raises transmission), the
bifurcation at $\mathcal{R}_0 = 1$ is forward (transcritical, a stable endemic equilibrium appears only
for $\mathcal{R}_0 > 1$) when $a < 0$, and backward (subcritical) when $a > 0$: then an unstable
endemic equilibrium exists for $\mathcal{R}_0$ slightly below $1$, and a stable endemic equilibrium
coexists with the stable disease-free equilibrium, so $\mathcal{R}_0 < 1$ is necessary but not
sufficient for elimination.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

Near $\phi = 0$ the flow reduces to a one-dimensional centre manifold tangent to $w$. Writing
$x = c\, w + O(c^2)$ and projecting onto $v$ gives the normal form

$$\dot c = \tfrac{1}{2} a\, c^2 + b\, \phi\, c + O\bigl(c^3 + \phi^2 c + \phi c^2\bigr),$$

whose nontrivial equilibrium is $c^* \approx -2 b \phi / a$. Its sign, which decides whether the
branch enters the biologically relevant orthant for $\phi < 0$ or $\phi > 0$, is the sign of
$-b\phi/a$, and its stability is that of $-b\phi$. In epidemic models the left null vector $v$ has
zero entries in the uninfected compartments, so $a$ collects only second derivatives of the
infected equations; terms such as disease-induced mortality, imperfect vaccination, reinfection or
incident co-infection can make $a$ positive. In the malaria sub-model of a malaria–COVID-19 system,
with the mosquito-to-human transmission rate as bifurcation parameter, $b = v_2 w_6 b_{\mathrm{bite}} >
0$ and the explicit sign condition $a > 0$ (their Eq. (24)) yields a backward bifurcation, whereas
the COVID-19 sub-model has $a < 0$ and only a forward bifurcation.

## Sources

- C. Castillo-Chavez, B. Song, "Dynamical models of tuberculosis and their applications",
  Mathematical Biosciences and Engineering 1 (2004) 361-404, Theorem 4.1,
  <https://doi.org/10.3934/mbe.2004.1.361>.
- S. Y. Tchoumi, M. L. Diagne, H. Rwezaura, J. M. Tchuenche, "Malaria and COVID-19 co-dynamics: A
  mathematical model and optimal control", Applied Mathematical Modelling 99 (2021), Sections
  3.1-3.2, Eqs. (9)-(11) and (22)-(24), <https://doi.org/10.1016/j.apm.2021.06.016> (PMC8249695).
- A. Omame, M. Abbas, C. P. Onyenegecha, "Backward bifurcation and optimal control in a co-infection
  model for SARS-CoV-2 and ZIKV", Results in Physics 37 (2022) 105481, backward bifurcation analysis
  of model (11), <https://doi.org/10.1016/j.rinp.2022.105481> (PMC8994284).
