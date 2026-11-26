# Castillo-Chavez–Song centre-manifold criterion

Consider $\dot x=f(x,\phi)$ with $x\in\mathbb{R}^n$, parameter $\phi\in\mathbb{R}$, $f\in C^2$, and $f(0,\phi)=0$ for all $\phi$ (after translating the disease-free equilibrium to the origin). Assume

- **(A1)** $A=D_xf(0,0)$ has a simple zero eigenvalue and all other eigenvalues have negative real part;
- **(A2)** $A$ has a right eigenvector $w$ and a left eigenvector $v$ for the zero eigenvalue with $v\cdot w=1$, where $v\ge 0$ and $w_j>0$ for every coordinate $j$ in which the equilibrium vanishes (in epidemic models: the infected classes).

Define

$$
a=\sum_{k,i,j=1}^{n}v_kw_iw_j\frac{\partial^2 f_k}{\partial x_i\partial x_j}(0,0),\qquad
b=\sum_{k,i=1}^{n}v_kw_i\frac{\partial^2 f_k}{\partial x_i\partial\phi}(0,0).
$$

Then, for $|\phi|$ small:

1. $a>0$, $b>0$: for $\phi<0$ the origin is locally asymptotically stable and a positive unstable equilibrium exists; for $\phi>0$ the origin is unstable and the bifurcating equilibrium is negative and stable (**backward bifurcation**).
2. $a<0$, $b<0$: for $\phi<0$ the origin is unstable; for $\phi>0$ it is stable and a positive unstable equilibrium exists.
3. $a>0$, $b<0$: for $\phi<0$ the origin is unstable with a negative stable equilibrium; for $\phi>0$ the origin is stable and a positive unstable equilibrium appears.
4. $a<0$, $b>0$: as $\phi$ passes through $0$ the origin changes from stable to unstable and a negative unstable equilibrium becomes positive and locally asymptotically stable (**forward, transcritical bifurcation**).

In epidemic models one takes $\phi=\beta-\beta^*$, where $\beta$ is a transmission rate and $\beta^*$ is the value with $R_0=1$; then (A1) holds because $R_0=1$ makes $0$ a simple eigenvalue of the infected-subsystem Jacobian, $b>0$ typically, and the sign of $a$ decides between a forward bifurcation (stable endemic equilibrium emerging at $R_0=1$) and a backward one (endemic equilibria for $R_0<1$, so $R_0<1$ no longer suffices for elimination). In the source's SEICR model with comorbid class $C$, the computation gives $a<0$ and $b>0$, so the endemic equilibrium bifurcates forward and is locally asymptotically stable for $R_0$ slightly above $1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Expansion

By (A1) the dynamics near $(0,0)$ reduce to a one-dimensional centre manifold tangent to $w$. Writing $x=cw+\dots$ and projecting with $v$, the reduced equation is $\dot c=\frac{a}{2}c^2+b\,\phi\,c+O(|c|^3+\phi^2|c|+\phi c^2)$, the normal form of a transcritical bifurcation. Its nonzero equilibrium is $c^*\approx-2b\phi/a$; the signs of $a$ and $b$ decide on which side of $\phi=0$ it is positive (biologically feasible) and whether it is stable, which yields the four cases.

## Sources

- P. Das, R. K. Upadhyay, A. K. Misra, F. A. Rihan, P. Das, D. Ghosh, "Mathematical model of COVID-19 with comorbidity and controlling using non-pharmaceutical interventions and vaccination", *Nonlinear Dynamics* 106 (2021) 1213–1227. <https://doi.org/10.1007/s11071-021-06517-w>. PMCID: PMC8133070. (Theorem 3, applying the criterion to the SEICR model.)
- C. Castillo-Chavez, B. Song, "Dynamical models of tuberculosis and their applications", *Mathematical Biosciences and Engineering* 1 (2004) 361–404. <https://doi.org/10.3934/mbe.2004.1.361> (Theorem 4.1.)
