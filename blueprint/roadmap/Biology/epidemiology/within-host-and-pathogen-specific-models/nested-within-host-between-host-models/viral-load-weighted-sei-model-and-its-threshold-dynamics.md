# Viral-load-weighted SEI model and its threshold dynamics

In a nested multiscale model, a within-host infection model, run over an infectious window $[d_1,d_2]$, is reduced to a single number, the area under the viral load curve

$$
N_h=\frac{\alpha\int_{d_1}^{d_2}U^*(s)\,ds}{y+\mu_v},
$$

where $U^*$ is the infected-cell trajectory, $\alpha$ is the virion production rate per infected cell, $y$ is the immune clearance rate of virions and $\mu_v$ is their natural decay rate. $N_h$ then scales transmission and disease-induced death in the between-host model

$$
\dot S=\Lambda-\beta N_h SI-\mu S,\qquad \dot E=\beta N_h SI-(\mu+\pi+\gamma_1)E,\qquad \dot I=\pi E-(\mu+\gamma_2+dN_h)I,
$$

with all parameters positive. Solutions with positive initial data stay positive, and $\Omega=\{S+E+I\le\Lambda/\mu\}\subset\mathbb R^3_+$ is positively invariant and attracting. The basic reproduction number is

$$
R_0=\frac{\beta N_h\Lambda\pi}{\mu(\mu+\pi+\gamma_1)(\mu+\gamma_2+dN_h)}.
$$

If $R_0<1$, the infection-free equilibrium $(\Lambda/\mu,0,0)$ is globally asymptotically stable in $\Omega$. If $R_0>1$, it is unstable and there is a unique endemic equilibrium with

$$
I^*=\frac{\mu(R_0-1)}{\beta N_h},\qquad E^*=\frac{(\mu+\gamma_2+dN_h)I^*}{\pi},\qquad S^*=\frac{\Lambda}{\beta N_hI^*+\mu}.
$$

The bifurcation at $R_0=1$ is forward (transcritical). Within-host parameters act on the population scale only through $N_h$: faster immune clearance of infected cells or virions lowers $N_h$, and with it $R_0$.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

$R_0$ is the spectral radius of $FV^{-1}$ for the infected compartments $(E,I)$. Global stability for $R_0<1$ follows from the Castillo-Chavez–Feng–Huang criterion. The susceptible subsystem $\dot S=\Lambda-\mu S$ has a globally stable equilibrium, and the infected part can be written as $AY-\widehat G(X,Y)$ with $\widehat G\ge0$ on $\Omega$ and $A$ a Metzler matrix. The direction of the bifurcation follows from the Castillo-Chavez–Song centre-manifold coefficients with $\beta$ as the bifurcation parameter: $a<0$, $b>0$.

## Sources

- Bishal Chhetri and Krishna Kiran Vamsi Dasu, "Stability and bifurcation analysis of a nested multi-scale model for COVID-19 viral infection", *Computational and Mathematical Biophysics* 12 (2024), 20240006, <https://doi.org/10.1515/cmb-2024-0006>. Preprint version: arXiv:2108.12150 (2021), Section 2 (Eqs. (2.17)–(2.20)), Lemmas 1–2, stability and global-stability theorems (Theorem 2.5 in the paper's numbering) and the transcritical bifurcation analysis, <https://doi.org/10.48550/arXiv.2108.12150>.
