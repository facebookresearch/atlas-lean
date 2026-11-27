# Parabolic limit of kinetic chemotaxis to the Keller–Segel equation

**Setting.** Bacteria with velocity $v$ in a compact, symmetric velocity set $V \subset \mathbb R^3$ (with $|V| = \int_V dv$) at position $x \in \mathbb R^3$ have phase-space density $f_\varepsilon(x,t,v)$ obeying the run-and-tumble equation in parabolic scaling,

$$\varepsilon^2 \partial_t f_\varepsilon + \varepsilon\, v \cdot \nabla_x f_\varepsilon = \int_V \big[K_\varepsilon(x,t,v,v') f_\varepsilon(x,t,v') - K_\varepsilon(x,t,v',v) f_\varepsilon(x,t,v)\big]\, dv', \qquad f_\varepsilon(x,0,v) = f_0(x,v),$$

where the chemoattractant field is fixed and absorbed into the tumbling kernel $K_\varepsilon = K_0 + \varepsilon K_1$. The kernel pair lies in the admissible set

$$\mathcal A = \big\{(K_0, K_1) \in \big(C^1(\mathbb R^3 \times [0,\infty) \times V \times V)\big)^2 : \|K_0\|_{C^1}, \|K_1\|_{C^1} \le C,\ K_0 \ge \alpha > 0 \text{ symmetric},\ K_1 \text{ antisymmetric in } (v,v')\big\}$$

for fixed constants $C, \alpha > 0$. For such kernels the local equilibrium is uniform, $F \equiv 1/|V|$.

**Theorem.** Let $(K_0, K_1) \in \mathcal A$ and $f_0 \in C^1_c(\mathbb R^3 \times V)$ nonnegative. Then:

1. for all sufficiently small $\varepsilon$ the solution $f_\varepsilon$ exists and is bounded in $L^\infty\big([0,T]; L^1_+ \cap L^\infty(\mathbb R^3 \times V)\big)$ for every $T < \infty$;
2. $f_\varepsilon \to \rho F$ in that space, where $\rho$ solves the Keller–Segel (drift–diffusion) equation

$$\partial_t \rho - \nabla \cdot (D \nabla \rho) + \nabla \cdot (\rho\, \Gamma) = 0, \qquad \rho(x,0) = \int_V f_0(x,v)\, dv,$$

with

$$D = \int_V v \otimes \kappa(x,t,v)\, dv, \qquad \Gamma = -\int_V v\, \theta(x,t,v)\, dv,$$

and $\kappa, \theta$ solve the cell problems $\mathcal K_0(\kappa) = vF$, $\mathcal K_0(\theta) = \mathcal K_1(F)$, where $\mathcal K_i(g) = \int_V (K_i\, g' - K_i'\, g)\, dv'$;
3. the bounds and the convergence are uniform over $\mathcal A$.

## Proof sketch

Insert the Hilbert expansion $f_\varepsilon = f^{(0)} + \varepsilon f^{(1)} + \varepsilon^2 f^{(2)} + \dots$. At order $\varepsilon^0$ the tumbling operator $\mathcal K_0$ must annihilate $f^{(0)}$; its kernel is spanned by $F$, so $f^{(0)} = \rho F$. At order $\varepsilon^1$, $v \cdot \nabla_x(\rho F) = \mathcal K_0(f^{(1)}) + \mathcal K_1(\rho F)$, solved through the cell functions $\kappa, \theta$ (solvable because $vF$ and $\mathcal K_1(F)$ have zero velocity mean). Integrating the order-$\varepsilon^2$ equation over $V$ kills the collision terms and gives the conservation law for $\rho$ with the flux $-D\nabla\rho + \rho\Gamma$. Uniformity over $\mathcal A$ comes from the lower bound $K_0 \ge \alpha$, which gives a uniform spectral gap for $\mathcal K_0$, and the $C^1$ bounds.

## Sources

- Kathrin Hellmuth, Christian Klingenberg, Qin Li and Min Tang, "Multiscale Convergence of the Inverse Problem for Chemotaxis in the Bayesian Setting", *Computation* 9 (2021), 119, <https://doi.org/10.3390/computation9110119>. Preprint version: arXiv:2110.13787 (2021), Section 2 and Theorem 1, <https://doi.org/10.48550/arXiv.2110.13787>.
