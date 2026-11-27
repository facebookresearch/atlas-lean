# Vector Allee effect in a mating and blood-meal mosquito model

**Model.** Aquatic biomass $A$ feeds newly emerged males $M_B$ and females $F_B$; mated females $B$ leave to quest for blood on humans ($Q_H$) or other vertebrates ($Q_V$), become fed ($R_H,R_V$) and return to oviposit:

$$\begin{aligned}
A'&=\lambda_0(a_HR_H+a_VR_V)\Big(1-\frac{A}{L_P}\Big)-(\gamma+\mu_{A1}+\mu_{A2}A)A,\\
\varepsilon M_B'&=(1-\varepsilon\theta)\xi\gamma A-\mu_{M_B}M_B,\qquad
F_B'=\theta\xi\gamma A-SM_BF_B-\mu_{F_B}F_B,\\
B'&=SM_BF_B+a_HR_H+a_VR_V-(b+\mu_B)B,\\
Q_H'&=b\omega B-(\tau_HH+\mu_{Q_H})Q_H,\qquad Q_V'=b(1-\omega)B-(\tau_VV+\mu_{Q_V})Q_V,\\
R_H'&=p\tau_HHQ_H-(a_H+\mu_{R_H})R_H,\qquad R_V'=q\tau_VVQ_V-(a_V+\mu_{R_V})R_V .
\end{aligned}$$

The small parameter $\varepsilon$ encodes short-lived, abundantly recruited males (large male death rate and biomass-to-individual conversion, small female fraction). Setting $\varepsilon=0$ gives the quasi-steady state $M_B=\xi\gamma A/\mu_{M_B}$ and a 7-dimensional reduced system in which mating enters as $\alpha AF_B$ with $\alpha=S\xi\gamma/\mu_{M_B}$.

**Thresholds.** Let

$$\mathcal{R}=\frac{b}{b+\mu_B}\Big(\frac{(1-\omega)qa_V}{a_V+\mu_{R_V}}\frac{\tau_VV}{\tau_VV+\mu_{Q_V}}+\frac{\omega pa_H}{a_H+\mu_{R_H}}\frac{\tau_HH}{\tau_HH+\mu_{Q_H}}\Big)<1$$

(the mean number of returning reproductive cycles per breeding female), $\rho\mathcal{D}=\frac{\lambda_0\theta\xi\gamma}{\mu_{A2}}\frac{\mathcal{R}}{1-\mathcal{R}}$, $\Gamma=\frac{\gamma+\mu_{A1}}{\mu_{A2}}$, $\Delta=\frac{\mu_{F_B}}{\alpha}$, $l=1/L_P$, and

$$N^*=\Gamma+\Delta+2l\Gamma\Delta+2\sqrt{\Gamma\Delta+l(\Gamma+\Delta)\Gamma\Delta+l^2\Gamma^2\Delta^2}\qquad\big(=(\sqrt\Gamma+\sqrt\Delta)^2\text{ if }l=0\big).$$

Nonzero equilibria have aquatic level $A$ solving $(l\rho\mathcal{D}+1)A^2+(\Gamma+\Delta-\rho\mathcal{D})A+\Gamma\Delta=0$, $0<A<L_P$.

**Theorem.** For the reduced system, on the invariant set $\Omega=\{0\le A\le L_P,\ 0\le F_B\le\theta\mu_{M_B}/S\}$ (on which it is cooperative):

1. If $\rho\mathcal{D}<N^*$, the extinction state $\mathbf{0}$ is the only equilibrium and is globally asymptotically stable.
2. If $\rho\mathcal{D}=N^*$, there is one positive equilibrium $\mathbf{x}^*(A_{12})$; $\mathbf{0}$ attracts $[\mathbf{0},\mathbf{x}^*(A_{12})]\setminus\{\mathbf{x}^*(A_{12})\}$ and $\mathbf{x}^*(A_{12})$ attracts $\{\mathbf{x}\in\Omega:\mathbf{x}>\mathbf{x}^*(A_{12})\}$; it is unstable.
3. If $\rho\mathcal{D}>N^*$, there are two ordered positive equilibria $\mathbf{0}\ll\mathbf{x}^*(A_1)\ll\mathbf{x}^*(A_2)$. The order interval $[\mathbf{0},\mathbf{x}^*(A_1)]$ and the upper set $\{\mathbf{x}\ge\mathbf{x}^*(A_1)\}$ are positively invariant; $\mathbf{0}$ is globally asymptotically stable on $[\mathbf{0},\mathbf{x}^*(A_1)]\setminus\{\mathbf{x}^*(A_1)\}$, $\mathbf{x}^*(A_2)$ on $\{\mathbf{x}\in\Omega:\mathbf{x}>\mathbf{x}^*(A_1)\}$, and $\mathbf{x}^*(A_1)$ is unstable. As $\rho\mathcal{D}$ increases from $N^*$ to $\infty$, $A_1$ decreases to $0$ and $A_2$ increases to $L_P$.
4. (Asymptotic equivalence) For initial data in these basins and arbitrary $M_B(0)\ge0$, solutions of the full system satisfy $\mathbf{x}_\varepsilon(t)=\mathbf{x}_0(t)+O(\varepsilon)$ uniformly on $[0,\infty)$ for the seven slow variables, and $M_{B,\varepsilon}(t)=\xi\gamma A_0(t)/\mu_{M_B}+O(\varepsilon)$ uniformly on $[t_0,\infty)$ for every $t_0>0$; so the full model has the same Allee-type pattern for small $\varepsilon$.

## Expansion

The Allee effect comes from mating: female recruitment into the breeding pool is $\alpha AF_B$, quadratic in density at low abundance, so a sparse population cannot replace itself, while overcrowding of the aquatic stage caps growth at high abundance. Solving the linear stages ($B,Q,R$) via the nonsingular Metzler matrix of the gonotrophic cycle gives $a_HR_H+a_VR_V=f\mathcal{R}/(1-\mathcal{R})$ with $f=\theta\xi\gamma\alpha A^2/(\mu_{F_B}+\alpha A)$, which reduces equilibria to one cubic in $A$; $N^*$ is the value at which its quadratic factor has a double root (a saddle–node). Monotone-systems theory finishes the job: points $\mathbf{y}\ll\mathbf{x}^*(A_1)$ with $\mathbf{f}(\mathbf{y})<0$ and $\mathbf{z}$ between the equilibria with $\mathbf{f}(\mathbf{z})>0$ yield invariant order intervals whose trajectories converge monotonically, and a check of the faces of the order intervals extends convergence to their boundaries. The Tikhonov singular-perturbation theorem, upgraded to infinite time intervals for initial data in basins of hyperbolic equilibria, transfers the picture to the full model.

## Sources

- J. Banasiak, Bime M. Ghakanyuy and Gideon A. Ngwa, "A vector Allee effect in mosquito dynamics", Discrete and Continuous Dynamical Systems - B 30 (2025), 4162–4184, <https://doi.org/10.3934/dcdsb.2025079>; numbering as in arXiv:2411.06551: Section 2.1 (asymptotic reduction), Lemma 3.1, Theorems 3.1–3.4, Corollary 3.1 and Theorem 4.1.
