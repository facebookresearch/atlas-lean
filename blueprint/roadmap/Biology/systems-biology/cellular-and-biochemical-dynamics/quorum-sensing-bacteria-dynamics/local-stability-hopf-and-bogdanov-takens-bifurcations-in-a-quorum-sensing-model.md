# Local stability and Hopf and Bogdanov–Takens bifurcations in a quorum-sensing bacteria model

**Model.** With the autoinducer concentration held constant, the rescaled densities of motile bacteria $u \ge 0$ and static bacteria $v > 0$ obey

$$\dot u = f(u,v) = \frac{u^2}{v(1 + K u^2)} + a - b u, \qquad \dot v = g(u,v) = u^2 + a e - v,$$

with saturation constant $K > 0$, bacterial decay parameter $b > 0$, and production parameters $a, e > 0$ (the product $ae$ depends only on the bacterial response to the autoinducer). This is an activator–inhibitor system with saturating autocatalysis, the constant-autoinducer reduction of a three-component model in which the autoinducer is also dynamic.

**Proposition (local stability).** At a positive steady state $(u_*, v_*)$ put

$$\mathcal{J} = \frac{2u_*}{v_*(1 + K u_*^2)^2}, \qquad \Theta = \mathcal{J} - \frac{2u_*^3}{v_*^2(1 + K u_*^2)}.$$

The Jacobian has trace $\mathcal{J} - b - 1$ and determinant $b - \Theta$, hence:
1. if $\mathcal{J} < b + 1$ and $b > \Theta$, the steady state is locally asymptotically stable;
2. if $\mathcal{J} > b + 1$ and $b > \Theta$, it is a repeller;
3. if $b < \Theta$, it is a saddle.

**Theorem (Hopf).** At a positive equilibrium where the trace of the Jacobian vanishes, its determinant is positive and the first Lyapunov coefficient $l_1 \neq 0$, the system undergoes a codimension-one Hopf bifurcation: supercritical with a stable limit cycle if $l_1 < 0$, subcritical with an unstable one if $l_1 > 0$.

**Theorem (Bogdanov–Takens).** Let $(U, V)$ be a positive equilibrium in

$$\Omega_{BT} = \big\{(u,v) \in \mathbb R_{>0}^2 : -2u^5 + v^3 > 0,\ 2u^3 - v^2 > 0,\ -2u^5 + v^3 - u^3v > 0,\ (u^2 - v)(2u^5 + u^3v - v^3) > 0,\ 4u^5 - u^3v - 6u^2v^2 + 4v^3 \ne 0\big\},$$

and let $(b^*, K^*)$ be the positive parameter values at which the Jacobian at $(U, V)$ is nilpotent (a double zero eigenvalue of geometric multiplicity one). The last condition in $\Omega_{BT}$ makes the map $(u, v, b, K) \mapsto (f, g, \operatorname{tr}, \det)$ regular at $(U, V, b^*, K^*)$ (transversality). If moreover the two normal-form coefficients are nonzero, the system undergoes a codimension-two Bogdanov–Takens bifurcation at $(b^*, K^*)$, from which curves of saddle-node, Hopf and homoclinic bifurcations emanate in the $(b, K)$ plane.

In the full three-component model the corresponding oscillations break up through Shilnikov homoclinic bifurcations, which produce chaotic quorum-sensing dynamics.

## Proof sketch

The Jacobian at $(u_*, v_*)$ is

$$\begin{pmatrix} \mathcal{J} - b & -\frac{u_*^2}{v_*^2(1 + K u_*^2)} \\ 2u_* & -1 \end{pmatrix},$$

since $\partial_u\big(u^2/(v(1+Ku^2))\big) = 2u/(v(1+Ku^2)^2)$. Its trace and determinant give the three cases, and their simultaneous degeneracies are the Hopf points ($\mathrm{tr} = 0$, $\det > 0$) and the Bogdanov–Takens points ($\mathrm{tr} = \det = 0$). The origin of the time-rescaled system is a repeller (one zero eigenvalue with a centre manifold, one eigenvalue $ae > 0$), so bacteria never die out from small positive densities. Sustained oscillations of motile versus static bacteria arise from the Hopf branch and terminate in homoclinic loops born at the Bogdanov–Takens point.

## Sources

- M. Harris, V. Rivera-Estay, P. Aguirre and V. F. Breña-Medina, "Multiple local and global bifurcations and their role in quorum sensing dynamics", *The ANZIAM Journal* 67 (2025), e17, <https://doi.org/10.1017/s1446181125000100>. Preprint version: arXiv:2409.02764 (2024), section on constant autoinducer concentration (the 2D system, the local stability proposition, the Andronov–Hopf theorem and the Bogdanov–Takens theorem) and section on bifurcation and chaos in the 3D system, <https://doi.org/10.48550/arXiv.2409.02764>.
