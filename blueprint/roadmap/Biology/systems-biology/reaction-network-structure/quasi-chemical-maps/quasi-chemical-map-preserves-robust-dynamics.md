# Quasi-chemical map preserves robust dynamics

**Chemical systems.** A monomial $\alpha x_1^{\nu_1}\cdots x_N^{\nu_N}$ in the $i$th component $g_i$ of a polynomial vector field is *chemical* if it is $\ge0$ whenever $x_i=0$ and $x_k\ge0$ for $k\ne i$; that is, a negative monomial in $g_i$ must contain $x_i$. A polynomial dynamical system whose components are all chemical is a *chemical dynamical system* (CDS); CDSs are exactly the mass-action ODEs of reaction networks and keep $\mathbb R^N_{\ge0}$ invariant.

**Robustness.** Two systems are *qualitatively equivalent* on regions $\mathbb U,\mathbb V$ if a homeomorphism $\mathbb U\to\mathbb V$ maps trajectories onto trajectories preserving time direction. A system $\dot{\mathbf y}=\mathbf f(\mathbf y)$ is *robust* (structurally stable) on a compact set $\mathbb K$ if every $C^1$ perturbation $\dot{\mathbf z}=\mathbf f(\mathbf z)+\mathbf F(\mathbf z;\mu)$ with $\mathbf F(\cdot;0)=0$ is qualitatively equivalent to it on $\mathbb K$ for all small $\mu>0$.

**Quasi-chemical map (Definition in Section 4).** Given $\dot y_i=f_i(\mathbf y)$ of degree $n$, a vector $\mathbf T\in\mathbb R^N_{>0}$ and a parameter $\mu>0$, set

$$\frac{dx_i}{dt}=q_i\Big(\mathbf x-\frac{\mathbf T}{\mu}\Big)+\frac{\mu}{T_i}\,x_i\Big[f_i\Big(\mathbf x-\frac{\mathbf T}{\mu}\Big)-q_i\Big(\mathbf x-\frac{\mathbf T}{\mu}\Big)\Big],$$

where the $q_i$ are polynomials of degree at most $n$ that are chemical for all small $\mu$; the right-hand side is a chemical vector field of degree $n+1$. The choice $q_i\equiv0$ gives $\dot x_i=\frac{\mu}{T_i}x_i f_i(\mathbf x-\mathbf T/\mu)$.

**Theorem 4.1.** If $\dot{\mathbf y}=\mathbf f(\mathbf y)$ is robust in a compact $\mathbb K\subset\mathbb R^N$, then for every sufficiently small $\mu>0$ the quasi-chemical system on $\mathbb K+\mathbf T/\mu\subset\mathbb R^N_{\ge0}$ is qualitatively equivalent to the original system on $\mathbb K$.

**Theorems 4.3–4.4.** Robust trajectories on finite time intervals are approximated uniformly, robust equilibria and limit cycles are preserved with their stability, and a robust bifurcation at parameter $\boldsymbol\beta^*$ is reproduced by the CDS at a nearby parameter $\boldsymbol\beta^{**}$. Theorem G.1 extends the construction to robust non-polynomial $C^1$ systems, which are first approximated by polynomial ones.

## Expansion

Substitute $\mathbf x=\mathbf z+\mathbf T/\mu$. Then $x_i\mu/T_i=1+\mu z_i/T_i$ and the system becomes $\dot z_i=f_i(\mathbf z)+\mu\frac{z_i}{T_i}\big(f_i(\mathbf z)-q_i(\mathbf z)\big)$, a perturbation of the target vanishing at $\mu=0$, so robustness gives qualitative equivalence on $\mathbb K$. In $\mathbf x$-coordinates every monomial of $\frac{\mu}{T_i}x_i(f_i-q_i)$ carries the factor $x_i$, so it is chemical regardless of sign, and the remaining term $q_i$ is chemical by assumption. The cost is one extra polynomial degree, which Theorem 4.2 trades against translating only some coordinates.

## Sources

- T. Plesa, "Mapping dynamical systems into chemical reactions", *Nonlinear Dynamics* 113(22) (2025), 31149–31173, definitions of chemical and robust systems, the quasi-chemical map of Section 4, Theorems 4.1–4.4 and G.1, <https://doi.org/10.1007/s11071-025-11622-1> (preprint arXiv:2406.03473).
