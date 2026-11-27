# Transcritical and Hopf thresholds in a predator–prey model with inducible defence

In nondimensional form, prey $u$ grows logistically. Predators $v$ consume prey through a Holling type II response, but prey induce a defence that lowers the attack rate by the factor $1-\frac{\omega v}{\phi+v}$, which increases with predator density, with $0\le\omega<1$:

$$
\dot u=u\Big[(1-u)-\frac{(1-\frac{\omega v}{\phi+v})v}{m+(1-\frac{\omega v}{\phi+v})u}\Big],\qquad
\dot v=v\Big[\frac{\xi(1-\frac{\omega v}{\phi+v})u}{m+(1-\frac{\omega v}{\phi+v})u}-\delta\Big],
$$

with $m,\phi,\xi,\delta>0$. Solutions starting in the closed positive quadrant stay non-negative and bounded.

1. **Transcritical bifurcation.** At the prey-only equilibrium $E_1=(1,0)$ the predator's invasion rate is $\frac{\xi}{m+1}-\delta$. Taking the half-saturation constant $m$ as bifurcation parameter, $E_1$ undergoes a transcritical bifurcation at

$$
m_{tc}=\frac\xi\delta-1:
$$

predators cannot invade for $m>m_{tc}$ and can for $m<m_{tc}$, where a coexistence equilibrium $E^*$ appears.
2. **Hopf bifurcation.** When $E^*$ is feasible, a simple Hopf bifurcation occurs at the unique $m=m_H$ where the trace of the Jacobian at $E^*$ vanishes, provided its determinant is positive there.

Numerically, stronger defence ($\omega$ larger) stabilizes coexistence. In the reaction–diffusion version it shrinks the Turing region, but with nonlocal intraspecific prey competition the Turing region expands as defence increases.

## Proof sketch

The defence factor equals $1$ at $v=0$, so it does not affect invasion at $E_1$. There the Jacobian is triangular, with eigenvalues $-1$ and $\xi/(m+1)-\delta$, and the second eigenvalue crosses zero at $m_{tc}$. Sotomayor's conditions confirm a transcritical bifurcation. For the Hopf point, the characteristic polynomial at $E^*$ is $\lambda^2-C_1(m)\lambda+C_2(m)$. A simple root $m_H$ of $C_1$ with $C_2(m_H)>0$, and transversal crossing, gives the bifurcation.

## Related topics

- [Lotka–Volterra predator–prey model](../../../lotka-volterra-predator-prey-model/README.md)

## Sources

- Sangeeta Saha, Swadesh Pal and Roderick Melnik, "The Role of Inducible Defence in Ecological Models: Effects of Nonlocal Intraspecific Competition", *Studies in Applied Mathematics* 156 (2026), e70253, <https://doi.org/10.1111/sapm.70253>. Preprint version: arXiv:2411.10551 (2024), Section 2 (system (eq:det1), Theorems 2.1–2.2), Sections 3–5, <https://doi.org/10.48550/arXiv.2411.10551>.
