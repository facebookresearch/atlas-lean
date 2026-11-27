# Hybrid Cucker–Smale–chemotaxis model and its linearized flocking

**Model.** $N$ cells (discrete agents of radius $R$) with positions $\mathbf X_i$ and velocities $\mathbf V_i$ in $\mathbb R^2$ align their velocities as in the Cucker–Smale model and climb the gradient of a continuous chemical signal $f(\mathbf x,t)$ that they produce:

$$\dot{\mathbf V}_i=\frac\beta N\sum_{j=1}^N\frac{\mathbf V_j-\mathbf V_i}{\bigl(1+\|\mathbf X_i-\mathbf X_j\|^2/R^2\bigr)^{\sigma}}+\gamma\nabla f(\mathbf X_i),\qquad \dot{\mathbf X}_i=\mathbf V_i,$$

$$\partial_tf=D\Delta f+g_{\mathbf X}-\eta f,\qquad f(\mathbf x,0)=0,$$

with source $g_{\mathbf X}(\mathbf x,t)=\xi\sum_j\varphi(|x_1-X_{j1}|)\varphi(|x_2-X_{j2}|)$ for a nonnegative bounded $\varphi\in C^1_c([-R,R])$. The signal is given explicitly by Duhamel's formula

$$f(\mathbf x,t)=\int_0^te^{-\eta(t-\tau)}\int_{\mathbb R^2}\Gamma(\mathbf x-\bar{\mathbf x},t-\tau)\,g_{\mathbf X}(\bar{\mathbf x},\tau)\,d\bar{\mathbf x}\,d\tau,$$

with $\Gamma$ the heat kernel, so the system is a delay (memory) integro-differential system for the particles alone.

**Theorem (well-posedness).** The particle system with the signal eliminated has a unique local solution (by a contraction argument for the integral formulation) which extends to a unique global solution for all $t\ge0$.

**Theorem (linearized asymptotics).** Replace the source by the ball indicator $g_{\mathbf X}=\xi\sum_j\chi_{B(\mathbf X_j,R)}$, $\xi>0$, with $B(\mathbf X_j,R)=\{\mathbf x:\|\mathbf x-\mathbf X_j\|\le R\}$, and linearize around coinciding positions: the alignment weight is replaced by $1$ and the chemotactic force by $-\int_0^t\bar C(t-\tau)\sum_j\bigl(\mathbf X_i(t)-\mathbf X_j(\tau)\bigr)d\tau$ with the memory kernel

$$\bar C(s)=\frac{\pi R^2\,C(s)\,e^{-R^2/(4sD)}}{2sD},\qquad C(s)=\frac{\gamma\xi\,e^{-\eta s}}{4\pi sD}.$$

For this linear system, all particles converge as $t\to\infty$ to a common velocity and a common position (their centre of mass), and the centre-of-mass velocity tends to zero.

## Expansion

Alignment alone (Cucker–Smale) yields velocity consensus but not spatial aggregation; the self-generated signal adds a delayed attraction towards where other cells were in the past. In the linearized system, the attraction acts like a damped spring towards past positions of the group, which both pulls particles together and slows the centre of mass. The model was introduced as a minimal version of collective migration in the zebrafish lateral line primordium.

## Sources

- Ezio Di Costanzo, Marta Menci, Eleonora Messina, Roberto Natalini and Antonia Vecchio, "A hybrid mathematical model of collective motion under alignment and chemotaxis", arXiv:1507.02980 (2015), Section 2 (model and explicit signal), Theorems 1–2 and Proposition 1 (existence and uniqueness), Section 5 (ball-indicator source (5.1), kernels (5.6) and (5.14), linear system (5.15) and Theorem 3), <https://doi.org/10.48550/arXiv.1507.02980>.
