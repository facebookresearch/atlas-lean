# Bistable coagulation wave in the reduced thrombin–factor Xa model

**Reduced kinetics.** For platelet-poor plasma, the coagulation cascade reduces to prothrombin $P$, thrombin $T$ and activated factor X $u$:

$$\frac{dP}{dt} = -(k_5 u + k_6 T + k_7 T^2 + k_8 T^3) P, \quad \frac{dT}{dt} = (k_5 u + k_6 T + k_7 T^2 + k_8 T^3) P - k_9 T, \quad \frac{du}{dt} = (k_1 + k_2 T + k_3 T^2)(u_0 - u) - k_4 u,$$

with $k_1$ describing initiation, the positive feedback terms propagation, and $k_9 T$, $k_4 u$ termination. Far from the vessel wall set $k_1 = 0$ and add equal diffusion $D$ to all species. If $k_9 = 0$ then $P + T$ is conserved, and with $P + T \equiv T_0$ one obtains the two-component system

$$\partial_t T = D\,\partial_x^2 T + F_1(T, u), \qquad \partial_t u = D\,\partial_x^2 u + F_2(T, u),$$

$$F_1 = (k_5 u + k_6 T + k_7 T^2 + k_8 T^3)(T_0 - T) - k_9 T, \qquad F_2 = (k_2 T + k_3 T^2)(u_0 - u) - k_4 u,$$

which approximates the full system for small $k_9 > 0$. On $0 \le T \le T_0$, $0 \le u \le u_0$ one has $\partial F_1/\partial u \ge 0$ and $\partial F_2/\partial T \ge 0$, so the system is **monotone** (cooperative) and satisfies a comparison principle.

**Equilibria.** $F_2 = 0$ gives $u = (k_2 T + k_3 T^2)u_0/(k_4 + k_2 T + k_3 T^2)$, and then $F_1 = 0$ reduces to $T = 0$ or

$$\Big(\frac{k_5 (k_2 + k_3 T)\, u_0}{k_4 + k_2 T + k_3 T^2} + k_6 + k_7 T + k_8 T^2\Big)(T_0 - T) = k_9 .$$

Under physiological parameters there are two positive roots $T_* < T^*$: the states $(0, 0)$ (no coagulation) and $(T^*, u^*)$ (thrombin production) are stable and $(T_*, u_*)$ is unstable (bistability).

**Theorem (coagulation wave).** If the equilibrium equation has two positive solutions $T_* < T^*$, the travelling-wave problem

$$D\theta'' + c\theta' + F_1(\theta, \omega) = 0, \quad D\omega'' + c\omega' + F_2(\theta, \omega) = 0, \quad (\theta, \omega)(-\infty) = (T^*, u^*),\ (\theta, \omega)(+\infty) = (0, 0)$$

has a component-wise monotonically decreasing solution for a unique speed $c$. It is globally asymptotically stable: for monotonically decreasing initial data with these limits, $T(x,t) \to \theta(x - ct + h)$ and $u(x,t) \to \omega(x - ct + h)$ uniformly in $x$ for some shift $h$. The speed has the minimax representation

$$c = \inf_{w \in M}\ \sup_{x \in \mathbb{R},\ i = 1,2} \frac{D w_i'' + F_i(w_1, w_2)}{-w_i'} = \sup_{w \in M}\ \inf_{x \in \mathbb{R},\ i = 1,2} \frac{D w_i'' + F_i(w_1, w_2)}{-w_i'},$$

where $M$ is the set of smooth monotonically decreasing $w = (w_1, w_2)$ with the same limits.

## Expansion

Existence, uniqueness of the speed, stability and the minimax formula are consequences of the general theory of bistable travelling waves for monotone reaction–diffusion systems (Volpert and Volpert): the comparison principle traps solutions between shifted sub- and super-solutions, and any monotone test function $w$ gives the two-sided bound in the minimax formula. The sign of $c$ decides whether the clot grows ($c > 0$, thrombin-producing state invades) or not. With parameters fitted to patients' thrombin generation curves, numerical wave speeds split hemophilia patients into three groups (no propagation, slow propagation around $0.2\ \mu$m/s, near-normal propagation), the first two separated from healthy subjects.

## Sources

- N. Ratto, A. Bouchnita, P. Chelle, M. Marion, M. Panteleev, D. Nechipurenko, B. Tardy-Poncet, V. Volpert, "Patient-specific modelling of blood coagulation", Bulletin of Mathematical Biology 83 (2021), 50, Section 2 (reduced model, Eqs. (1)–(3)) and Section 3 ("Existence, stability, and speed of waves", Eqs. (4)–(13), Theorem 1; "Patient-specific clot growth rate", Fig. 5), <https://doi.org/10.1007/s11538-021-00890-8> (PMC7998098).
- A. I. Volpert, V. A. Volpert, V. A. Volpert, *Traveling Wave Solutions of Parabolic Systems*, American Mathematical Society (1994).
