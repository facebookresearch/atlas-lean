# Pulse solutions as thresholds for clot growth

**Setting.** Consider the monotone two-component coagulation system $\partial_t v = D\,\partial_x^2 v + F(v)$, $v = (T, u)$, on $x \in \mathbb{R}$, with bistable kinetics (stable states $0$ and $(T^*, u^*)$, an unstable intermediate state) and travelling wave of speed $c$ connecting $(T^*, u^*)$ to $0$. A **pulse** is a positive stationary solution vanishing at infinity:

$$D v_1'' + F_1(v_1, v_2) = 0, \qquad D v_2'' + F_2(v_1, v_2) = 0, \qquad v(\pm\infty) = 0 .$$

**Theorem (existence and instability of pulses; source Theorem 2).** A pulse exists if and only if the wave speed $c$ is positive. The linearized operator $L w = D w'' + F'(v(x))\, w$ about a pulse has a positive eigenvalue, so the pulse is unstable as a stationary solution.

**Theorem (pulse as a threshold; source Theorem 3).** Let $v$ be a pulse. There are sequences $\hat v^k \le v \le \tilde v^k$ (component-wise, approaching the pulse from below and from above), with $\tilde v^k \to v$ and $\hat v^k \to v$, such that

1. if the initial condition satisfies $(T, u)(x, 0) \ge \tilde v^k(x)$ for all $x$ and some $k$, then $(T, u)(x, t) \to (T^*, u^*)$ as $t \to \infty$ uniformly on bounded intervals (the clot grows);
2. if $(T, u)(x, 0) \le \hat v^k(x)$ for all $x$ and some $k$, then $(T, u)(x, t) \to 0$ uniformly on $\mathbb{R}$ (no clot).

Hence clot growth requires both a positive wave speed and an initial production of thrombin and factor Xa (at the injury) exceeding the threshold set by the pulse. (The ordering is the one under which the two alternatives are disjoint: data above the pulse grow, data below it decay; the pulse itself is the separatrix.) Analogous results hold on the half-line $x \ge 0$ with a homogeneous Neumann condition at the vessel wall.

## Expansion

Existence of the pulse is proved by a Leray–Schauder degree argument, as for fuller coagulation models. For instability, $L v' = 0$ because the problem is translation invariant, so $0$ is an eigenvalue with eigenfunction $v'$; $v'$ changes sign (the pulse rises and then decays), so $0$ is not the principal eigenvalue, and by the spectral theory of monotone systems the principal eigenvalue, which has a positive eigenfunction, is positive. The threshold theorem rests on the comparison principle for monotone systems: perturbing the pulse slightly upward or downward yields sub- and super-solutions whose evolutions are monotone in time, so initial data dominating an upward perturbation are pushed toward $(T^*, u^*)$ and data dominated by a downward perturbation decay to $0$; the explicit construction of the two sequences is in the source's appendix. In the patient-fitted simulations, absence of wave propagation in most hemophilia patients, despite large initial data, was attributed to a non-positive wave speed rather than to insufficient initiation.

## Depends on

- [Bistable coagulation wave in the reduced thrombin–factor Xa model](bistable-coagulation-wave-in-the-reduced-thrombin-factor-xa-model.md)

## Sources

- N. Ratto, A. Bouchnita, P. Chelle, M. Marion, M. Panteleev, D. Nechipurenko, B. Tardy-Poncet, V. Volpert, "Patient-specific modelling of blood coagulation", Bulletin of Mathematical Biology 83 (2021), 50, Section 3 ("Existence of pulses and conditions of clot growth", Eqs. (14)–(18), Theorems 2–3) and Appendix 4 (proof of Theorem 3), <https://doi.org/10.1007/s11538-021-00890-8> (PMC7998098).
