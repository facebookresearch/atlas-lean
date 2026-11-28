# Periodic solutions under threshold-triggered mosquito control in a West Nile virus model

Let $M(t)$ be the number of mosquitoes and $I_b(t)$ the number of infected birds in a bird population of constant size $N_b$. Between control actions,

$$
\frac{dM}{dt} = \mu_m M\Big(1 - \frac{M}{K_m}\Big) - \delta_m M, \qquad \frac{dI_b}{dt} = c\,\beta_{bm}\Big(1 - \frac{I_b}{N_b}\Big) M - \mu_b I_b ,
$$

while $I_b < H_b$; when infected birds reach the threshold $I_b = H_b$, an impulsive intervention kills a fraction $p \in (0,1)$ of mosquitoes and removes a fraction $q \in (0,1)$ of infected birds: $M(t^+) = (1-p)M(t)$, $I_b(t^+) = (1-q)I_b(t)$. Here $\mu_m, \delta_m$ are the mosquito birth and death rates, $K_m$ the carrying capacity, $c$ the biting rate, $\beta_{bm}$ the transmission probability and $\mu_b$ the bird removal rate. Put

$$
M^* = \frac{K_m(\mu_m - \delta_m)}{\mu_m}, \quad N_{mq} = \frac{\mu_b N_b (1-q) H_b}{c\beta_{bm}(N_b - (1-q)H_b)}, \quad N_{mh} = \frac{\mu_b N_b H_b}{c\beta_{bm}(N_b - H_b)} .
$$

**Theorem.**

1. Without control: if $\mu_m < \delta_m$ the disease-free equilibrium is globally asymptotically stable and there is no endemic equilibrium; if $\mu_m > \delta_m$ the disease-free equilibrium is unstable and a unique endemic equilibrium $(M^*, I_b^*)$ is globally asymptotically stable.
2. With control and $\mu_m > \delta_m$, solutions with positive initial values stay positive, and for every $p, q \in (0,1)$ there is a positive order-1 periodic solution.
3. If $(1-p)M^* < N_{mq}$, there is a unique positive periodic solution of order $1$ or $2$, it is orbitally asymptotically stable, and no periodic solution of order $k \ge 3$ exists.
4. If $(1-p)N_{mh} > N_{mq}$, there is a unique positive order-1 periodic solution, it is orbitally asymptotically stable, and no periodic solution of order $k \ge 2$ exists.

## Expansion

The impulsive system is a planar semi-dynamical system with impulse set $\{I_b = H_b\}$ and phase set $\{I_b = (1-q)H_b\}$. The successor function $F(M)$ maps the mosquito level on the phase set to its level after the next impulse; fixed points of $F$ are order-1 cycles, and two-cycles of $F$ are order-2 cycles. Monotonicity of the flow between the two lines gives existence by an intermediate-value argument and uniqueness under the threshold conditions; orbital stability follows from an analogue of the Poincaré criterion for impulsive systems. Biologically, control triggered by bird infection keeps prevalence below $H_b$ along a periodic regime instead of the endemic level.

## Sources

- Lin-Fei Nie and Jing-Yun Shen, *A state-dependent vector control for a West Nile Virus model from mosquitoes to birds*, arXiv:1604.08007, Theorem 1 (Section 3), Theorems 2–6 and Corollary 1 (Section 4). <https://doi.org/10.48550/arXiv.1604.08007> Published version: Nonlinear Dynamics 96 (2019) 751–763, <https://doi.org/10.1007/s11071-019-04819-8>.
