# Optimal convex mixture of incidence functions in a diffusive SIR model

**State system.** On a bounded smooth domain $\mathcal O \subset \mathbb R^N$ and $Q_T = \mathcal O\times(0,T)$, let

$$S_t - d_1\Delta S = -\sum_{i=1}^m \theta_i f_i(S,I), \qquad I_t - d_2\Delta I = \sum_{i=1}^m \theta_i f_i(S,I) - \gamma I, \qquad R_t - d_3\Delta R = \gamma I,$$

with homogeneous Neumann boundary conditions, non-negative initial data $(S_0,I_0,R_0) \in H^2(\mathcal O)^3$ satisfying the Neumann condition, diffusion rates $d_k > 0$ and recovery rate $\gamma > 0$. The candidate incidence functions $f_1,\dots,f_m$ are smooth and non-negative with $f_i(0,I) = f_i(S,0) = 0$, and the weights range over the simplex

$$\mathcal U_{ad} = \Big\{\theta \in \mathbb R^m : \theta_i \ge 0,\ \sum_{i=1}^m \theta_i = 1\Big\}.$$

Each $\theta \in \mathcal U_{ad}$ yields a unique global strong solution $\mathcal F(\theta) = (S_\theta,I_\theta,R_\theta)$, bounded in $L^2(0,T;H^2) \cap L^\infty(0,T;H^1) \cap L^\infty(Q_T)$ uniformly in $\theta$.

**Identification problem.** Given observations $S^{ob}, I^{ob} \in L^2(Q_T)$ and $\sigma > 0$,

$$\min_{\theta\in\mathcal U_{ad}} \mathcal J(\theta) = \int_{Q_T}|S_\theta - S^{ob}|^2 + \int_{Q_T}|I_\theta - I^{ob}|^2 + \frac\sigma2\|\theta\|^2_{\mathbb R^m}.$$

**Theorem.**

1. The parameter-to-state map $\mathcal F$ is Fréchet differentiable; its derivative in direction $\tilde\theta$ is the solution $(\bar S,\bar I,\bar R)$ of the linearized system

$$\bar S_t - d_1\Delta\bar S = -\sum_i\tilde\theta_i f_i(S_\theta,I_\theta) - \sum_i\theta_i\big(\partial_S f_i\,\bar S + \partial_I f_i\,\bar I\big), \qquad \bar I_t - d_2\Delta\bar I = -(\bar S_t - d_1\Delta\bar S) - \gamma\bar I,$$

with $\bar R_t - d_3\Delta\bar R = \gamma\bar I$, Neumann conditions and zero initial data.
2. The problem has at least one global minimizer $\theta^* \in \mathcal U_{ad}$.
3. If $\theta^*$ is optimal and $(P_1,P_2,P_3)$ solves the backward adjoint system

$$-P_{1,t} - d_1\Delta P_1 = \sum_i\theta^*_i\,\partial_S f_i(S^*,I^*)(P_2 - P_1) + 2(S^* - S^{ob}),$$

$$-P_{2,t} - d_2\Delta P_2 = \sum_i\theta^*_i\,\partial_I f_i(S^*,I^*)(P_2 - P_1) + \gamma(P_3 - P_2) + 2(I^* - I^{ob}), \qquad -P_{3,t} - d_3\Delta P_3 = 0,$$

with Neumann conditions and $P(\cdot,T) = 0$, then the gradient of the reduced cost is $\big(\int_{Q_T} f_i(S^*,I^*)(P_2 - P_1) + \sigma\theta^*_i\big)_{i=1}^m$, and the first-order condition is the variational inequality

$$\sum_{i=1}^m(\theta_i - \theta^*_i)\Big(\int_{Q_T} f_i(S^*,I^*)(P_2 - P_1)\,dx\,dt + \sigma\theta^*_i\Big) \ge 0 \qquad \text{for all } \theta \in \mathcal U_{ad}.$$

## Expansion

Uniform a priori bounds make $\mathcal F$ continuous from the compact set $\mathcal U_{ad}$ into $L^2(Q_T)^3$, so $\mathcal J$ attains its minimum. Differentiability follows by writing the equation for $\mathcal F(\theta + \epsilon\tilde\theta) - \mathcal F(\theta)$, dividing by $\epsilon$ and passing to the limit with the uniform $L^\infty$ bounds controlling the Taylor remainders of $f_i$. Testing the linearized system with the adjoint state converts $\mathcal J'(\theta^*)\tilde\theta$ into the stated integral, and minimality over the convex set $\mathcal U_{ad}$ gives the variational inequality, which a projected-gradient scheme exploits numerically.

## Sources

- Mohamed Mehdaoui, Mouhcine Tilioua, "A Note on Quantifying the Contributions of Incidence Functions in Spatio-Temporal Epidemic Models", Acta Biotheoretica 74 (2026), 1, <https://doi.org/10.1007/s10441-025-09512-5>. Published version of arXiv:2509.09301, cited next; locators there refer to the arXiv version.
- Mohamed Mehdaoui, Mouhcine Tilioua, "A note on quantifying the contributions of incidence functions in spatio-temporal epidemic models", arXiv (2025). Problem formulation, Theorem 2.1, Theorem 3.1, Theorem 3.2. <https://doi.org/10.48550/arXiv.2509.09301>
