# Pontryagin conditions for optimal chemotherapy in a delayed tumour-immune model

**Problem.** Extend the delayed tumour-immune-normal cell model with a drug concentration $u(t)$, infused at rate $v(t)$ and cleared at rate $d_1$, killing each cell type with fractional kill $a_i(1-e^{-u})$:

$$
\begin{aligned}
E'&=\sigma+\frac{\rho E_\tau T_\tau}{\eta+T_\tau}-\mu E_\tau T_\tau-\delta E-a_1(1-e^{-u})E,\\
T'&=r_2T(1-\beta T)-nET-c_1NT-a_2(1-e^{-u})T,\\
N'&=r_3N(1-\beta_2N)-c_2TN-a_3(1-e^{-u})N,\qquad u'=v-d_1u,
\end{aligned}
$$

where $X_\tau=X(t-\tau)$, with given initial histories $E=\varphi_1$, $T=\varphi_2$, $N=\varphi_3$, $u=\varphi_4$ on $[-\tau,0]$. Maximize

$$
J(v)=\int_0^{t_f}\Bigl(E(t)-T(t)-\tfrac{B_v}{2}v(t)^2\Bigr)\,dt
$$

over $V_{ad}=\{v\in L^\infty([0,t_f]):0\le v(t)\le v_{\max}\}$, subject to the state constraint $N(t)\ge 0.75$ for $t\in[0,t_f]$.

**Existence.** Suppose the set of admissible states is nonempty: some $v\in V_{ad}$ keeps $N(t)\ge0.75$ on $[0,t_f]$ (this depends on the initial history; for instance none does if $\varphi_3(0)<0.75$). Then an optimal pair $(x^*,v^*)\in W^{1,\infty}([0,t_f],\mathbb R^4)\times L^\infty([0,t_f])$ exists: $V_{ad}$ is nonempty, convex and closed, the right-hand side is bounded by a linear function of state and control, the integrand is concave in $v$, and $E-T-\tfrac{B_v}{2}v^2\le h_2-h_3|v|^2$ with $h_3=B_v/2$.

**Necessary conditions.** With Hamiltonian $H=E-T-\tfrac{B_v}{2}v^2+\lambda_1E'+\lambda_2T'+\lambda_3N'+\lambda_4u'+\gamma(t)(N-0.75)$, the adjoints satisfy the advanced equations

$$
\lambda_i'(t)=-\frac{\partial H}{\partial x_i}(t)-\chi_{[0,t_f-\tau]}(t)\,\frac{\partial H}{\partial x_{i,\tau}}(t+\tau),\qquad \lambda_i(t_f)=0,
$$

for the delayed states $x_i\in\{E,T\}$ (and without the advanced term for $N,u$), and the optimal infusion is

$$
v^*(t)=\max\Bigl(0,\,\min\Bigl(v_{\max},\,\frac{\lambda_4(t)}{B_v}\Bigr)\Bigr),
$$

the projection of $\lambda_4/B_v$ onto $[0,v_{\max}]$. The source's Eq. (32) prints $v^*=\min(v_{\max},\lambda_4/B_v)$, which drops the lower bound; the page keeps it because the admissible controls take values in $[0,v_{\max}]$ and the Hamiltonian is strictly concave in $v$, so its maximizer over that interval is the clipped stationary point.

## Expansion

Existence follows from the Fleming-Rishel and Lukes compactness theorems once the state is shown bounded by comparison with a linear delay system. The optimality system uses the Pontryagin principle for retarded problems with mixed constraints: a delay in the state equation produces an advanced term in the adjoint, active only on $[0,t_f-\tau]$ because perturbations after $t_f-\tau$ cannot propagate through the delay before the horizon ends. Since $H$ is strictly concave in $v$, $\partial H/\partial v=-B_vv+\lambda_4=0$ gives the unconstrained maximizer, which is then clipped to the control bounds. Adding adoptive immunotherapy $w(t)s_1$ to the $E$ equation with cost $\tfrac{B_w}{2}w^2$ yields the analogous projection formula for $w^*$.

## Depends on

- [Tumour-free equilibrium threshold of the delayed tumour-immune-normal cell model](tumour-free-equilibrium-threshold-of-the-delayed-tumour-immune-normal-cell-model.md)

## Sources

- Rihan FA, Abdelrahman DH, Al-Maskari F, Ibrahim F, Abdeen MA. Delay differential model for tumour-immune response with chemoimmunotherapy and optimal control. *Computational and Mathematical Methods in Medicine* (2014) 982978. <https://doi.org/10.1155/2014/982978>. PMCID: PMC4147205. Eqs. (14c) and (15a)-(15g), Theorem 5 (whose first condition is that the set of admissible states is nonempty), Theorem 6, Eqs. (26)-(32), Section 7.
