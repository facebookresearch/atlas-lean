# Optimal immune-boosting and antiviral controls in the target-cell model

**Model.** Healthy target cells $S$ (type II pneumocytes for SARS-CoV-2 pneumonia), infected cells $I$ and free virus $V$ follow the target-cell-limited model with lumped innate (cytokine and chemokine mediated) clearance:

$$
S'=\omega-\beta SV-\mu S,\qquad I'=\beta SV-(d+\mu)I,\qquad V'=\alpha I-(b+\mu_1)V,
$$

where $d=\sum_{i=1}^6d_i$ and $b=\sum_{i=1}^6b_i$ collect the removal rates of infected cells and virus attributed to IL-6, TNF-$\alpha$, IFN-$\alpha$, CCL5, CXCL8 and CXCL10. Its basic reproduction number is $R_0=\dfrac{\beta\alpha\omega}{\mu(d+\mu)(b+\mu_1)}$.

**Control problem.** Treat the immune-mediated clearance rates as controls $u_{11}(t)$ (infected cells) and $u_{12}(t)$ (virus), and add an antiviral that lowers the burst rate by $u_2(t)$:

$$
S'=\omega-\beta SV-\mu S,\qquad I'=\beta SV-\mu I-u_{11}I,\qquad V'=(\alpha-u_2)I-\mu_1V-u_{12}V,
$$

with admissible controls $U=\{(u_{11},u_{12},u_2)\text{ measurable}:\ u_{11}\in[0,u_{11}^{\max}],\ u_{12}\in[0,u_{12}^{\max}],\ u_2\in[0,u_2^{\max}]\}$ on $[0,T]$, minimizing

$$
J(u)=\int_0^T\big(I+V+A_1u_{11}^2+A_2u_{12}^2+A_3u_2^2\big)\,dt,\qquad A_1,A_2,A_3>0 .
$$

**Theorem (existence).** There exists $(u_{11}^*,u_{12}^*,u_2^*)\in U$ attaining $\min_{u\in U}J(u)$.

**Characterization.** With Hamiltonian $H=I+V+\sum A u^2+\lambda_1S'+\lambda_2I'+\lambda_3V'$, Pontryagin's principle gives adjoint equations, for the state system above,

$$
\lambda_1'=\lambda_1(\beta V+\mu)-\lambda_2\beta V,\qquad \lambda_2'=-1+\lambda_2(\mu+u_{11})-\lambda_3(\alpha-u_2),\qquad \lambda_3'=-1+(\lambda_1-\lambda_2)\beta S+\lambda_3(\mu_1+u_{12}),
$$

with $\lambda_i(T)=0$, and the optimal controls are the projected stationarity solutions

$$
u_{11}^*=\min\Big\{\max\Big\{\frac{\lambda_2I}{2A_1},0\Big\},u_{11}^{\max}\Big\},\quad u_{12}^*=\min\Big\{\max\Big\{\frac{\lambda_3V}{2A_2},0\Big\},u_{12}^{\max}\Big\},\quad u_2^*=\min\Big\{\max\Big\{\frac{\lambda_3I}{2A_3},0\Big\},u_2^{\max}\Big\}.
$$

## Expansion

Existence follows the Fleming–Rishel criteria: solutions stay nonnegative and bounded for bounded controls, so the admissible state–control set is nonempty; $U$ is closed and convex and the dynamics are affine in the controls; and the running cost is convex in $u$ with the coercive lower bound $c|u|^2$, $c=\min\{A_1,A_2,A_3\}$. The control formulas come from $\partial H/\partial u=0$, e.g. $2A_1u_{11}-\lambda_2I=0$, projected onto the box. Numerically the state–adjoint system is solved by forward–backward sweep; in the paper's simulations combining immune boosting with replication inhibition lowers infected cells and viral load faster than either alone. The uncontrolled model is the basic viral dynamics model, with threshold $R_0$ (disease-free equilibrium globally stable for $R_0<1$, infected equilibrium for $R_0>1$, transcritical bifurcation at $R_0=1$).

## Sources

- B. Chhetri, D. K. K. Vamsi, V. M. Bhagat, A. V. S., "Crucial Inflammatory Mediators and Efficacy of Drug Interventions in Pneumonia Inflated COVID-19: An Invivo Mathematical Modelling Study" (2020), Section 2 (Models 1 and 2), Section 3 ($R_0$ and its threshold analysis) and Section 4 (Theorem 4.1, existence of optimal control, and the characterization of optimal control). <https://doi.org/10.48550/arXiv.2005.02261>
