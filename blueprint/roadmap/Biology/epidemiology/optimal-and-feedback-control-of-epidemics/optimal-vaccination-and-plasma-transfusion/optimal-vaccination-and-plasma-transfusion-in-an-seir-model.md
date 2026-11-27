# Optimal vaccination and convalescent-plasma transfusion in an SEIR model

**Control system.** Fractions $s,e,i,r$ follow an SEIR model with transmission rate $\beta$, incubation rate $\gamma$ and recovery rate $\mu$, controlled by a vaccination rate $u(t)\in[0,u_{\max}]$ (moving susceptibles directly to $r$) and a plasma-transfusion rate $p(t)\in[0,p_{\max}]$ (a recovered donor's plasma cures an infective, an interaction term $p\,r\,i$):

$$\dot s=-\beta si-us,\qquad \dot e=\beta si-\gamma e,\qquad \dot i=\gamma e-\mu i-p\,r\,i,\qquad \dot r=\mu i+p\,r\,i+us .$$

The single-control systems are the cases $p\equiv0$ and $u\equiv0$; admissible controls are bounded measurable functions on $[0,T]$.

**Theorem (vaccination-only problem).** For the problem of minimizing $\int_0^T\bigl(i(t)+u(t)^2\bigr)dt$ over $0\le u\le u_{\max}$ with fixed horizon $T$ and nonnegative initial data, there is a unique optimal solution, and the optimal control is

$$u^*(t)=\min\Bigl\{\max\Bigl\{0,\ \frac{(\lambda_4(t)-\lambda_1(t))\,s(t)}{2}\Bigr\},\ u_{\max}\Bigr\},$$

where the adjoints solve $\dot\lambda_1=-\lambda_1(-\beta i-u)-\lambda_2\beta i-\lambda_4u$, $\dot\lambda_2=\gamma(\lambda_2-\lambda_3)$, $\dot\lambda_3=1+\beta s(\lambda_1-\lambda_2)+\mu(\lambda_3-\lambda_4)$, $\dot\lambda_4=0$, with $\lambda_i(T)=0$ (so $\lambda_4\equiv0$ and $u^*=\min\{\max\{0,-\lambda_1s/2\},u_{\max}\}$). The same Pontryagin argument gives the analogous projection formulas for the plasma-only and combined problems, the plasma control being driven by the switching function $(\lambda_3-\lambda_4)\,r\,i$ and its own quadratic cost weight.

Variants of the objective reward recovered individuals as well ($\int_0^T(r-i-u^2)\,dt$ maximized). Numerically the optimal plasma-transfusion rate peaks later than the optimal vaccination rate, since transfusion needs a pool of recovered donors.

## Expansion

Existence follows from Filippov–Cesari: the state equations are Lipschitz in the state, affine in the controls, and the running cost is convex in $u$ over a compact convex control set. The Hamiltonian $H=-i-u^2+\lambda\cdot f(x,u)$ is strictly concave in $u$, so its maximizer over $[0,u_{\max}]$ is the projection of the stationary point $u=(\lambda_4-\lambda_1)s/2$; uniqueness follows from boundedness of the states and adjoints and the Lipschitz property of the system. The adjoint equations are $\dot\lambda=-\partial H/\partial x$ with transversality $\lambda(T)=0$, since there is no terminal cost.

## Sources

- Juliana Couras, Iván Area, Juan J. Nieto, Cristiana J. Silva, Delfim F. M. Torres, "Optimal Control of Vaccination and Plasma Transfusion with Potential Usefulness for Covid-19", in Infosys Science Foundation Series (2021), 509–525, <https://doi.org/10.1007/978-981-16-2450-6_23>. Published version of arXiv:2010.04146, cited next; locators there refer to the arXiv version.
- J. Couras, I. Area, J. J. Nieto, C. J. Silva, "Optimal control of vaccination and plasma transfusion with potential usefulness for COVID-19", arXiv:2010.04146 (2020), Section 2 (controlled SEIR systems), Section 3 (optimal control problems and the Pontryagin-principle theorem for the vaccination problem) and the numerical results. <https://doi.org/10.48550/arXiv.2010.04146>
