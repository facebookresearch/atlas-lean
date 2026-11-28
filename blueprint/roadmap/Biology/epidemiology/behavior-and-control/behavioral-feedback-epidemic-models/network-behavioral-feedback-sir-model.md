# Network behavioral-feedback SIR model

**Setting.** A population is divided into $n$ subpopulations with susceptible fractions $x_i$ and infected fractions $y_i$ (recovered $1-x_i-y_i$), state space $\mathcal S$. In the **network behavioral-feedback SIR (NBF-SIR) model**

$$\dot x_i=-x_i\sum_jA_{ij}(x,y)\,y_j,\qquad \dot y_i=x_i\sum_jA_{ij}(x,y)\,y_j-\gamma y_i,\qquad i=1,\dots,n,$$

with recovery rate $\gamma>0$, the interaction matrix $A:[0,1]^{2n}\to\mathbb R^{n\times n}_{\ge0}$ is a $C^1$ function of the epidemic state: $A_{ij}$ is proportional to the rate at which infected individuals of group $j$ infect susceptibles of group $i$, and its dependence on $(x,y)$ encodes endogenous behaviour such as voluntary distancing when prevalence is high. Write $[x]=\mathrm{diag}(x)$ and $\lambda_{\max}$ for the spectral abscissa.

**Proposition 1 (basic properties).** Solutions exist, are unique and stay in $\mathcal S$; each $x_i(t)$ is non-increasing; positivity of $x_i$ and of $y_i$ is preserved; the equilibria are exactly the infection-free states $\mathcal S^*=\{(x,0):x\in[0,1]^n\}$; and every solution converges to some $(x^*,0)$ with $0\le x^*\le x(0)$.

**Theorem 1 (stability of infection-free states).** An equilibrium $(x,0)\in\mathcal S^*$ is unstable if $\lambda_{\max}([x]A(x,0))>\gamma$ and stable if $\lambda_{\max}([x]A(x,0))<\gamma$. Under monotonicity conditions on $A(\cdot,0)$ (Proposition 2), the stability region is characterized more explicitly.

**Theorem 2 (unimodal epidemic curve).** For interaction matrices of the form $A_{ij}(x,y)=g_i(x_i)f_j(y_j)$, i.e.

$$\dot x_i=-x_ig_i(x_i)\sum_jf_j(y_j)y_j,\qquad \dot y_i=x_ig_i(x_i)\sum_jf_j(y_j)y_j-\gamma y_i,$$

with $g,f>0$, $x_ig_i(x_i)$ increasing and $f_j(y_j)y_j$ increasing and concave, and nonzero initial $x(0),y(0)$, the aggregate infection curve $\bar y(t)=\sum_jf_j(y_j(t))y_j(t)$ is either strictly decreasing for all $t\ge0$ (if $\dot{\bar y}(0)\le0$) or strictly increasing up to a single peak time $\hat t$ and strictly decreasing afterwards (if $\dot{\bar y}(0)>0$).

## Expansion

Infection-free states form a continuum of equilibria; linearizing in the infected directions gives $\dot y=([x]A(x,0)-\gamma I)y$, whose spectral abscissa decides whether a small reintroduced infection grows, so $\lambda_{\max}([x]A(x,0))/\gamma$ acts as an effective reproduction number at the current susceptible level. Monotone decrease of $x$ forces convergence to the equilibrium set. Unimodality uses the rank-one-like structure: the force of infection is a common scalar $\bar y$ weighted by group susceptibilities, and the increasing-and-concave assumption on $f_jy_j$ (behavioural response weakening the growth of infection pressure) ensures that once $\bar y$ starts to decline it cannot rise again. This extends the single-peak property of homogeneous SIR epidemics to heterogeneous populations with behavioural feedback.

## Sources

- M. Alutto, L. Cianfanelli, G. Como, F. Fagnani, "Network behavioral-feedback SIR epidemic model", *Automatica* 193 (2026), 113220, Proposition 1, Theorem 1, Proposition 2, Theorem 2, <https://doi.org/10.1016/j.automatica.2026.113220> (preprint arXiv:2507.03852).
