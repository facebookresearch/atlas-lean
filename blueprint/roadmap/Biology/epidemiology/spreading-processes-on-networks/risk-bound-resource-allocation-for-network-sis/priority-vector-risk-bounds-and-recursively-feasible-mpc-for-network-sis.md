# Priority-vector risk bounds and recursively feasible model predictive control for network SIS

**Process.** On a graph with nodes $1,\dots,n$, the mean-field SIS probabilities $x_i\in[0,1]$ evolve, after an Euler step $h$, as

$$x(k+1)=[A-B(x(k))]\,x(k),\qquad A_{ii}=1-h\delta_i,\quad A_{ij}=h\beta_{ij}\ (i\ne j),\quad B_{ij}(x)=hx_i\beta_{ij},$$

with $h\delta_j\le1$ and $h\sum_i\beta_{ij}<1$, so that $[0,1]^n$ is invariant. The risk of an outbreak $x$ is the discounted cost $R(x)=\sum_{k\ge0}\alpha^kCx(k)$ with $x(0)=x$, a row vector of node costs $C>0$ and $\alpha\in(0,1]$. Interventions lower edge rates $\beta_{ij}$ and raise node rates $\delta_i$ monotonically in time between unmodified values and limits $\underline\beta_{ij}>0$, $\bar\delta_i<\bar\Delta_i$ (with $h\bar\Delta_i\le1$), so $\bar A\ge A(k-1)\ge A(k)\ge\underline A$ entrywise. Moving from $A^1$ to $A^2$ costs $\Gamma(A^1,A^2)=\sum_{ij}W_{ij}U_{ij}$ with logarithmic effort $U_{ij}=\log(\beta^1_{ij}/\beta^2_{ij})$ on edges and $U_{ii}=\log\frac{\bar\Delta_i-\delta^1_i}{\bar\Delta_i-\delta^2_i}$ on nodes, and at most $\bar\Gamma>0$ may be spent per step.

**Risk bound.** If nonnegative row vectors $p(\ell|k)$, $0\le\ell\le L$, satisfy the Bellman inequality

$$p(\ell|k)\ge C+\alpha\,p(\ell+1|k)A(\ell|k)\quad(0\le\ell<L),\qquad p(L|k)=p(L-1|k),$$

for an admissible rate sequence, then $R(x(k))\le\bar R(x(k)):=p(0|k)x(k)$.

**Relaxed problem.** At step $k$, minimize $p(0|k)x(k)+\epsilon\sum_ip_i(0|k)$ ($\epsilon>0$ small) over priority vectors and rate sequences subject to the Bellman inequality, the monotone rate bounds and $\Gamma(\ell|k)\le\bar\Gamma$. With $y^\ell_i=\log p_i(\ell)$ and the cumulative efforts as variables it is an exponential cone program, hence convex, and its optimal solutions satisfy:

1. the Bellman equation $p^*(\ell|k)=C+\alpha p^*(\ell+1|k)A^*(\ell|k)$ for $\ell<L$;
2. if $A(k-1)\gneqq\underline A$, then $A^*(\ell|k)$ and $p^*(\ell|k)$ strictly decrease in $\ell$ until $A^*$ reaches $\underline A$;
3. if $\Gamma(A(k-1),\underline A)>\bar\Gamma$, the whole per-step budget is spent: $\Gamma(A(k-1),A^*(0|k))=\bar\Gamma$.

**Theorem (closed loop).** Apply the first optimal rates at each step and re-solve when $x(k+1)$ is observed. If $\alpha\rho(\bar A)<1$, the scheme is recursively feasible. If moreover the set

$$\mathcal A=\Big\{A:\underline A\le A\le\bar A,\ \sum_ic_i\beta_{ij}<c_j\delta_j\ \text{for all }j\Big\}$$

is nonempty, then $\bar R(x(k))>\bar R(x(k+1))$ for every $x(k)\gneqq0$ and every $k\ge K=\lceil\Gamma_M/\bar\Gamma\rceil$, where $\Gamma_M=\inf_{A\in\mathcal A}\Gamma(\bar A,A)$ (itself computable by an exponential cone program).

## Depends on

- [Spectral radius and die-out of SIS epidemics on graphs](../../epidemics-on-networks/spectral-radius-and-die-out-of-sis-epidemics.md)

## Expansion

Because $B(x)\ge0$, the nonlinear trajectory is dominated entrywise by the linear positive system $\hat x(\ell+1)=A(\ell)\hat x(\ell)$ from the same start, and for positive linear systems with nonnegative linear costs the cost-to-go is linear; any $p$ satisfying the Bellman inequality is a supersolution, so $p(0)x$ bounds the cost of the linear system and therefore the risk. The condition $\alpha\rho(\bar A)<1$ makes the stationary choice $p=C(I-\alpha\bar A)^{-1}$ finite and nonnegative, which keeps the problem feasible at every step. The set $\mathcal A$ consists of intervention levels under which the weighted node costs strictly contract, $C-(1-\alpha)p>0$ for $p=C(I-\alpha A)^{-1}$; once the accumulated spending has driven $A(k)$ into $\mathcal A$, which takes at most $K$ steps, the bound strictly decreases along the closed loop. The logarithmic effort model never allows a rate to be reduced to zero and its $\ell_1$-type budget promotes sparse allocations concentrated on few nodes and edges.

## Sources

- Ruigang Wang, Armaghan Zafar, Ian R. Manchester, "Model Predictive Control of Spreading Processes via Sparse Resource Allocation", in 2023 American Control Conference (ACC) (2023), 4320–4325, <https://doi.org/10.23919/acc55779.2023.10155802>. Published version of arXiv:2210.15798, cited next; locators there refer to the arXiv version.
- R. Wang, A. Zafar and I. R. Manchester, "Model predictive control of spreading processes via sparse resource allocation", arXiv:2210.15798 (2022), Problem Formulation section (process, risk, intervention and resource models) and Dynamic Programming Relaxation section (risk-bound proposition, properties of the relaxed problem, standing assumptions on the discount rate and the stabilizing set, the closed-loop theorem, and the exponential cone reformulation), <https://doi.org/10.48550/arXiv.2210.15798>.
