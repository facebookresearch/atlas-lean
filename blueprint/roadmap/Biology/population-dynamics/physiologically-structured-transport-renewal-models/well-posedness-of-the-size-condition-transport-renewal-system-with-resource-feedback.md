# Well-posedness of the size–condition transport–renewal system with resource feedback

**Model.** A population is distributed over $S$ zones $s\in\{1,\dots,S\}$ and structured by size $l\in\Omega_l=[l_0,l_m]$ ($0<l_0<l_m<\infty$) and physiological condition $c\in\Omega_c=[0,c_m]$. Let $x_s(t,l,c)\ge 0$ be the zone densities and $R_s(t)\ge 0$ the zone resources. With nonlocal feedback $\mathcal N_s[x]=\big(\sum_r\int\!\!\int \chi_{s,j,r}\,x_r\,dc\,dl\big)_{j=1}^m$ ($\chi_{s,j,r}\in L^\infty_+$), a prescribed environment $Y\in C([0,T];\mathbb R^{d_Y})$, harvest mortality $u_s=q_s(t)\sigma_s(l,c)\eta_s(\widehat B_s[x],Y)$ with effort $0\le q_s\le q_{s,\max}$, and inter-zone transfer rates $\theta_{rs}\in L^\infty_+$, the densities satisfy
$$\partial_t x_s+\partial_l\big(g_s x_s\big)+\partial_c\big(h_s x_s\big)=-\big(\mu_s+u_s+\theta_s^{\mathrm{out}}\big)x_s+\sum_{r\ne s}\theta_{rs}x_r ,$$
where $g_s,h_s,\mu_s$ are evaluated at $(\mathcal N_s[x],R_s,Y,l,c)$ and $\theta_s^{\mathrm{out}}=\sum_{r\ne s}\theta_{sr}$. Recruitment enters through the renewal boundary condition at the smallest size
$$g_s(\cdot,l_0,c)\,x_s(t,l_0,c)=\int_{\Omega_l}\!\int_{\Omega_c}\beta_s(\mathcal N_s[x],R_s,Y,l,c')\,\Pi_s(c\mid l,c',R_s,Y)\,x_s(t,l,c')\,dc'\,dl ,$$
with $\int_{\Omega_c}\Pi_s(c\mid\cdot)\,dc=1$, and each resource obeys
$$\dot R_s=F_s(R_s,Y)-\rho_s(R_s)\int\!\!\int\kappa_s\,x_s\,dc\,dl,\qquad 0\le\rho_s\le\rho_{s,\max},\ \rho_s(0)=0,\ F_s(0,y)\ge 0 .$$

**Hypotheses.** $g_s,h_s,\mu_s,\beta_s$ are $C^1$ with locally bounded first derivatives; $0<g_{\min}\le g_s\le g_{\max}$ (so $l=l_0$ is the only inflow boundary and residence times are at most $(l_m-l_0)/g_{\min}$); $|h_s|\le h_{\max}$ with $h_s\le 0$ at $c=0$ and $h_s\ge 0$ at $c=c_m$ (no inflow through the condition boundary); $\mu_s\ge\mu_{\min}\ge 0$; $\Pi_s$ is nonnegative, measurable and essentially bounded; $0\le\eta_s\le\eta_{\max}$. Initial data $\phi_s\in L^1_+\cap L^\infty$ and $R_s(0)\ge 0$.

**Theorem.** On the state space $X=\prod_s L^1(\Omega_l\times\Omega_c)$, for every horizon $T>0$:
1. *(Local existence.)* There is $\tau>0$ and a unique weak solution $(x,R)$ with $x\in C([0,\tau];X)\cap L^\infty$, $R\in W^{1,\infty}(0,\tau;\mathbb R^S)$, $x(t)\ge 0$ and $R(t)\ge 0$.
2. *(Global existence.)* The weak solution extends uniquely to $[0,T]$ with the same regularity.
3. *(Continuous dependence.)* If $(\phi^{(n)},R_0^{(n)},Y^{(n)},q^{(n)})\to(\phi,R_0,Y,q)$ strongly in $X\times\mathbb R^S\times C([0,T])\times L^\infty(0,T)$, then $\sup_{[0,T]}\|x^{(n)}(t)-x(t)\|_X+\sup_{[0,T]}|R^{(n)}(t)-R(t)|\to 0$.

## Expansion

Freezing the nonlocal arguments $(\mathcal N,R,Y)$ along a candidate trajectory turns the density equation into a linear transport problem with inflow at $l=l_0$, solvable along characteristics with $L^1$ and $L^\infty$ estimates. The map sending a candidate $(\bar x,\bar R)$ to the solution of the frozen problem (and of the resource ODE) is a self-map of a ball and a contraction with constant of order $\sqrt\tau$, giving local existence and uniqueness by Banach's fixed point theorem. Positivity of $R_s$ follows from the Nagumo inward-pointing condition $\dot R_s|_{R_s=0}=F_s(0,Y)\ge 0$. A priori $L^1$, resource and $L^\infty$ bounds depending only on data and elapsed time rule out blow-up, so the maximal solution reaches $T$; continuous dependence comes from a Gronwall argument on the same estimates.

## Sources

- Jiguang Yu, Louis Shuo Wang and Ye Liang, "Rigorous Analysis of a Nonlocal Transport–Renewal System for Physiologically Structured Populations", arXiv:2609.00735 (2026), Assumptions 2.2–2.6, Definition 2.8, Theorems 3.10, 3.14 and 3.15, <https://doi.org/10.48550/arXiv.2609.00735>.
