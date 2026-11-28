# Global threshold dynamics of the k-stage malaria intrahost model

**Model.** Let $x$ be healthy red blood cells (RBC), $y_1,\dots,y_k$ parasitized RBC in successive age classes, and $m$ free merozoites:

$$
\begin{aligned}
\dot x &= \varphi(x) - \beta xm,\\
\dot y_1 &= \beta xm - \alpha_1y_1,\qquad \dot y_j = \gamma_{j-1}y_{j-1} - \alpha_jy_j\quad (j=2,\dots,k),\\
\dot m &= r\gamma_ky_k - \mu_mm - u\beta xm,
\end{aligned}
$$

where all rates are positive (when $\alpha_j$ is $\gamma_j$ plus a stage mortality, $\gamma_j/\alpha_j$ is the probability of passing stage $j$, but the theorem needs no assumption such as $\alpha_j>\gamma_j$: by the source's Remark 1 its only hypothesis is positivity of the parameters), $r$ is the number of merozoites per bursting cell, $u\ge 0$ is the mean number of merozoites lost per invasion, and $\varphi(x)=f(x)-\mu_xx$ is $C^1$ with a unique $x^*>0$ such that $\varphi>0$ on $[0,x^*)$ and $\varphi<0$ on $(x^*,\infty)$ (homeostatic RBC production). Define

$$
\mathcal R_0 = \frac{r\beta x^*}{\mu_m+u\beta x^*}\,\frac{\gamma_1\cdots\gamma_k}{\alpha_1\cdots\alpha_k}.
$$

**Theorem.**

1. The disease-free equilibrium $(x^*,0,\dots,0)$ is globally asymptotically stable on $\mathbb R_+^{k+2}$ if and only if $\mathcal R_0\le 1$.
2. If $\mathcal R_0>1$, the disease-free equilibrium is unstable and there is a unique endemic equilibrium in the positive orthant, with

$$
\bar x = \frac{\mu_m}{\beta\Big[r\frac{\gamma_1\cdots\gamma_k}{\alpha_1\cdots\alpha_k}-u\Big]}.
$$

With $\alpha^* := -\max_{x\in[0,x^*]}\varphi'(x)$, if $u\beta\varphi(\bar x)\le\alpha^*\mu_m$ then the endemic equilibrium is globally asymptotically stable on the nonnegative orthant minus the $x$-axis.
3. The same holds when a gametocyte compartment $\dot y_{k+1}=\rho\gamma_ky_k-\alpha_{k+1}y_{k+1}$ is added, since it does not feed back.
4. *(Classical Anderson–May–Gupta model.)* For $\varphi(x)=\Lambda-\mu_xx$ and the three-dimensional model, the endemic equilibrium is globally asymptotically stable (off the $x$-axis) whenever $\mathcal R_0>1$ and $\beta\Lambda\le(\sqrt r+\sqrt{r-1})^2\mu_x\mu_m$.

The threshold $\mathcal T_0 := x^*/\bar x$ satisfies $\mathcal T_0>1$ exactly when $\mathcal R_0>1$; it is the quantity strains are ranked by in the multistrain model.

## Expansion

Writing $z=(y_1,\dots,y_k,m)$, the parasite dynamics is $\dot z=\beta x\,z_{k+1}e_1 + A_0z - u\beta x\,z_{k+1}e_{k+1}$ with a stable Metzler matrix $A_0$; $\mathcal R_0$ is the spectral radius of the next-generation operator and is the product of the merozoite yield $r\prod\gamma_j/\alpha_j$ and the fraction $\beta x^*/(\mu_m+u\beta x^*)$ of merozoites that invade before dying. For $\mathcal R_0\le1$ the linear Lyapunov function $\beta x^*\langle e_{k+1},(-A_0)^{-1}z\rangle$ plus the Volterra term $x-x^*\ln x$ has nonpositive derivative. For $\mathcal R_0>1$ a Volterra-type function $a(x-\bar x\ln x)+\sum_i b_i(z_i-\bar z_i\ln z_i)$, with weights built from $A_0$, works under the condition $u\beta\varphi(\bar x)\le\alpha^*\mu_m$, which holds automatically when $u=0$ and is satisfied by published malaria parameter values.

## Sources

- A. Iggidr, J.-C. Kamgang, G. Sallet, J.-J. Tewa, *Global analysis of new malaria intrahost models with a competitive exclusion principle*, arXiv:1101.0922 (2011). <https://doi.org/10.48550/arXiv.1101.0922> — Theorem 2.1 (global stability of the one-strain $k$-stage model), Definition 2.2 (threshold $\mathcal T_0$), Proposition 2.3 (original Anderson–May–Gupta model). Published version: SIAM Journal on Applied Mathematics 67(1) (2006), 260–278, <https://doi.org/10.1137/050643271>; locators above refer to the arXiv version.
