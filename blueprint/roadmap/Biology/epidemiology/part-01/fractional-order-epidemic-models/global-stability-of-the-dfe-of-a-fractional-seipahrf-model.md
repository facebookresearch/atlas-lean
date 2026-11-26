# Extinction of infection below threshold in a fractional SEIPAHRF model with super-spreaders

**Model.** For $0<\alpha<1$ let ${}^{C}D^{\alpha}$ be the Caputo derivative ${}^{C}D^{\alpha}x(t)=\frac{1}{\Gamma(1-\alpha)}\int_0^t (t-s)^{-\alpha}x'(s)\,ds$. A population of constant size $N=S+E+I+P+A+H+R+F$ is split into susceptible $S$, exposed $E$, symptomatic infectious $I$, super-spreaders $P$, asymptomatic $A$, hospitalized $H$, recovered $R$ and dead $F$:

$$
\begin{aligned}
{}^{C}D^{\alpha}S&=-\tfrac{S}{N}\bigl(\beta I+l\beta H+\beta'P\bigr), & {}^{C}D^{\alpha}E&=\tfrac{S}{N}\bigl(\beta I+l\beta H+\beta'P\bigr)-\kappa E,\\
{}^{C}D^{\alpha}I&=\kappa\rho_1E-\varpi_iI, & {}^{C}D^{\alpha}P&=\kappa\rho_2E-\varpi_pP,\\
{}^{C}D^{\alpha}A&=\kappa(1-\rho_1-\rho_2)E, & {}^{C}D^{\alpha}H&=\gamma_a(I+P)-\varpi_hH,\\
{}^{C}D^{\alpha}R&=\gamma_i(I+P)+\gamma_rH, & {}^{C}D^{\alpha}F&=\delta_iI+\delta_pP+\delta_hH,
\end{aligned}
$$

with $\varpi_i=\gamma_a+\gamma_i+\delta_i$, $\varpi_p=\gamma_a+\gamma_i+\delta_p$, $\varpi_h=\gamma_r+\delta_h$, transmission rates $\beta$ (symptomatic), $l\beta$ (hospitalized) and $\beta'$ (super-spreaders), and fractions $\rho_1,\rho_2$ of exposed becoming symptomatic and super-spreaders.

**Theorem (well-posedness).** For nonnegative initial data the system has a unique solution, and it stays in $\Omega=\{(S,E,I,P,A,H,R,F)\in\mathbb R^8_{+}: S+\dots+F\le N\}$.

**Theorem (extinction of infection below threshold).** Let

$$
R_0=\frac{\beta\rho_1(\gamma_al+\varpi_h)}{\varpi_i\varpi_h}+\frac{(\beta\gamma_al+\beta'\varpi_h)\rho_2}{\varpi_p\varpi_h}
$$

(the same next-generation reproduction number as for $\alpha=1$). If $R_0<1$, then for every $\alpha\in(0,1)$ and every solution in $\Omega$ the infected compartments vanish: $E(t),I(t),P(t),H(t)\to0$ as $t\to\infty$.

The point $(N,0,\dots,0)$ is not globally attracting: $A$, $R$ and $F$ have no outflow, so every state with $E=I=P=H=0$ is an equilibrium, the disease-free equilibria form a continuum, and a solution started with $A(0)+R(0)+F(0)>0$ cannot have $S(t)\to N$.

## Expansion

Take the linear Lyapunov function $V=a_0E+a_1I+a_2P+a_3H$ with $a_0=\varpi_i\varpi_p\varpi_h$, $a_1=(\beta\varpi_h+\beta\gamma_al)\varpi_p$, $a_2=(\beta'\varpi_h+\beta\gamma_al)\varpi_i$ and $a_3=\beta l\varpi_i\varpi_p$. Since ${}^{C}D^{\alpha}$ is linear and $S\le N$,

$$
{}^{C}D^{\alpha}V\le(a_0\beta+a_3\gamma_a-a_1\varpi_i)I+(a_0\beta l-a_3\varpi_h)H+(a_0\beta'+a_3\gamma_a-a_2\varpi_p)P+\kappa(a_1\rho_1+a_2\rho_2-a_0)E .
$$

The first three coefficients vanish by the choice of $a_j$, and $a_1\rho_1+a_2\rho_2-a_0=\varpi_i\varpi_p\varpi_h(R_0-1)<0$, so ${}^{C}D^{\alpha}V\le0$ with equality only when $E=0$. The fractional LaSalle invariance principle then gives convergence to the largest invariant set in $\{E=0\}$; on it the $E$ equation forces $\frac{S}{N}(\beta I+l\beta H+\beta'P)=0$ and the $I,P,H$ equations then force $I=P=H=0$. Nothing forces $S\to N$: the source's statement that the disease-free equilibrium $(N,0,\dots,0)$ is globally asymptotically stable overlooks the absorbing compartments $A,R,F$, and only the extinction of the infected compartments is stated here. Well-posedness follows from a linear-growth bound on the vector field (existence on $[0,\infty)$ for Caputo systems) and the generalized mean value theorem $x(t)=x(0)+\frac{1}{\Gamma(\alpha)}{}^{C}D^{\alpha}x(\eta)\,t^{\alpha}$, which shows that a component with nonnegative Caputo derivative on its boundary face cannot become negative.

## Sources

- F. Ndaïrou and D. F. M. Torres, "Mathematical analysis of a fractional COVID-19 model applied to Wuhan, Spain and Portugal", arXiv:2106.15407 (2021), Section 3 (model), Section 4 (existence and uniqueness theorem) and Section 5 (Eq. for $R_0$ and the global stability theorem), <https://doi.org/10.48550/arXiv.2106.15407>.
- Published version: F. Ndaïrou and D. F. M. Torres, "Mathematical Analysis of a Fractional COVID-19 Model Applied to Wuhan, Spain and Portugal", Axioms 10 (2021), 135, <https://doi.org/10.3390/axioms10030135>.
