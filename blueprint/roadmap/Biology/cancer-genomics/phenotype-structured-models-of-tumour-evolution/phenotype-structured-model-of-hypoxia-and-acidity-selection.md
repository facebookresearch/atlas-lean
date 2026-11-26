# Phenotype-structured model of oxygen- and lactate-driven selection

Let $x\in[0,L]$ be the distance from a blood vessel at $x=0$ and let $y=(y_1,y_2)\in[0,1]^2$ be the phenotypic state of a tumour cell, where $y_1$ is the normalised expression level of an acidity-resistant gene and $y_2$ that of a hypoxia-resistant gene. The local phenotypic distribution $n(t,x,y)\ge 0$ evolves by

$$\partial_t n=\beta_n\,\partial_{xx} n+\theta\,\Delta_y n+R\big(S_o,S_g,S_l,\rho,y\big)\,n,\qquad (t,x,y)\in(0,T]\times(0,L)\times(0,1)^2,$$

with zero-flux conditions at $x=0$, $x=L$ and on $\partial[0,1]^2$, where $\beta_n>0$ is the cell motility and $\theta>0$ is the rate of spontaneous phenotypic changes. The cell density is

$$\rho(t,x)=\int_{[0,1]^2}n\,dy,$$

and, at points where $\rho(t,x)>0$, the mean phenotypic traits are

$$\mu_i(t,x)=\frac{1}{\rho(t,x)}\int_{[0,1]^2}y_i\,n\,dy\quad(i=1,2).$$

The fitness landscape is

$$R=p_o(S_o)+p_g(S_o,S_g)-\eta_o\big(y_2-\varphi_o(S_o)\big)^2-\eta_l\big(y_1-\varphi_l(S_l)\big)^2-\kappa\rho,$$

with Michaelis–Menten proliferation $p_o=\gamma_o\frac{S_o}{\alpha_o+S_o}w(S_o)$ via oxidative phosphorylation and $p_g=\gamma_g\frac{S_g}{\alpha_g+S_g}\big(1-w(S_o)\big)$ via glycolysis. For oxygen thresholds $0<O_m<O_M$ the weight $w$ equals $1$ for $S_o\ge O_M$, $0$ for $S_o\le O_m$ and $1-\frac{O_M-S_o}{O_M-O_m}$ in between, and the fittest hypoxia-resistance level is $\varphi_o=1-w$. For lactate thresholds $0<L_m<L_M$ the fittest acidity-resistance level $\varphi_l$ is $0$ for $S_l\le L_m$, $1$ for $S_l\ge L_M$ and $\frac{S_l-L_m}{L_M-L_m}$ in between. The selection gradients $\eta_o,\eta_l>0$ penalise distance from the fittest phenotype, and $\kappa>0$ encodes competition for space.

The abiotic concentrations of oxygen $S_o$, glucose $S_g$ and lactate $S_l$ satisfy reaction–diffusion equations

$$\partial_t S_o=\beta_o\partial_{xx}S_o-\lambda_oS_o-\zeta_o p_o\rho,\qquad \partial_t S_g=\beta_g\partial_{xx}S_g-\lambda_gS_g-\zeta_g p_g\rho,\qquad \partial_t S_l=\beta_l\partial_{xx}S_l-\lambda_lS_l+\zeta_l p_g\rho,$$

with the boundary conditions, for all $t>0$,

$$S_o(t,0)=\bar S_o,\quad S_g(t,0)=\bar S_g,\quad S_l(t,0)=\underline S_l,\qquad S_o(t,L)=\underline S_o,\quad S_g(t,L)=\underline S_g,\quad \partial_xS_l(t,L)=0,$$

where the vessel values satisfy $\bar S_o>O_M$, $\bar S_g>0$ and $0<\underline S_l<L_m$, and the values far from the vessel satisfy $0<\underline S_o<O_m$ and $0<\underline S_g<\bar S_g$. Oxygen and glucose thus enter only through the vessel, which is well oxygenated, and the far end is hypoxic; lactate is flushed out only through the vessel, where its level is below the acidity threshold, and the zero-flux condition models its accumulation far from the vessel. Lactate is produced in proportion to glycolytic proliferation, which couples acidity to hypoxia.

## Expansion

The Laplacian in $y$ is the continuum limit of small, heritable, undirected phenotypic jumps in individual-based models. Each quadratic penalty encodes a trade-off: expressing less resistance than the environment requires raises death, expressing more costs proliferation, so the fittest level tracks the local oxygen or lactate concentration through the piecewise-linear maps $\varphi_o$ and $\varphi_l$. Numerical solutions show resistant phenotypes concentrating far from the vessel, where oxygen is low and lactate accumulates.

## Sources

- G. Fiandaca, M. E. Delitala, T. Lorenzi, "A Mathematical Study of the Influence of Hypoxia and Acidity on the Evolutionary Dynamics of Cancer", Bull. Math. Biol. 83 (2021), Equations (1), (4)–(17), Assumptions 1–7, <https://doi.org/10.1007/s11538-021-00914-3>, PMCID PMC8205926.
