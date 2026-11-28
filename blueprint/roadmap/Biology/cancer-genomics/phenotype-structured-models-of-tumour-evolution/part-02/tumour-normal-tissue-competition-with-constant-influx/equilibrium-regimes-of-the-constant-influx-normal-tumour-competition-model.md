# Equilibrium regimes of the constant-influx normal–tumour competition model

Let $N(t)$ and $A(t)$ be the numbers of normal and tumour cells in a tissue, with

$$\frac{dN}{dt}=r_N-\mu_NN-\beta_1NA,\qquad \frac{dA}{dt}=r_AA\Bigl(1-\frac{A}{K_A}\Bigr)-\beta_3NA-(\mu_A+\epsilon_A)A,$$

where $r_N>0$ is the constant production of normal cells, $\mu_N>0$ their mortality, $r_A,K_A>0$ the logistic growth parameters of tumour cells, $\mu_A,\epsilon_A\ge0$ their natural and apoptotic mortality, $\beta_1>0$ the damage of tumour cells to normal tissue and $\beta_3>0$ the tissue response against tumour cells. Assume $l_A=r_A-(\mu_A+\epsilon_A)>0$ and set

$$\beta_1^{th}=\frac{\mu_Nr_A}{l_AK_A},\qquad \beta_3^{th}=\frac{\mu_N}{r_N}l_A,\qquad \eta=\frac{r_Ar_N(\beta_3-\beta_3^{th})}{K_Al_A^2},\qquad \beta_{1,\Delta}^{th}=\beta_1^{th}+2\eta+2\sqrt{\eta(\beta_1^{th}+\eta)}.$$

**Equilibria.** The cancer-free equilibrium is $P_0=(r_N/\mu_N,0)$. Tumour equilibria are $P_i=(r_N/(\mu_N+\beta_1A_i),A_i)$, where $A_1<A_2$ are the real roots of $aA^2+bA+c=0$ with $a=\beta_1r_A/K_A$, $b=l_A(\beta_1^{th}-\beta_1)$, $c=r_N(\beta_3-\beta_3^{th})$. There is never an equilibrium with $N=0$: normal cells cannot go extinct.

**Theorem.**

1. If $\beta_3>\beta_3^{th}$ and $\beta_1<\beta_{1,\Delta}^{th}$, then $P_0$ is the only non-negative equilibrium and it is globally stable (cure).
2. If $\beta_3>\beta_3^{th}$ and $\beta_1>\beta_{1,\Delta}^{th}$, then $P_0$ and $P_2$ are both locally stable, $P_1$ is a saddle, and the stable separatrix (stable invariant curve) of $P_1$ separates the basins of attraction of $P_0$ and $P_2$ (bistability between cure and cancer).
3. If $\beta_3<\beta_3^{th}$, then $P_2$ is globally stable for all initial conditions with $A(0)>0$ (cancer).

Since $\beta_3^{th}=l_A/N_0$ with $N_0=r_N/\mu_N$, tumour establishment is favoured by a large tumour net growth rate and a small normal-cell carrying level. In regime 2, onset and treatment are transitions between the two basins, so the size and shape of the basins (resilience of the equilibria) govern the outcome.

## Expansion

At an interior equilibrium $N=r_N/(\mu_N+\beta_1A)$; substituting into $dA/dt=0$ and clearing denominators gives the quadratic. Since $a>0$, Descartes' rule of signs gives two positive roots when $c>0$ and $b<0$ with non-negative discriminant, and exactly one when $c<0$; $\beta_{1,\Delta}^{th}$ is the value of $\beta_1>\beta_1^{th}$ where $b^2-4ac=0$. By comparison with $dN/dt\le r_N-\mu_NN$ and $dA/dt\le l_AA(1-r_AA/(l_AK_A))$, trajectories are eventually confined to the box $[0,r_N/\mu_N]\times[0,l_AK_A/r_A]$, and the Dulac function $1/(NA)$ gives a vector field of strictly negative divergence there, ruling out periodic orbits; so by Poincaré–Bendixson every trajectory converges to an equilibrium; the local stability types then determine the global picture. The $N$-axis is the stable invariant curve of $P_0$ in regime 3, which is why $A(0)>0$ is required there.

## Proof depends on

- [Poincaré–Bendixson theorem](../../../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Sources

- A. C. Fassoni and H. M. Yang, *An ecological resilience perspective on cancer: insights from a toy model*, arXiv:1604.08921 (2016), Sections 2 and 3, Theorem 1. <https://doi.org/10.48550/arXiv.1604.08921>
