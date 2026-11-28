# Coexistence equilibrium of the ratio-dependent predator-prey model

**Model.** Let $P(t),Q(t)>0$ be prey and predator densities obeying the ratio-dependent (Michaelis-Menten in the ratio $P/Q$) kinetics

$$\dot P=P(a-bP)-\frac{cPQ}{mQ+P},\qquad \dot Q=-dQ+\frac{fPQ}{mQ+P},$$

with prey growth rate $a>0$, crowding coefficient $b>0$, capture rate $c>0$, half-saturation constant $m>0$, conversion rate $f>0$ and predator death rate $d>0$.

**Statement.** Besides the predator-free state $(a/b,0)$ (the source prints "one is predator free point (1, 0)", which is an equilibrium only when $a=b$; setting $Q=0$ and $\dot P=0$ in the displayed system gives $P=a/b$), the system has an interior equilibrium if and only if

$$f>d\qquad\text{and}\qquad amf-cf+cd>0,$$

and it is then unique:

$$P^*=\frac{(am-c)f+cd}{bmf},\qquad Q^*=\frac{(f-d)\,(amf-cf+cd)}{b\,d\,m^2 f}.$$

## Expansion

At an interior equilibrium the predator equation gives $fP=d(mQ+P)$, so $Q=(f-d)P/(dm)$, which is positive only if $f>d$; then $mQ+P=fP/d$. Substituting into the prey equation, $a-bP-cQ/(mQ+P)=a-bP-c(f-d)/(mf)=0$, which is linear in $P$ and gives $P^*$; positivity of $P^*$ is the second condition, and $Q^*=(f-d)P^*/(dm)$. The same pair of homogeneous states is the equilibrium set of the spatially extended model with homogeneous Neumann boundary conditions, around which the source studies noise-perturbed reaction-diffusion dynamics; the source reports the stability criterion of the coexistence point in terms of the sign of $(c-mf)d^2-(c-ma-md)f^2$ from earlier work.

## Sources

- Yasin MW, Ahmed N, Iqbal MS, Raza A, Rafiq M, Eldin EMT, Khan I. Spatio-temporal numerical modeling of stochastic predator-prey model. *Scientific Reports* 13 (2023). <https://doi.org/10.1038/s41598-023-28324-6> (PMCID: PMC10439196). Results and discussion section, equilibria of Eqs. (2)-(3).
