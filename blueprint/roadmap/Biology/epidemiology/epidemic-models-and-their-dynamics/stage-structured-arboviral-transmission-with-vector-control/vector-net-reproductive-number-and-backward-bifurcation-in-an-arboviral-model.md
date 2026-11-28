# Vector net reproductive number and backward bifurcation in a stage-structured arboviral model

**Model.** A host-vector model for arboviral diseases (dengue, chikungunya, yellow fever) couples humans, split into susceptible, vaccinated (with waning vaccine immunity), exposed, infectious and immune classes with immigration and disease-induced death rate $\delta\ge0$, to a vector population with aquatic stages egg $E$, larva $L$, pupa $P$ and adult females that are susceptible, exposed or infectious. The aquatic dynamics are

$$\dot E=\mu_b\Bigl(1-\frac{E}{\alpha_2\Gamma_E}\Bigr)N_v-(s+\mu_E+\eta_1)E,\qquad \dot L=sE\Bigl(1-\frac{L}{\alpha_2\Gamma_L}\Bigr)-(l+\mu_L+\eta_2)L,\qquad \dot P=lL-(\theta+\mu_P)P,$$

where $N_v$ is the adult female population, $\mu_b$ the egg-laying rate, $s,l,\theta$ the stage transition rates, $\Gamma_E,\Gamma_L$ the breeding-site capacities, and the controls are mechanical removal of breeding sites ($\alpha_2\le1$), egg and larva chemical mortality $\eta_1,\eta_2$, adulticide mortality $c_m$ (adults die at rate $\mu_v+c_m$) and individual protection $\alpha_1$, which multiplies both forces of infection by $1-\alpha_1$. Transmission uses standard incidence.

**Thresholds.** With $k_5=s+\mu_E+\eta_1$, $k_6=l+\mu_L+\eta_2$, $k_7=\theta+\mu_P$, $k_8=\mu_v+c_m$, the *net reproductive number* of the vector population is

$$\mathcal N=\frac{\mu_b\,\theta\, l\, s}{k_5k_6k_7k_8},$$

the expected number of adult females produced by one adult female through the egg, larva and pupa stages when breeding sites are unsaturated.

**Theorem.**

1. If $\mathcal N\le1$, the trivial (vector-free and disease-free) equilibrium is globally asymptotically stable.
2. If $\mathcal N>1$, the trivial equilibrium is unstable, and the disease-free equilibrium with a positive vector population is locally asymptotically stable whenever the basic reproduction number $R_0<1$; it is globally asymptotically stable when $R_0<R_c<1$, where $R_c^2=\bigl((\mu_h+\delta)/\mu_h\bigr)^2R_0^2$ and $\mu_h$ is the human natural death rate.
3. If $\mathcal N>1$ and $\delta=0$, there is a unique endemic equilibrium when a threshold $R_1>1$ and none otherwise; if $\delta>0$, there is at least one endemic equilibrium when $R_0>1$ and there may be zero, one or several when $R_0<1$.
4. The model undergoes a backward bifurcation at $R_0=1$ under an explicit sign condition on the centre-manifold coefficient, and a forward bifurcation under the reverse inequality.

Without disease-induced death $R_c=R_0$, and with mass-action instead of standard incidence the disease-free equilibrium is globally stable whenever its reproduction number is below one; disease-induced death combined with the nonlinear standard incidence is what produces the backward bifurcation. So pushing $R_0$ just below $1$ need not eliminate the disease, while pushing $\mathcal N$ below $1$ (breeding-site and larval control) eliminates vector and disease alike.

## Expansion

1. $\mathcal N$ is the product of the stage-survival probabilities $s/k_5$, $l/k_6$, $\theta/k_7$ and the adult lifetime fecundity $\mu_b/k_8$; the logistic breeding-site terms make the vector equilibrium positive exactly when $\mathcal N>1$.
2. $R_0$ is obtained by the next-generation method at the vector-positive disease-free equilibrium, as the geometric mean of host-to-vector and vector-to-host reproduction numbers.
3. Global stability below $R_c$ uses the Kamgang-Sallet theorem for systems of the form $\dot X_S=A_1(X)(X_S-X_{\mathrm{DFE}})+A_{12}(X)X_I$, $\dot X_I=A_2(X)X_I$ with Metzler $A_2$.
4. The backward bifurcation follows from the Castillo-Chavez-Song criterion with $\beta_{hv}$ as bifurcation parameter: the sign of the quadratic coefficient $a$ decides the direction.

## Sources

- H. Abboubakar, J. C. Kamgang, D. Tieudjo, *Backward bifurcation and control in transmission dynamics of arboviral diseases*, arXiv:1509.04919 (Section 2 model; Theorems 3.1, 3.2, 3.4, 3.5 and 3.6; Remarks 3.1 and 3.2; Theorems 3.10 and 3.11; Lemma 3.3). <https://doi.org/10.48550/arXiv.1509.04919> Published version: Mathematical Biosciences 278 (2016) 100–129, <https://doi.org/10.1016/j.mbs.2016.06.002>.
