# Basic reproduction number of a multiscale model with environmental transmission

**Model.** Susceptible $S$, pre-symptomatic infected $E$, symptomatic infected $I$, recovered $R$ hosts and an environmental virus reservoir $Z$ are coupled to the within-host target cells $T$, infected cells $T^*$ and virus $V$ of an average infected host:

$$\begin{aligned}
\dot S&=\Lambda-\beta_E(V,E)SE-\beta_I(V,I)SI-\beta_Z(Z)SZ-\mu S,\\
\dot E&=\beta_E(V,E)SE+\beta_I(V,I)SI+\beta_Z(Z)SZ-(\alpha+\mu)E,\\
\dot I&=\alpha E-(\omega+\gamma+\mu)I,\qquad \dot R=\gamma I-\mu R,\qquad \dot Z=\xi_EE+\xi_II-\delta Z,\\
\epsilon\dot T&=b-\kappa VT-dT,\qquad \epsilon\dot T^*=\kappa VT-qT^*,\qquad \epsilon\dot V=\eta(Z)+pT^*-cV,
\end{aligned}$$

with $0<\epsilon\ll1$ separating the fast within-host from the slow between-host time scale. Assume the transmission rates are positive, increase with viral load ($\partial_V\beta_W>0$), do not increase with prevalence ($\partial_W\beta_W\le0$ for $W=E,I$, $\beta_Z'\le0$), $\beta_E,\beta_I$ are concave, and the environmental intake satisfies $\eta(0)=0$, $\eta'\ge0$, $\eta''\le0$, $\eta'(Z)>0$ for $Z>0$.

**Result.** The disease-free equilibrium is $(S,E,I,R,Z,T,T^*,V)=(\Lambda/\mu,0,0,0,0,b/d,0,0)$, and the next-generation matrix gives

$$\mathcal R_0=\max\{\mathcal R_0^b,\ \mathcal R_0^w\},\qquad \mathcal R_0^b=\mathcal R_0^E+\mathcal R_0^I+\mathcal R_0^Z,$$

$$\mathcal R_0^E=\frac{\beta_E(0,0)S_0}{\alpha+\mu},\quad \mathcal R_0^I=\frac{\alpha\beta_I(0,0)S_0}{(\alpha+\mu)(\omega+\gamma+\mu)},\quad \mathcal R_0^Z=\frac{\beta_Z(0)S_0\,[\alpha\xi_I+(\omega+\gamma+\mu)\xi_E]}{(\alpha+\mu)(\omega+\gamma+\mu)\delta},\quad \mathcal R_0^w=\frac{\kappa p\,b}{c\,q\,d},$$

with $S_0=\Lambda/\mu$. The three between-host terms are the contributions of pre-symptomatic, symptomatic and environmental transmission; $\mathcal R_0^w$ is the within-host reproduction number.

**Fast system.** For fixed $Z>0$ the within-host quasi-steady state is $T=b/(\kappa V+d)$, $T^*=b\kappa V/(q(\kappa V+d))$, where $V=f(Z)$ is the unique positive root of $c\kappa V^2+\big(cd-\kappa\eta(Z)-b\kappa p/q\big)V-d\eta(Z)=0$; $f$ is strictly increasing and strictly concave in $Z$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

With infected compartments $(E,I,Z,T^*,V)$, the new-infection matrix $F$ has first row $(\beta_E(0,0)S_0,\beta_I(0,0)S_0,\beta_Z(0)S_0,0,0)$ and the entry $\kappa T_0/\epsilon$ for virus infecting target cells, and the transition matrix $V$ is block lower-triangular, coupling the within-host block to $Z$ only through $\eta'(0)$. Hence $FV^{-1}$ is block triangular and its spectral radius is the larger of the between-host block, whose dominant eigenvalue is the sum of the three route-specific terms, and the within-host block $\kappa pT_0/(cq)$. Implicit differentiation of the quadratic along $V=f(Z)$ gives $f'(Z)=(\kappa V+d)\eta'(Z)/(2c\kappa V+a_1(Z))>0$ and, using $T^*<b/q$ and $\eta''\le0$, $f''<0$.

## Sources

- X. Wang, S. Wang, J. Wang, L. Rong, "A Multiscale Model of COVID-19 Dynamics", Bulletin of Mathematical Biology (2022), model Eq. (1) with assumptions (H1)–(H4), Eqs. (2)–(4); slow-system analysis Eqs. (5)–(12), <https://doi.org/10.1007/s11538-022-01058-8>, PMCID PMC9360740.
