# Hopf threshold for the degree of partial cooperation

**Model.** Prey $u\ge0$ and predator $v\ge0$ interact through

$$\frac{du}{dt}=\frac{r_0u^N}{1+Kv}-au^2-du-puv,\qquad \frac{dv}{dt}=quv-mv,$$

with birth rate $r_0$, fear level $K$ (predator presence suppresses prey reproduction), intraspecific competition $a$, prey death rate $d$, linear predation rate $p$, conversion $q$ and predator death rate $m$, all positive. The exponent $N\in[1,2)$, the *degree of partial cooperation*, makes per capita reproduction grow with density as $u^{N-1}$ but more slowly than full cooperation ($N=2$), which would destroy boundedness; $N=1$ is the classical fear model. After rescaling (prey by $m/q$, time by the factor $1+Kv$), the system becomes

$$\dot u=a_0u^N-(a_1u^2+a_2u+a_3uv)(1+v),\qquad \dot v=v(u-1)(1+v),$$

with positive constants $a_0,a_1,a_2,a_3$ built from the original parameters.

**Equilibria.** $(0,0)$ is always locally stable for $N>1$ (a demographic Allee effect, since $a_0u^{N-1}\to0$ as $u\to0$). Axial equilibria $(u,0)$ solve $a_0u^{N-1}=a_1u+a_2$, a concave curve against a line, so there are at most two, $\alpha<\beta$. The interior equilibrium is $(1,\bar v)$, where $\bar v>0$ solves $a_0=(a_1+a_2+a_3\bar v)(1+\bar v)$.

**Theorem.** At $(1,\bar v)$ the Jacobian has positive determinant $(a_1+a_2+a_3+2a_3\bar v)\,\bar v(1+\bar v)$ and trace $Na_0-(1+\bar v)(2a_1+a_2+a_3\bar v)$. Hence the interior equilibrium is locally stable for

$$N<N_H:=1+\frac{a_1}{a_1+a_2+a_3\bar v},$$

unstable for $N>N_H$, and a Hopf bifurcation occurs exactly at $N=N_H$.

## Expansion

Substituting the equilibrium relation $a_0=(a_1+a_2+a_3\bar v)(1+\bar v)$ into the trace gives $(1+\bar v)\big[(N-1)(a_1+a_2+a_3\bar v)-a_1\big]$, which changes sign at $N_H$ with nonzero speed in $N$, while the determinant stays positive; this is the Hopf condition. Raising the degree of cooperation therefore destabilizes coexistence and produces predator-prey oscillations, while the Allee-type stability of extinction creates bistability: when $\alpha<m/q<\beta$ in original units, a heteroclinic connection between the axial saddles separates the basin of extinction from the basin of the interior attractor.

## Sources

- Suvranil Chowdhury, Susmita Sarkar, Joydev Chattopadhyay, "Modeling Cost-Associated Cooperation: A Dilemma of Species Interaction Unveiling New Aspects of Fear Effect", arXiv:2501.16522 (2025), Theorems 3.1, 4.1, 4.4, 5.2 and 5.3 (Sections 3-5), <https://doi.org/10.48550/arXiv.2501.16522>
